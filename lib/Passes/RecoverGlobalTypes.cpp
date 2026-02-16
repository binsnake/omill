#include "omill/Passes/RecoverGlobalTypes.h"

#include <llvm/ADT/SmallString.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/Format.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

namespace {

/// Minimum string length to avoid false positives.
static constexpr unsigned kMinStringLen = 4;

/// Maximum string length to read.
static constexpr unsigned kMaxStringLen = 4096;

/// Check if a byte is a printable ASCII character or common whitespace.
bool isPrintableOrWhitespace(uint8_t c) {
  return (c >= 0x20 && c <= 0x7E) || c == '\n' || c == '\r' || c == '\t';
}

/// Try to read a null-terminated ASCII string from memory.
/// Returns empty string on failure.
std::string tryReadAsciiString(const BinaryMemoryMap &map, uint64_t addr) {
  std::string result;
  result.reserve(64);

  for (unsigned i = 0; i < kMaxStringLen; ++i) {
    uint8_t byte;
    if (!map.read(addr + i, &byte, 1)) return {};

    if (byte == 0) {
      // Null terminator.
      if (result.size() >= kMinStringLen) return result;
      return {};
    }

    if (!isPrintableOrWhitespace(byte)) return {};
    result.push_back(static_cast<char>(byte));
  }

  return {};  // Too long, likely not a real string.
}

/// Try to read a null-terminated UTF-16LE string from memory.
/// Only accepts strings where all code units are in BMP and printable ASCII
/// range (conservative). Returns empty string on failure.
std::string tryReadUtf16LEString(const BinaryMemoryMap &map, uint64_t addr) {
  std::string result;
  result.reserve(64);

  for (unsigned i = 0; i < kMaxStringLen; ++i) {
    uint8_t lo, hi;
    if (!map.read(addr + i * 2, &lo, 1)) return {};
    if (!map.read(addr + i * 2 + 1, &hi, 1)) return {};

    uint16_t ch = lo | (static_cast<uint16_t>(hi) << 8);

    if (ch == 0) {
      if (result.size() >= kMinStringLen) return result;
      return {};
    }

    // Conservative: only accept ASCII-range characters in UTF-16.
    if (ch > 0x7E) return {};
    if (!isPrintableOrWhitespace(static_cast<uint8_t>(ch))) return {};

    result.push_back(static_cast<char>(ch));
  }

  return {};
}

/// Get or create a global string constant for the given address.
llvm::GlobalVariable *getOrCreateStringGlobal(
    llvm::Module &M, uint64_t addr, llvm::StringRef str, bool is_utf16) {
  // Create a unique name.
  llvm::SmallString<32> name;
  llvm::raw_svector_ostream os(name);
  os << (is_utf16 ? ".wstr." : ".str.") << "0x"
     << llvm::format_hex_no_prefix(addr, 1);

  // Check if already exists.
  if (auto *existing = M.getGlobalVariable(name)) {
    return existing;
  }

  llvm::Constant *init;
  if (is_utf16) {
    // Create [N x i16] with null terminator.
    llvm::SmallVector<uint16_t, 64> data;
    for (char c : str) data.push_back(static_cast<uint16_t>(c));
    data.push_back(0);

    auto *i16_ty = llvm::Type::getInt16Ty(M.getContext());
    llvm::SmallVector<llvm::Constant *, 64> elts;
    for (uint16_t ch : data) {
      elts.push_back(llvm::ConstantInt::get(i16_ty, ch));
    }
    auto *arr_ty = llvm::ArrayType::get(i16_ty, data.size());
    init = llvm::ConstantArray::get(arr_ty, elts);
  } else {
    // Create a ConstantDataArray for ASCII string (with null terminator).
    init = llvm::ConstantDataArray::getString(M.getContext(), str,
                                               /*AddNull=*/true);
  }

  auto *GV = new llvm::GlobalVariable(
      M, init->getType(), /*isConstant=*/true,
      llvm::GlobalValue::PrivateLinkage, init, name);
  GV->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
  return GV;
}

}  // namespace

llvm::PreservedAnalyses RecoverGlobalTypesPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  auto &M = *F.getParent();
  bool changed = false;

  // Collect inttoptr instructions and ConstantExpr inttoptr users.
  // IntToPtrInst: explicit instruction form.
  // ConstantExpr: when IRBuilder folds inttoptr(constant) at construction.
  llvm::SmallVector<std::pair<llvm::Instruction *, uint64_t>, 16> inst_candidates;
  llvm::DenseMap<llvm::ConstantExpr *, uint64_t> ce_candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      // Check IntToPtrInst.
      if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&I)) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(ITP->getOperand(0))) {
          inst_candidates.push_back({ITP, CI->getZExtValue()});
        }
        continue;
      }

      // Check operands for ConstantExpr inttoptr.
      for (unsigned i = 0, e = I.getNumOperands(); i < e; ++i) {
        auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(I.getOperand(i));
        if (!CE) continue;
        if (CE->getOpcode() != llvm::Instruction::IntToPtr) continue;
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CE->getOperand(0))) {
          ce_candidates[CE] = CI->getZExtValue();
        }
      }
    }
  }

  // Replace IntToPtrInst.
  for (auto &[ITP, addr] : inst_candidates) {
    std::string str = tryReadAsciiString(*map, addr);
    bool is_utf16 = false;
    if (str.empty()) {
      str = tryReadUtf16LEString(*map, addr);
      is_utf16 = true;
    }
    if (str.empty()) continue;

    auto *GV = getOrCreateStringGlobal(M, addr, str, is_utf16);
    ITP->replaceAllUsesWith(GV);
    ITP->eraseFromParent();
    changed = true;
  }

  // Replace ConstantExpr inttoptr.
  for (auto &[CE, addr] : ce_candidates) {
    std::string str = tryReadAsciiString(*map, addr);
    bool is_utf16 = false;
    if (str.empty()) {
      str = tryReadUtf16LEString(*map, addr);
      is_utf16 = true;
    }
    if (str.empty()) continue;

    auto *GV = getOrCreateStringGlobal(M, addr, str, is_utf16);
    CE->replaceAllUsesWith(GV);
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

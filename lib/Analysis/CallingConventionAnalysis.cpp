#include "omill/Analysis/CallingConventionAnalysis.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

llvm::AnalysisKey CallingConventionAnalysis::Key;

namespace {

/// Win64 ABI: integer/pointer parameter registers, in order.
static constexpr const char *kWin64ParamRegs[] = {
    "RCX", "RDX", "R8", "R9",
};
static constexpr unsigned kWin64ParamCount = 4;

/// Win64 callee-saved (nonvolatile) registers.
static constexpr const char *kWin64CalleeSaved[] = {
    "RBX", "RBP", "RDI", "RSI", "R12", "R13", "R14", "R15",
};
static constexpr unsigned kWin64CalleeSavedCount =
    sizeof(kWin64CalleeSaved) / sizeof(kWin64CalleeSaved[0]);

/// Win64 shadow space size: 32 bytes (4 x 8) reserved by caller.
static constexpr unsigned kWin64ShadowSpaceSize = 32;

/// Resolve a pointer to its State byte offset. Returns -1 if not resolvable.
int64_t resolveStateOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }
  return -1;
}

/// Compute live-in and live-out State field offsets for a function.
void computeLiveness(llvm::Function &F, const llvm::DataLayout &DL,
                     llvm::DenseSet<unsigned> &live_in,
                     llvm::DenseSet<unsigned> &live_out) {
  llvm::DenseSet<unsigned> ever_written;
  llvm::DenseSet<unsigned> written_in_entry;

  // Entry block: precise tracking of read-before-write
  if (!F.empty()) {
    for (auto &I : F.getEntryBlock()) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u = static_cast<unsigned>(off);
          if (!written_in_entry.count(u)) {
            live_in.insert(u);
          }
        }
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u = static_cast<unsigned>(off);
          written_in_entry.insert(u);
          ever_written.insert(u);
        }
      }
    }
  }

  // Remaining blocks: conservatively add reads not covered by entry writes
  for (auto &BB : F) {
    if (&BB == &F.getEntryBlock()) continue;
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u = static_cast<unsigned>(off);
          if (!written_in_entry.count(u)) {
            live_in.insert(u);
          }
        }
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          ever_written.insert(static_cast<unsigned>(off));
        }
      }
    }
  }

  live_out = ever_written;
}

/// Count how many consecutive Win64 parameter registers are live-in.
unsigned scoreWin64Params(const llvm::DenseSet<unsigned> &live_in,
                          const StateFieldMap &field_map) {
  unsigned matched = 0;
  for (unsigned i = 0; i < kWin64ParamCount; ++i) {
    auto field = field_map.fieldByName(kWin64ParamRegs[i]);
    if (!field) break;
    if (live_in.count(field->offset)) {
      matched++;
    } else {
      break;
    }
  }
  return matched;
}

FunctionABI analyzeFunction(llvm::Function &F, const llvm::DataLayout &DL,
                            const StateFieldMap &field_map) {
  FunctionABI abi;

  if (F.isDeclaration() || F.empty()) return abi;
  if (F.arg_size() == 0) return abi;

  llvm::DenseSet<unsigned> live_in, live_out;
  computeLiveness(F, DL, live_in, live_out);

  // Win64 detection: check parameter registers RCX, RDX, R8, R9.
  unsigned win64_score = scoreWin64Params(live_in, field_map);

  if (win64_score > 0) {
    abi.cc = DetectedCC::kWin64;

    // Build parameter list
    for (unsigned i = 0; i < win64_score; ++i) {
      auto field = field_map.fieldByName(kWin64ParamRegs[i]);
      if (!field) break;

      RecoveredParam param;
      param.reg_name = kWin64ParamRegs[i];
      param.state_offset = field->offset;
      param.size = field->size;
      param.index = i;
      abi.params.push_back(param);
    }
  } else {
    // No parameter registers detected.
    auto rax_field = field_map.fieldByName("RAX");
    if (rax_field && live_out.count(rax_field->offset)) {
      // Returns a value but takes no parameters.
      abi.cc = DetectedCC::kWin64;
    } else {
      abi.cc = DetectedCC::kVoid;
      return abi;
    }
  }

  // Return value: RAX for integer, XMM0 for float (check RAX first).
  auto rax_field = field_map.fieldByName("RAX");
  if (rax_field && live_out.count(rax_field->offset)) {
    RecoveredReturn ret;
    ret.reg_name = "RAX";
    ret.state_offset = rax_field->offset;
    ret.size = rax_field->size;
    abi.ret = ret;
  }

  // Identify clobbered callee-saved registers.
  // In Win64, RBX, RBP, RDI, RSI, R12-R15 are nonvolatile.
  for (unsigned i = 0; i < kWin64CalleeSavedCount; ++i) {
    auto field = field_map.fieldByName(kWin64CalleeSaved[i]);
    if (field && live_out.count(field->offset)) {
      abi.clobbered_callee_saved.push_back(kWin64CalleeSaved[i]);
    }
  }

  // Win64: shadow space (home area) of 32 bytes is allocated by the caller
  // at [RSP+8..RSP+40]. Store this info for stack frame recovery.
  abi.shadow_space_size = kWin64ShadowSpaceSize;

  return abi;
}

}  // namespace

CallingConventionInfo CallingConventionAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  CallingConventionInfo result;
  auto &DL = M.getDataLayout();
  StateFieldMap field_map(M);

  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;

    result.function_abis[&F] = analyzeFunction(F, DL, field_map);
  }

  return result;
}

}  // namespace omill

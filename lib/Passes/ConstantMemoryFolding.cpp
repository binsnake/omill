#include "omill/Passes/ConstantMemoryFolding.h"

#include <cstdint>
#include <cstring>
#include <optional>

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

namespace {

/// Try to resolve a pointer operand to a constant integer address.
/// Handles:
///   - inttoptr(i64 <const>)  (ConstantExpr or IntToPtrInst)
///   - gep(inttoptr(i64 <const>), <const offsets>)
std::optional<uint64_t> resolveConstantAddress(llvm::Value *ptr,
                                                const llvm::DataLayout &DL) {
  // Strip pointer casts (bitcast, addrspacecast).
  ptr = ptr->stripPointerCasts();

  // Case 1: ConstantExpr inttoptr.
  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CE->getOperand(0)))
        return CI->getZExtValue();
    }
    // GEP constant expression with inttoptr base.
    if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
      auto *GEP = llvm::cast<llvm::GEPOperator>(CE);
      auto base_addr = resolveConstantAddress(GEP->getPointerOperand(), DL);
      if (!base_addr)
        return std::nullopt;
      llvm::APInt offset(DL.getPointerSizeInBits(), 0);
      if (!GEP->accumulateConstantOffset(DL, offset))
        return std::nullopt;
      return *base_addr + offset.getZExtValue();
    }
  }

  // Case 2: IntToPtrInst with constant operand.
  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(ITP->getOperand(0)))
      return CI->getZExtValue();
  }

  // Case 3: GEP instruction with resolvable base.
  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    auto base_addr = resolveConstantAddress(GEP->getPointerOperand(), DL);
    if (!base_addr)
      return std::nullopt;
    llvm::APInt offset(DL.getPointerSizeInBits(), 0);
    if (!GEP->accumulateConstantOffset(DL, offset))
      return std::nullopt;
    return *base_addr + offset.getZExtValue();
  }

  return std::nullopt;
}

struct SymbolicAddress {
  llvm::Value *base = nullptr;
  int64_t offset = 0;
};

/// Resolve integer expression into (base + const_offset).
/// Examples:
///   add i64 %rsp, -56   -> {base=%rsp, offset=-56}
///   sub i64 %x, 8       -> {base=%x, offset=-8}
///   i64 %x              -> {base=%x, offset=0}
std::optional<SymbolicAddress> resolveBasePlusConst(llvm::Value *V) {
  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    if (BO->getOpcode() == llvm::Instruction::Add ||
        BO->getOpcode() == llvm::Instruction::Sub) {
      auto add_const = [&](llvm::Value *lhs, llvm::ConstantInt *rhs,
                           bool negate_rhs) -> std::optional<SymbolicAddress> {
        auto lhs_addr = resolveBasePlusConst(lhs);
        if (!lhs_addr)
          return std::nullopt;
        int64_t c = rhs->getSExtValue();
        lhs_addr->offset += negate_rhs ? -c : c;
        return lhs_addr;
      };

      if (auto *CRHS = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
        return add_const(BO->getOperand(0), CRHS,
                         BO->getOpcode() == llvm::Instruction::Sub);
      }
      if (BO->getOpcode() == llvm::Instruction::Add) {
        if (auto *CLHS =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
          return add_const(BO->getOperand(1), CLHS, false);
        }
      }
    }
  }

  // Base value with zero offset.
  return SymbolicAddress{V, 0};
}

/// Resolve pointer into (base + const_offset) when possible.
/// Handles:
///   inttoptr(base + const)
///   gep(inttoptr(base + const), const)
std::optional<SymbolicAddress> resolveSymbolicAddress(llvm::Value *ptr,
                                                      const llvm::DataLayout &DL) {
  ptr = ptr->stripPointerCasts();

  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr) {
      return resolveBasePlusConst(CE->getOperand(0));
    }
    if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
      auto *GEP = llvm::cast<llvm::GEPOperator>(CE);
      auto base = resolveSymbolicAddress(GEP->getPointerOperand(), DL);
      if (!base)
        return std::nullopt;
      llvm::APInt gep_off(DL.getPointerSizeInBits(), 0);
      if (!GEP->accumulateConstantOffset(DL, gep_off))
        return std::nullopt;
      base->offset += gep_off.getSExtValue();
      return base;
    }
    return std::nullopt;
  }

  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    return resolveBasePlusConst(ITP->getOperand(0));
  }

  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    auto base = resolveSymbolicAddress(GEP->getPointerOperand(), DL);
    if (!base)
      return std::nullopt;
    llvm::APInt gep_off(DL.getPointerSizeInBits(), 0);
    if (!GEP->accumulateConstantOffset(DL, gep_off))
      return std::nullopt;
    base->offset += gep_off.getSExtValue();
    return base;
  }

  return std::nullopt;
}

struct ByteKey {
  const llvm::Value *base = nullptr;
  int64_t offset = 0;
  bool operator==(const ByteKey &o) const {
    return base == o.base && offset == o.offset;
  }
};

struct ByteKeyInfo {
  static inline ByteKey getEmptyKey() {
    return ByteKey{llvm::DenseMapInfo<const llvm::Value *>::getEmptyKey(), 0};
  }
  static inline ByteKey getTombstoneKey() {
    return ByteKey{llvm::DenseMapInfo<const llvm::Value *>::getTombstoneKey(), 0};
  }
  static unsigned getHashValue(const ByteKey &k) {
    return llvm::hash_combine(k.base, k.offset);
  }
  static bool isEqual(const ByteKey &a, const ByteKey &b) { return a == b; }
};

std::optional<unsigned> loadOrStoreByteWidth(llvm::Type *ty) {
  if (ty->isIntegerTy()) {
    unsigned bits = ty->getIntegerBitWidth();
    unsigned bytes = (bits + 7) / 8;
    if (bytes > 8)
      return std::nullopt;
    return bytes;
  }
  if (ty->isFloatTy())
    return 4;
  if (ty->isDoubleTy())
    return 8;
  return std::nullopt;
}

std::optional<uint64_t> constantScalarBits(llvm::Value *v, llvm::Type *ty) {
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(v)) {
    return CI->getZExtValue();
  }
  if (auto *CF = llvm::dyn_cast<llvm::ConstantFP>(v)) {
    if (ty->isFloatTy()) {
      auto bits = CF->getValueAPF().bitcastToAPInt().getZExtValue();
      return static_cast<uint32_t>(bits);
    }
    if (ty->isDoubleTy()) {
      return CF->getValueAPF().bitcastToAPInt().getZExtValue();
    }
  }
  return std::nullopt;
}

llvm::Constant *constantFromBits(llvm::Type *ty, uint64_t bits) {
  if (ty->isIntegerTy())
    return llvm::ConstantInt::get(ty, bits);
  if (ty->isFloatTy()) {
    uint32_t b = static_cast<uint32_t>(bits);
    float f;
    std::memcpy(&f, &b, 4);
    return llvm::ConstantFP::get(ty, static_cast<double>(f));
  }
  if (ty->isDoubleTy()) {
    double d;
    std::memcpy(&d, &bits, 8);
    return llvm::ConstantFP::get(ty, d);
  }
  return nullptr;
}

}  // namespace

llvm::PreservedAnalyses ConstantMemoryFoldingPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  const auto &DL = F.getDataLayout();
  bool changed = false;

  llvm::SmallVector<llvm::LoadInst *, 16> loads;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
        loads.push_back(LI);

  // Get or create the !omill.relocated metadata kind.
  auto &Ctx = F.getContext();
  unsigned reloc_md_kind = Ctx.getMDKindID("omill.relocated");
  bool suspicious_base = map->isSuspiciousImageBase();

  for (auto *LI : loads) {
    auto addr = resolveConstantAddress(LI->getPointerOperand(), DL);
    if (!addr)
      continue;

    llvm::Type *ty = LI->getType();
    unsigned bytes = 0;

    if (ty->isIntegerTy()) {
      unsigned bits = ty->getIntegerBitWidth();
      bytes = (bits + 7) / 8;
      if (bytes > 8)
        continue;
    } else if (ty->isFloatTy()) {
      bytes = 4;
    } else if (ty->isDoubleTy()) {
      bytes = 8;
    } else {
      continue;
    }

    auto val = map->readInt(*addr, bytes);
    if (!val)
      continue;

    // Check relocation overlap and classify.
    auto kind = map->classifyRelocatedValue(*addr, bytes, *val);

    if (kind == RelocValueKind::Suspicious) {
      // The value at a relocated address doesn't look like a valid VA.
      // This could be a protector encoding constants via relocations.
      // At preferred base (delta=0), the on-disk value is still correct.
      // If the image base is suspicious, refuse to fold — the delta is
      // likely non-zero and the on-disk value would be wrong.
      if (suspicious_base)
        continue;
    }

    // Fold the value.
    llvm::Value *replacement = nullptr;

    if (ty->isIntegerTy()) {
      replacement = llvm::ConstantInt::get(ty, *val);
    } else if (ty->isFloatTy()) {
      uint32_t bits = static_cast<uint32_t>(*val);
      float fval;
      std::memcpy(&fval, &bits, 4);
      replacement = llvm::ConstantFP::get(ty, static_cast<double>(fval));
    } else if (ty->isDoubleTy()) {
      double dval;
      std::memcpy(&dval, &*val, 8);
      replacement = llvm::ConstantFP::get(ty, dval);
    }

    if (!replacement)
      continue;

    // If the value is relocated, tag the original load's users with metadata
    // before replacing. For integer types, we can directly tag the replacement
    // instruction if there is one. For constants, we use metadata on the
    // load's debug location as a breadcrumb.
    if (kind != RelocValueKind::NotRelocated) {
      // Create metadata: !omill.relocated !{kind_string, original_addr}
      auto *kind_str = llvm::MDString::get(
          Ctx, kind == RelocValueKind::NormalAddress ? "address" : "suspicious");
      auto *addr_val = llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), *addr));
      auto *md = llvm::MDNode::get(Ctx, {kind_str, addr_val});

      // Attach to users that are instructions (they survive replacement).
      for (auto *U : LI->users()) {
        if (auto *UI = llvm::dyn_cast<llvm::Instruction>(U))
          UI->setMetadata(reloc_md_kind, md);
      }
    }

    LI->replaceAllUsesWith(replacement);
    LI->eraseFromParent();
    changed = true;
  }

  // Local fold: track constant bytes for stack-like symbolic addresses
  // (inttoptr(base + const)) and fold subsequent scalar loads.
  llvm::SmallVector<llvm::LoadInst *, 16> local_folded_loads;
  for (auto &BB : F) {
    llvm::DenseMap<ByteKey, uint8_t, ByteKeyInfo> local_const_bytes;
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        // Basic-block local mode: do not propagate constants across calls.
        if (!CB->onlyReadsMemory()) {
          local_const_bytes.clear();
        }
        continue;
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto addr = resolveSymbolicAddress(SI->getPointerOperand(), DL);
        if (!addr) {
          // Unknown memory write: invalidate tracked bytes.
          local_const_bytes.clear();
          continue;
        }

        auto width = loadOrStoreByteWidth(SI->getValueOperand()->getType());
        if (!width)
          continue;

        auto bits = constantScalarBits(SI->getValueOperand(),
                                       SI->getValueOperand()->getType());
        for (unsigned i = 0; i < *width; ++i) {
          ByteKey key{addr->base, addr->offset + static_cast<int64_t>(i)};
          if (bits) {
            local_const_bytes[key] = static_cast<uint8_t>((*bits >> (8 * i)) & 0xff);
          } else {
            local_const_bytes.erase(key);
          }
        }
        continue;
      }

      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI)
        continue;

      auto addr = resolveSymbolicAddress(LI->getPointerOperand(), DL);
      if (!addr)
        continue;

      auto width = loadOrStoreByteWidth(LI->getType());
      if (!width)
        continue;

      uint64_t bits = 0;
      bool all_present = true;
      for (unsigned i = 0; i < *width; ++i) {
        ByteKey key{addr->base, addr->offset + static_cast<int64_t>(i)};
        auto it = local_const_bytes.find(key);
        if (it == local_const_bytes.end()) {
          all_present = false;
          break;
        }
        bits |= static_cast<uint64_t>(it->second) << (8 * i);
      }
      if (!all_present)
        continue;

      if (auto *C = constantFromBits(LI->getType(), bits)) {
        LI->replaceAllUsesWith(C);
        local_folded_loads.push_back(LI);
        changed = true;
      }
    }
  }
  for (auto *LI : local_folded_loads) {
    LI->eraseFromParent();
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

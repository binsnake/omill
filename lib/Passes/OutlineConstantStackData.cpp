#include "omill/Passes/OutlineConstantStackData.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>

#include <optional>

namespace omill {

namespace {

struct ConstantStoreInfo {
  llvm::StoreInst *inst;
  int64_t offset;
};

bool analyzeIntUses(llvm::Value *ival, llvm::AllocaInst *AI,
                    const llvm::DataLayout &DL, int64_t base_offset,
                    bool offset_known,
                    llvm::SmallVectorImpl<ConstantStoreInfo> &stores,
                    llvm::SmallVectorImpl<llvm::Instruction *> &dead,
                    bool &has_non_entry_store, bool &saw_load);

std::optional<int64_t> getConstantOffsetFromInt(llvm::Value *ival,
                                                llvm::AllocaInst *AI,
                                                const llvm::DataLayout &DL);

std::optional<int64_t> getConstantOffsetFromPtr(llvm::Value *ptr,
                                                llvm::AllocaInst *AI,
                                                const llvm::DataLayout &DL) {
  if (ptr == AI) {
    return 0;
  }

  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    llvm::APInt gep_off(64, 0);
    if (!GEP->accumulateConstantOffset(DL, gep_off)) {
      return std::nullopt;
    }
    auto base = getConstantOffsetFromPtr(GEP->getPointerOperand(), AI, DL);
    if (!base.has_value()) {
      return std::nullopt;
    }
    return *base + gep_off.getSExtValue();
  }

  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    return getConstantOffsetFromInt(ITP->getOperand(0), AI, DL);
  }

  if (auto *BC = llvm::dyn_cast<llvm::BitCastInst>(ptr)) {
    return getConstantOffsetFromPtr(BC->getOperand(0), AI, DL);
  }

  return std::nullopt;
}

std::optional<int64_t> getConstantOffsetFromInt(llvm::Value *ival,
                                                llvm::AllocaInst *AI,
                                                const llvm::DataLayout &DL) {
  if (auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(ival)) {
    return getConstantOffsetFromPtr(PTI->getPointerOperand(), AI, DL);
  }

  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(ival)) {
    auto opcode = BO->getOpcode();
    if (opcode != llvm::Instruction::Add && opcode != llvm::Instruction::Sub) {
      return std::nullopt;
    }

    if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
      auto base = getConstantOffsetFromInt(BO->getOperand(0), AI, DL);
      if (!base.has_value()) {
        return std::nullopt;
      }
      int64_t delta = C->getSExtValue();
      return opcode == llvm::Instruction::Sub ? (*base - delta)
                                              : (*base + delta);
    }
    if (opcode == llvm::Instruction::Add) {
      if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
        auto base = getConstantOffsetFromInt(BO->getOperand(1), AI, DL);
        if (!base.has_value()) {
          return std::nullopt;
        }
        return *base + C->getSExtValue();
      }
    }
    return std::nullopt;
  }

  if (auto *Cast = llvm::dyn_cast<llvm::CastInst>(ival)) {
    switch (Cast->getOpcode()) {
      case llvm::Instruction::SExt:
      case llvm::Instruction::ZExt:
      case llvm::Instruction::Trunc:
        return getConstantOffsetFromInt(Cast->getOperand(0), AI, DL);
      default:
        return std::nullopt;
    }
  }

  return std::nullopt;
}

std::optional<llvm::APInt> tryEvaluateIntValue(llvm::Value *V,
                                               llvm::AllocaInst *AI,
                                               const llvm::DataLayout &DL,
                                               const std::vector<uint8_t> &bytes,
                                               uint64_t size) {
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    return CI->getValue();
  }

  if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
    auto *ITy = llvm::dyn_cast<llvm::IntegerType>(LI->getType());
    if (!ITy) {
      return std::nullopt;
    }

    auto off = getConstantOffsetFromPtr(LI->getPointerOperand(), AI, DL);
    if (!off.has_value()) {
      return std::nullopt;
    }

    uint64_t load_size = DL.getTypeStoreSize(ITy);
    if (*off < 0 || static_cast<uint64_t>(*off) + load_size > size) {
      return std::nullopt;
    }

    llvm::APInt out(ITy->getBitWidth(), 0);
    for (uint64_t i = 0; i < load_size; ++i) {
      uint64_t idx = static_cast<uint64_t>(*off) + i;
      out |= llvm::APInt(ITy->getBitWidth(), bytes[idx]) << (i * 8);
    }
    return out;
  }

  if (auto *Cast = llvm::dyn_cast<llvm::CastInst>(V)) {
    auto in = tryEvaluateIntValue(Cast->getOperand(0), AI, DL, bytes, size);
    if (!in.has_value()) {
      return std::nullopt;
    }
    unsigned bw = Cast->getType()->getIntegerBitWidth();
    switch (Cast->getOpcode()) {
      case llvm::Instruction::Trunc:
        return in->trunc(bw);
      case llvm::Instruction::ZExt:
        return in->zext(bw);
      case llvm::Instruction::SExt:
        return in->sext(bw);
      default:
        return std::nullopt;
    }
  }

  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto lhs = tryEvaluateIntValue(BO->getOperand(0), AI, DL, bytes, size);
    auto rhs = tryEvaluateIntValue(BO->getOperand(1), AI, DL, bytes, size);
    if (!lhs.has_value() || !rhs.has_value()) {
      return std::nullopt;
    }
    if (lhs->getBitWidth() != rhs->getBitWidth()) {
      return std::nullopt;
    }
    switch (BO->getOpcode()) {
      case llvm::Instruction::Add:
        return *lhs + *rhs;
      case llvm::Instruction::Sub:
        return *lhs - *rhs;
      case llvm::Instruction::Xor:
        return *lhs ^ *rhs;
      case llvm::Instruction::Or:
        return *lhs | *rhs;
      case llvm::Instruction::And:
        return *lhs & *rhs;
      case llvm::Instruction::Shl:
        return lhs->shl(*rhs);
      case llvm::Instruction::LShr:
        return lhs->lshr(*rhs);
      case llvm::Instruction::AShr:
        return lhs->ashr(*rhs);
      case llvm::Instruction::Mul:
        return *lhs * *rhs;
      default:
        return std::nullopt;
    }
  }

  return std::nullopt;
}

/// Recursively analyze uses of a pointer derived from an alloca.
/// Returns false if the alloca cannot be promoted to a global constant.
bool analyzeUses(llvm::Value *ptr, llvm::AllocaInst *AI,
                 const llvm::DataLayout &DL, int64_t base_offset,
                 bool offset_known,
                 llvm::SmallVectorImpl<ConstantStoreInfo> &stores,
                 llvm::SmallVectorImpl<llvm::Instruction *> &dead,
                 bool &has_non_entry_store, bool &saw_load) {
  for (auto *U : ptr->users()) {
    if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
      llvm::APInt gep_off(64, 0);
      bool constant_gep = GEP->accumulateConstantOffset(DL, gep_off);
      int64_t new_off =
          base_offset + (constant_gep ? gep_off.getSExtValue() : 0);
      if (!analyzeUses(GEP, AI, DL, new_off, offset_known && constant_gep,
                       stores, dead, has_non_entry_store, saw_load))
        return false;
    } else if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
      // Storing the alloca pointer itself somewhere means it escapes.
      if (SI->getValueOperand() == ptr)
        return false;
      if (!offset_known)
        return false;
      if (SI->getParent() != &AI->getFunction()->getEntryBlock()) {
        has_non_entry_store = true;
      }
      stores.push_back({SI, base_offset});
    } else if (llvm::isa<llvm::LoadInst>(U)) {
      // Loads are fine — they'll read from the global after promotion.
      saw_load = true;
    } else if (auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(U)) {
      // Handle stack-address math patterns:
      //   ptrtoint -> add/sub const -> inttoptr -> load/store
      if (!analyzeIntUses(PTI, AI, DL, base_offset, offset_known, stores, dead,
                          has_non_entry_store, saw_load))
        return false;
    } else if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(U)) {
      auto id = II->getIntrinsicID();
      if (id == llvm::Intrinsic::lifetime_start ||
          id == llvm::Intrinsic::lifetime_end) {
        dead.push_back(II);
        continue;
      }
      return false;
    } else {
      return false;
    }
  }
  return true;
}

bool analyzeIntUses(llvm::Value *ival, llvm::AllocaInst *AI,
                    const llvm::DataLayout &DL, int64_t base_offset,
                    bool offset_known,
                    llvm::SmallVectorImpl<ConstantStoreInfo> &stores,
                    llvm::SmallVectorImpl<llvm::Instruction *> &dead,
                    bool &has_non_entry_store, bool &saw_load) {
  for (auto *U : ival->users()) {
    if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(U)) {
      if (!analyzeUses(ITP, AI, DL, base_offset, offset_known, stores, dead,
                       has_non_entry_store, saw_load))
        return false;
      continue;
    }

    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U)) {
      auto opcode = BO->getOpcode();
      if (opcode != llvm::Instruction::Add &&
          opcode != llvm::Instruction::Sub) {
        return false;
      }

      bool lhs_is_ival = BO->getOperand(0) == ival;
      bool rhs_is_ival = BO->getOperand(1) == ival;
      bool has_const_delta = false;
      int64_t delta = 0;

      if (lhs_is_ival) {
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
          has_const_delta = true;
          delta = C->getSExtValue();
          if (opcode == llvm::Instruction::Sub) {
            delta = -delta;
          }
        }
      } else if (rhs_is_ival && opcode == llvm::Instruction::Add) {
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
          has_const_delta = true;
          delta = C->getSExtValue();
        }
      }

      int64_t new_off = base_offset + (has_const_delta ? delta : 0);
      if (!analyzeIntUses(BO, AI, DL, new_off,
                          offset_known && has_const_delta, stores, dead,
                          has_non_entry_store, saw_load)) {
        return false;
      }
      continue;
    }

    if (llvm::isa<llvm::SExtInst>(U) || llvm::isa<llvm::ZExtInst>(U) ||
        llvm::isa<llvm::TruncInst>(U)) {
      if (!analyzeIntUses(llvm::cast<llvm::Instruction>(U), AI, DL,
                          base_offset, offset_known, stores, dead,
                          has_non_entry_store, saw_load)) {
        return false;
      }
      continue;
    }

    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
      if (SI->getValueOperand() == ival) {
        continue;
      }
      return false;
    }

    // Integer-only consumers (icmp/select/calls/etc.) do not create new
    // address-derived memory accesses on their own. Ignore them so we don't
    // reject promotable allocas just because pointer-as-int is also used for
    // flag math or bookkeeping.
    continue;
  }

  return true;
}

}  // namespace

llvm::PreservedAnalyses OutlineConstantStackDataPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  auto &DL = F.getDataLayout();
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();
  bool changed = false;

  llvm::SmallVector<llvm::AllocaInst *, 4> allocas;
  for (auto &I : F.getEntryBlock())
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I))
      allocas.push_back(AI);

  for (auto *AI : allocas) {
    if (!AI->isStaticAlloca())
      continue;
    auto alloc_size = AI->getAllocationSize(DL);
    if (!alloc_size || alloc_size->isScalable())
      continue;
    uint64_t size = alloc_size->getFixedValue();
    if (size == 0 || size > 65536)
      continue;

    llvm::SmallVector<ConstantStoreInfo, 8> stores;
    llvm::SmallVector<llvm::Instruction *, 4> dead;
    bool has_non_entry_store = false;
    bool saw_load = false;

    if (!analyzeUses(AI, AI, DL, 0, true, stores, dead, has_non_entry_store,
                     saw_load))
      continue;
    if (stores.empty())
      continue;
    if (has_non_entry_store && saw_load)
      continue;

    // Sort stores by instruction order so overlapping writes resolve correctly
    // (last write wins).
    llvm::sort(stores, [](const ConstantStoreInfo &a,
                          const ConstantStoreInfo &b) {
      return a.inst->comesBefore(b.inst);
    });

    // Build byte array from constant stores.
    std::vector<uint8_t> bytes(size, 0);
    bool supported = true;
    for (auto &[SI, offset] : stores) {
      auto *val = SI->getValueOperand();
      unsigned store_size = DL.getTypeStoreSize(val->getType());

      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(val)) {
        llvm::APInt apval = CI->getValue();
        for (unsigned i = 0; i < store_size; ++i) {
          int64_t idx = offset + i;
          if (idx >= 0 && static_cast<uint64_t>(idx) < size)
            bytes[idx] = apval.extractBitsAsZExtValue(8, i * 8);
        }
      } else if (auto *CDS = llvm::dyn_cast<llvm::ConstantDataSequential>(val)) {
        llvm::StringRef raw = CDS->getRawDataValues();
        for (unsigned i = 0; i < raw.size() && i < store_size; ++i) {
          int64_t idx = offset + i;
          if (idx >= 0 && static_cast<uint64_t>(idx) < size)
            bytes[idx] = static_cast<uint8_t>(raw[i]);
        }
      } else if (llvm::isa<llvm::ConstantAggregateZero>(val)) {
        // Already zero-initialized.
      } else if (val->getType()->isIntegerTy()) {
        auto apval = tryEvaluateIntValue(val, AI, DL, bytes, size);
        if (!apval.has_value()) {
          supported = false;
          break;
        }
        for (unsigned i = 0; i < store_size; ++i) {
          int64_t idx = offset + i;
          if (idx >= 0 && static_cast<uint64_t>(idx) < size) {
            bytes[idx] = apval->extractBitsAsZExtValue(8, i * 8);
          }
        }
      } else {
        supported = false;
        break;
      }
    }
    if (!supported) {
      continue;
    }

    // Create global constant.
    auto *initializer = llvm::ConstantDataArray::get(Ctx, bytes);
    auto *GV = new llvm::GlobalVariable(
        M, initializer->getType(), /*isConstant=*/true,
        llvm::GlobalValue::PrivateLinkage, initializer, ".const_stack");
    GV->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    GV->setAlignment(AI->getAlign());

    // Delete stores and lifetime markers.
    for (auto &[SI, offset] : stores)
      SI->eraseFromParent();
    for (auto *I : dead)
      I->eraseFromParent();

    // Replace alloca with global constant pointer.
    AI->replaceAllUsesWith(GV);
    AI->eraseFromParent();
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

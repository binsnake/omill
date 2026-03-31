#include "omill/Passes/OptimizeState.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/Debug.h>

#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

#define DEBUG_TYPE "optimize-state"

namespace omill {

namespace {

// ============================================================================
// Shared utility
// ============================================================================

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

// ============================================================================
// Phase 1: DeadStateFlagElimination
// ============================================================================

static bool eliminateDeadFlagStores(llvm::Function &F,
                                     const llvm::DataLayout &DL,
                                     const StateFieldMap &field_map) {
  llvm::SmallVector<llvm::Instruction *, 16> dead_stores;

  for (auto &BB : F) {
    llvm::DenseMap<unsigned, llvm::StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          auto field = field_map.fieldAtOffset(static_cast<unsigned>(off));
          if (field && field->category == StateFieldCategory::kFlag)
            last_store.erase(static_cast<unsigned>(off));
        }
        continue;
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          auto field = field_map.fieldAtOffset(static_cast<unsigned>(off));
          if (field && field->category == StateFieldCategory::kFlag) {
            unsigned u_off = static_cast<unsigned>(off);
            auto it = last_store.find(u_off);
            if (it != last_store.end()) {
              dead_stores.push_back(it->second);
            }
            last_store[u_off] = SI;
          }
        }
        continue;
      }

      if (llvm::isa<llvm::CallInst>(&I) && !llvm::isa<llvm::IntrinsicInst>(&I)) {
        last_store.clear();
      }
    }
  }

  for (auto *I : dead_stores)
    I->eraseFromParent();

  return !dead_stores.empty();
}

// ============================================================================
// Phase 2: DeadStateStoreElimination
// ============================================================================

static bool eliminateDeadStateStores(llvm::Function &F,
                                      const llvm::DataLayout &DL) {
  llvm::SmallVector<llvm::Instruction *, 32> dead_stores;

  for (auto &BB : F) {
    llvm::DenseMap<unsigned, llvm::StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0)
          last_store.erase(static_cast<unsigned>(off));
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u_off = static_cast<unsigned>(off);
          auto it = last_store.find(u_off);
          if (it != last_store.end())
            dead_stores.push_back(it->second);
          last_store[u_off] = SI;
        }
      }

      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (!CI->isInlineAsm() && !llvm::isa<llvm::IntrinsicInst>(CI))
          last_store.clear();
      }
    }
  }

  for (auto *I : dead_stores)
    I->eraseFromParent();

  return !dead_stores.empty();
}

// ============================================================================
// Phase 3: EliminateRedundantByteStores
// ============================================================================

static bool getBaseAndOffset(llvm::Value *ptr, llvm::Value *&base,
                              uint64_t &offset) {
  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    if (GEP->getNumIndices() == 1) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1))) {
        base = GEP->getPointerOperand();
        offset = CI->getZExtValue();
        return true;
      }
    }
  }
  base = ptr;
  offset = 0;
  return true;
}

static bool getConstantByte(llvm::Constant *C, const llvm::DataLayout &DL,
                             unsigned byte_offset, uint8_t &out) {
  llvm::Type *ty = C->getType();
  unsigned total_bytes = DL.getTypeStoreSize(ty);
  if (byte_offset >= total_bytes)
    return false;

  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(C)) {
    llvm::APInt val = CI->getValue();
    out = val.extractBits(8, byte_offset * 8).getZExtValue();
    return true;
  }

  if (auto *CDV = llvm::dyn_cast<llvm::ConstantDataVector>(C)) {
    unsigned elem_size = DL.getTypeStoreSize(CDV->getElementType());
    unsigned elem_idx = byte_offset / elem_size;
    unsigned byte_in_elem = byte_offset % elem_size;
    if (auto *elem_ci = llvm::dyn_cast<llvm::ConstantInt>(CDV->getElementAsConstant(elem_idx))) {
      llvm::APInt val = elem_ci->getValue();
      out = val.extractBits(8, byte_in_elem * 8).getZExtValue();
      return true;
    }
    return false;
  }

  if (llvm::isa<llvm::ConstantAggregateZero>(C)) {
    out = 0;
    return true;
  }

  return false;
}

static bool eliminateRedundantByteStores(llvm::Function &F,
                                          const llvm::DataLayout &DL) {
  bool changed = false;

  for (auto &BB : F) {
    struct WideStore {
      llvm::Value *base;
      uint64_t offset;
      llvm::Constant *value;
      unsigned size;
    };
    llvm::SmallVector<WideStore, 16> wide_stores;
    llvm::SmallVector<llvm::StoreInst *, 16> dead_stores;

    for (auto &I : BB) {
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI) continue;

      llvm::Value *base = nullptr;
      uint64_t offset = 0;
      if (!getBaseAndOffset(SI->getPointerOperand(), base, offset))
        continue;

      unsigned store_size = DL.getTypeStoreSize(SI->getValueOperand()->getType());

      if (auto *C = llvm::dyn_cast<llvm::Constant>(SI->getValueOperand())) {
        if (store_size > 1) {
          wide_stores.erase(
              std::remove_if(wide_stores.begin(), wide_stores.end(),
                             [&](const WideStore &WS) {
                               if (WS.base != base) return false;
                               return !(offset + store_size <= WS.offset ||
                                        WS.offset + WS.size <= offset);
                             }),
              wide_stores.end());
          wide_stores.push_back({base, offset, C, store_size});
          continue;
        }

        if (store_size == 1) {
          auto *narrow_ci = llvm::dyn_cast<llvm::ConstantInt>(C);
          if (!narrow_ci) continue;
          uint8_t narrow_val = narrow_ci->getZExtValue() & 0xFF;

          for (auto &WS : wide_stores) {
            if (WS.base != base) continue;
            if (offset < WS.offset || offset >= WS.offset + WS.size) continue;
            uint8_t wide_byte = 0;
            if (getConstantByte(WS.value, DL, offset - WS.offset, wide_byte)) {
              if (wide_byte == narrow_val) {
                dead_stores.push_back(SI);
                break;
              }
            }
          }
          continue;
        }
      }

      wide_stores.erase(
          std::remove_if(wide_stores.begin(), wide_stores.end(),
                         [&](const WideStore &WS) {
                           if (WS.base != base) return false;
                           return !(offset + store_size <= WS.offset ||
                                    WS.offset + WS.size <= offset);
                         }),
          wide_stores.end());
    }

    for (auto *SI : dead_stores) {
      SI->eraseFromParent();
      changed = true;
    }
  }

  return changed;
}

// ============================================================================
// Phase 4: PromoteStateToSSA
// ============================================================================

static llvm::Value *buildStateFieldGEP(llvm::IRBuilder<> &Builder,
                                        llvm::Value *state_ptr,
                                        unsigned offset, llvm::Type *field_type,
                                        const llvm::DataLayout &DL) {
  auto *i8_ptr = Builder.CreateBitCast(state_ptr, Builder.getPtrTy());
  auto *gep = Builder.CreateConstGEP1_64(Builder.getInt8Ty(), i8_ptr, offset);
  return gep;
}

static bool hasRemillControlTransfer(const llvm::Function &F) {
  for (const auto &BB : F) {
    for (const auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      auto name = callee->getName();
      if (isDispatchIntrinsicName(name) ||
          name == "__remill_function_return") {
        return true;
      }
      // Before full control-flow lowering, lifted traces can still contain
      // remill helper calls (e.g. *_JMPI_*), not just __remill_* intrinsics.
      // Treat these helpers as control-transfer to avoid collapsing NEXT_PC
      // flow during PromoteStateToSSA.
      if (name.contains_insensitive("jmpi") ||
          name.contains_insensitive("jump") ||
          name.contains_insensitive("function_call") ||
          name.contains_insensitive("function_return")) {
        return true;
      }
    }
  }
  return false;
}

static bool promoteStateToSSA(llvm::Function &F, const llvm::DataLayout &DL) {
  llvm::Value *state_ptr = (F.arg_size() > 0) ? F.getArg(0) : nullptr;
  if (!state_ptr)
    return false;

  // PromoteStateToSSA before control-flow lowering is unsafe on traces that
  // still contain remill dispatch/transfer intrinsics. Flushing/reloading
  // around these calls can over-constrain NEXT_PC/state flow and collapse
  // traces to incorrect self-loops.
  if (F.getName().starts_with("sub_") && hasRemillControlTransfer(F) &&
      !F.hasFnAttribute("omill.vm_handler"))
    return false;

  struct FieldInfo {
    unsigned offset;
    llvm::Type *type;
    unsigned max_access_size = 0;
    llvm::SmallVector<llvm::LoadInst *, 4> loads;
    llvm::SmallVector<llvm::StoreInst *, 4> stores;
    bool is_live_in = false;
  };

  llvm::DenseMap<unsigned, FieldInfo> fields;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off < 0) continue;
        unsigned u_off = static_cast<unsigned>(off);
        auto &info = fields[u_off];
        info.offset = u_off;
        unsigned sz = DL.getTypeStoreSize(LI->getType());
        if (sz > info.max_access_size) {
          info.max_access_size = sz;
          info.type = LI->getType();
        }
        info.loads.push_back(LI);
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off < 0) continue;
        unsigned u_off = static_cast<unsigned>(off);
        auto &info = fields[u_off];
        info.offset = u_off;
        unsigned sz = DL.getTypeStoreSize(SI->getValueOperand()->getType());
        if (sz > info.max_access_size) {
          info.max_access_size = sz;
          info.type = SI->getValueOperand()->getType();
        }
        info.stores.push_back(SI);
      }
    }
  }

  if (fields.empty())
    return false;

  // Be conservative across CFG order: any field that is ever loaded is a
  // live-in. Using "first textual access" can misclassify fields when a store
  // appears earlier in block order but does not dominate all loads.
  for (auto &[offset, info] : fields) {
    (void)offset;
    info.is_live_in = !info.loads.empty();
  }

  // Phase 2: Create allocas
  llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  llvm::DenseMap<unsigned, llvm::AllocaInst *> field_allocas;

  for (auto &[offset, info] : fields) {
    auto *alloca = EntryBuilder.CreateAlloca(info.type, nullptr,
                                              "state_" + std::to_string(offset));
    field_allocas[offset] = alloca;

    if (info.is_live_in) {
      llvm::IRBuilder<> Builder(alloca->getNextNode());
      auto *gep = buildStateFieldGEP(Builder, state_ptr, offset,
                                      info.type, DL);
      auto *initial = Builder.CreateLoad(info.type, gep, "state_init");
      Builder.CreateStore(initial, alloca);
    }
  }

  // Phase 3: Replace loads/stores
  for (auto &[offset, info] : fields) {
    auto *alloca = field_allocas[offset];

    for (auto *LI : info.loads) {
      llvm::IRBuilder<> Builder(LI);
      auto *new_load = Builder.CreateLoad(LI->getType(), alloca);
      LI->replaceAllUsesWith(new_load);
      LI->eraseFromParent();
    }

    for (auto *SI : info.stores) {
      llvm::IRBuilder<> Builder(SI);
      auto *val = SI->getValueOperand();
      Builder.CreateStore(val, alloca);

      unsigned store_size = DL.getTypeStoreSize(val->getType());
      for (auto &[other_off, other_info] : fields) {
        if (other_off > offset && other_off < offset + store_size) {
          auto *other_alloca = field_allocas[other_off];
          unsigned byte_off = other_off - offset;
          auto *sub_ptr = Builder.CreateConstGEP1_64(
              Builder.getInt8Ty(), alloca, byte_off);
          auto *sub_val = Builder.CreateLoad(other_info.type, sub_ptr,
                                              "wide.sub");
          Builder.CreateStore(sub_val, other_alloca);
        }
      }

      SI->eraseFromParent();
    }
  }

  // Phase 3.5: Flush/reload around calls that take State
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;
      bool takes_state = false;
      for (auto &arg : CI->args()) {
        if (arg.get() == state_ptr) { takes_state = true; break; }
      }
      if (!takes_state) continue;

      {
        llvm::IRBuilder<> Builder(CI);
        for (auto &[offset, info] : fields) {
          if (info.stores.empty()) continue;
          auto *alloca = field_allocas[offset];
          auto *val = Builder.CreateLoad(info.type, alloca);
          auto *gep = buildStateFieldGEP(Builder, state_ptr, offset,
                                          info.type, DL);
          Builder.CreateStore(val, gep);
        }
      }

      {
        if (CI->isTailCall() || CI->isMustTailCall())
          continue;

        llvm::IRBuilder<> Builder(CI->getNextNode());
        for (auto &[offset, info] : fields) {
          // Only reload fields that have loads — fields with no loads
          // anywhere in the function can't be observed, so skipping
          // their reload is safe and avoids dead alloca churn in SROA.
          if (info.loads.empty()) continue;
          auto *alloca = field_allocas[offset];
          auto *gep = buildStateFieldGEP(Builder, state_ptr, offset,
                                          info.type, DL);
          auto *reloaded = Builder.CreateLoad(info.type, gep);
          Builder.CreateStore(reloaded, alloca);
        }
      }
    }
  }

  // Phase 4: Write-back before returns
  for (auto &BB : F) {
    auto *term = BB.getTerminator();
    if (!term) continue;

    bool is_exit = llvm::isa<llvm::ReturnInst>(term);
    if (!is_exit) {
      if (auto *prev = term->getPrevNode()) {
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(prev)) {
          if (CI->isTailCall() || CI->isMustTailCall())
            is_exit = true;
        }
      }
    }
    if (!is_exit) continue;

    llvm::Instruction *insert_point = term;
    if (auto *prev = term->getPrevNode()) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(prev)) {
        if (CI->isTailCall() || CI->isMustTailCall())
          insert_point = CI;
      }
    }
    llvm::IRBuilder<> Builder(insert_point);
    for (auto &[offset, info] : fields) {
      if (info.stores.empty()) continue;
      auto *alloca = field_allocas[offset];
      auto *val = Builder.CreateLoad(info.type, alloca);
      auto *gep = buildStateFieldGEP(Builder, state_ptr, offset,
                                      info.type, DL);
      Builder.CreateStore(val, gep);
    }
  }

  return true;
}

// ============================================================================
// Phase 5: DeadStateRoundtripElimination
// ============================================================================

static bool getGEPBaseAndOffset(llvm::Value *V, llvm::Value *&base,
                                 uint64_t &offset) {
  auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(V);
  if (!GEP || GEP->getNumIndices() != 1)
    return false;
  auto *Idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
  if (!Idx)
    return false;
  base = GEP->getPointerOperand();
  offset = Idx->getZExtValue();
  return true;
}

static bool noInterveningClobber(llvm::LoadInst *LI, llvm::StoreInst *SI,
                                  llvm::Value *base, uint64_t offset) {
  if (LI->getParent() != SI->getParent())
    return false;

  for (auto it = std::next(LI->getIterator()); &*it != SI; ++it) {
    if (llvm::isa<llvm::CallBase>(&*it))
      return false;
    if (auto *S = llvm::dyn_cast<llvm::StoreInst>(&*it)) {
      llvm::Value *s_base = nullptr;
      uint64_t s_offset = 0;
      if (getGEPBaseAndOffset(S->getPointerOperand(), s_base, s_offset)) {
        if (s_base == base && s_offset == offset)
          return false;
      } else {
        return false;
      }
    }
  }
  return true;
}

static bool eliminateDeadRoundtrips(llvm::Function &F) {
  bool changed = false;
  llvm::SmallVector<std::pair<llvm::LoadInst *, llvm::StoreInst *>, 16> to_remove;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI || SI->isVolatile()) continue;

      auto *LI = llvm::dyn_cast<llvm::LoadInst>(SI->getValueOperand());
      if (!LI || LI->isVolatile()) continue;
      if (!LI->hasOneUse()) continue;

      llvm::Value *load_base = nullptr, *store_base = nullptr;
      uint64_t load_offset = 0, store_offset = 0;
      if (!getGEPBaseAndOffset(LI->getPointerOperand(), load_base, load_offset))
        continue;
      if (!getGEPBaseAndOffset(SI->getPointerOperand(), store_base, store_offset))
        continue;

      if (load_base != store_base || load_offset != store_offset) continue;
      if (!noInterveningClobber(LI, SI, load_base, load_offset)) continue;

      to_remove.push_back({LI, SI});
    }
  }

  for (auto &[LI, SI] : to_remove) {
    SI->eraseFromParent();
    if (LI->use_empty())
      LI->eraseFromParent();
    changed = true;
  }

  return changed;
}

}  // namespace

// ============================================================================
// Pass entry point
// ============================================================================

llvm::PreservedAnalyses OptimizeStatePass::run(llvm::Function &F,
                                          llvm::FunctionAnalysisManager &AM) {
  auto &DL = F.getParent()->getDataLayout();
  bool changed = false;

  if (phases_ & OptimizePhases::DeadFlags) {
    StateFieldMap field_map(*F.getParent());
    changed |= eliminateDeadFlagStores(F, DL, field_map);
  }

  if (phases_ & OptimizePhases::DeadStores)
    changed |= eliminateDeadStateStores(F, DL);

  if (phases_ & OptimizePhases::RedundantBytes)
    changed |= eliminateRedundantByteStores(F, DL);

  if (phases_ & OptimizePhases::Promote)
    changed |= promoteStateToSSA(F, DL);

  if (phases_ & OptimizePhases::Roundtrip)
    changed |= eliminateDeadRoundtrips(F);

  if (!changed)
    return llvm::PreservedAnalyses::all();

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

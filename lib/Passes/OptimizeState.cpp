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

#include "omill/Utils/StateFieldMap.h"

#define DEBUG_TYPE "optimize-state"

using namespace llvm;

namespace omill {

namespace {

// ============================================================================
// Shared utility
// ============================================================================

int64_t resolveStateOffset(Value *ptr, const DataLayout &DL) {
  int64_t total_offset = 0;
  Value *base = ptr;

  while (true) {
    if (auto *GEP = dyn_cast<GEPOperator>(base)) {
      APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = dyn_cast<BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (auto *arg = dyn_cast<Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }
  return -1;
}

// ============================================================================
// Phase 1: DeadStateFlagElimination
// ============================================================================

static bool eliminateDeadFlagStores(Function &F, const DataLayout &DL,
                                     const StateFieldMap &field_map) {
  SmallVector<Instruction *, 16> dead_stores;

  for (auto &BB : F) {
    DenseMap<unsigned, StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          auto field = field_map.fieldAtOffset(static_cast<unsigned>(off));
          if (field && field->category == StateFieldCategory::kFlag)
            last_store.erase(static_cast<unsigned>(off));
        }
        continue;
      }

      if (auto *SI = dyn_cast<StoreInst>(&I)) {
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

      if (isa<CallInst>(&I) && !isa<IntrinsicInst>(&I)) {
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

static bool eliminateDeadStateStores(Function &F, const DataLayout &DL) {
  SmallVector<Instruction *, 32> dead_stores;

  for (auto &BB : F) {
    DenseMap<unsigned, StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0)
          last_store.erase(static_cast<unsigned>(off));
      }

      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u_off = static_cast<unsigned>(off);
          auto it = last_store.find(u_off);
          if (it != last_store.end())
            dead_stores.push_back(it->second);
          last_store[u_off] = SI;
        }
      }

      if (auto *CI = dyn_cast<CallInst>(&I)) {
        if (!CI->isInlineAsm() && !isa<IntrinsicInst>(CI))
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

static bool getBaseAndOffset(Value *ptr, Value *&base, uint64_t &offset) {
  if (auto *GEP = dyn_cast<GetElementPtrInst>(ptr)) {
    if (GEP->getNumIndices() == 1) {
      if (auto *CI = dyn_cast<ConstantInt>(GEP->getOperand(1))) {
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

static bool getConstantByte(Constant *C, const DataLayout &DL,
                             unsigned byte_offset, uint8_t &out) {
  Type *ty = C->getType();
  unsigned total_bytes = DL.getTypeStoreSize(ty);
  if (byte_offset >= total_bytes)
    return false;

  if (auto *CI = dyn_cast<ConstantInt>(C)) {
    APInt val = CI->getValue();
    out = val.extractBits(8, byte_offset * 8).getZExtValue();
    return true;
  }

  if (auto *CDV = dyn_cast<ConstantDataVector>(C)) {
    unsigned elem_size = DL.getTypeStoreSize(CDV->getElementType());
    unsigned elem_idx = byte_offset / elem_size;
    unsigned byte_in_elem = byte_offset % elem_size;
    if (auto *elem_ci = dyn_cast<ConstantInt>(CDV->getElementAsConstant(elem_idx))) {
      APInt val = elem_ci->getValue();
      out = val.extractBits(8, byte_in_elem * 8).getZExtValue();
      return true;
    }
    return false;
  }

  if (isa<ConstantAggregateZero>(C)) {
    out = 0;
    return true;
  }

  return false;
}

static bool eliminateRedundantByteStores(Function &F, const DataLayout &DL) {
  bool changed = false;

  for (auto &BB : F) {
    struct WideStore {
      Value *base;
      uint64_t offset;
      Constant *value;
      unsigned size;
    };
    SmallVector<WideStore, 16> wide_stores;
    SmallVector<StoreInst *, 16> dead_stores;

    for (auto &I : BB) {
      auto *SI = dyn_cast<StoreInst>(&I);
      if (!SI) continue;

      Value *base = nullptr;
      uint64_t offset = 0;
      if (!getBaseAndOffset(SI->getPointerOperand(), base, offset))
        continue;

      unsigned store_size = DL.getTypeStoreSize(SI->getValueOperand()->getType());

      if (auto *C = dyn_cast<Constant>(SI->getValueOperand())) {
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
          auto *narrow_ci = dyn_cast<ConstantInt>(C);
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

static Value *buildStateFieldGEP(IRBuilder<> &Builder, Value *state_ptr,
                                  unsigned offset, Type *field_type,
                                  const DataLayout &DL) {
  auto *i8_ptr = Builder.CreateBitCast(state_ptr, Builder.getPtrTy());
  auto *gep = Builder.CreateConstGEP1_64(Builder.getInt8Ty(), i8_ptr, offset);
  return gep;
}

static bool promoteStateToSSA(Function &F, const DataLayout &DL) {
  Value *state_ptr = (F.arg_size() > 0) ? F.getArg(0) : nullptr;
  if (!state_ptr)
    return false;

  struct FieldInfo {
    unsigned offset;
    Type *type;
    unsigned max_access_size = 0;
    SmallVector<LoadInst *, 4> loads;
    SmallVector<StoreInst *, 4> stores;
    bool is_live_in = false;
  };

  DenseMap<unsigned, FieldInfo> fields;
  DenseSet<unsigned> first_access_seen;

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *LI = dyn_cast<LoadInst>(&I)) {
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
        if (!first_access_seen.count(u_off)) {
          first_access_seen.insert(u_off);
          info.is_live_in = true;
        }
      }

      if (auto *SI = dyn_cast<StoreInst>(&I)) {
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
        if (!first_access_seen.count(u_off)) {
          first_access_seen.insert(u_off);
        }
      }
    }
  }

  if (fields.empty())
    return false;

  // Phase 2: Create allocas
  IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  DenseMap<unsigned, AllocaInst *> field_allocas;

  for (auto &[offset, info] : fields) {
    auto *alloca = EntryBuilder.CreateAlloca(info.type, nullptr,
                                              "state_" + std::to_string(offset));
    field_allocas[offset] = alloca;

    if (info.is_live_in) {
      IRBuilder<> Builder(alloca->getNextNode());
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
      IRBuilder<> Builder(LI);
      auto *new_load = Builder.CreateLoad(LI->getType(), alloca);
      LI->replaceAllUsesWith(new_load);
      LI->eraseFromParent();
    }

    for (auto *SI : info.stores) {
      IRBuilder<> Builder(SI);
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
      auto *CI = dyn_cast<CallInst>(&I);
      if (!CI) continue;
      bool takes_state = false;
      for (auto &arg : CI->args()) {
        if (arg.get() == state_ptr) { takes_state = true; break; }
      }
      if (!takes_state) continue;

      {
        IRBuilder<> Builder(CI);
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
        IRBuilder<> Builder(CI->getNextNode());
        for (auto &[offset, info] : fields) {
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

    bool is_exit = isa<ReturnInst>(term);
    if (!is_exit) {
      if (auto *CI = dyn_cast<CallInst>(BB.getTerminator()->getPrevNode())) {
        if (CI->isTailCall() || CI->isMustTailCall())
          is_exit = true;
      }
    }
    if (!is_exit) continue;

    Instruction *insert_point = term;
    if (auto *prev = term->getPrevNode()) {
      if (auto *CI = dyn_cast<CallInst>(prev)) {
        if (CI->isTailCall() || CI->isMustTailCall())
          insert_point = CI;
      }
    }
    IRBuilder<> Builder(insert_point);
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

static bool getGEPBaseAndOffset(Value *V, Value *&base, uint64_t &offset) {
  auto *GEP = dyn_cast<GetElementPtrInst>(V);
  if (!GEP || GEP->getNumIndices() != 1)
    return false;
  auto *Idx = dyn_cast<ConstantInt>(GEP->getOperand(1));
  if (!Idx)
    return false;
  base = GEP->getPointerOperand();
  offset = Idx->getZExtValue();
  return true;
}

static bool noInterveningClobber(LoadInst *LI, StoreInst *SI,
                                  Value *base, uint64_t offset) {
  if (LI->getParent() != SI->getParent())
    return false;

  for (auto it = std::next(LI->getIterator()); &*it != SI; ++it) {
    if (isa<CallBase>(&*it))
      return false;
    if (auto *S = dyn_cast<StoreInst>(&*it)) {
      Value *s_base = nullptr;
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

static bool eliminateDeadRoundtrips(Function &F) {
  bool changed = false;
  SmallVector<std::pair<LoadInst *, StoreInst *>, 16> to_remove;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *SI = dyn_cast<StoreInst>(&I);
      if (!SI || SI->isVolatile()) continue;

      auto *LI = dyn_cast<LoadInst>(SI->getValueOperand());
      if (!LI || LI->isVolatile()) continue;
      if (!LI->hasOneUse()) continue;

      Value *load_base = nullptr, *store_base = nullptr;
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

PreservedAnalyses OptimizeStatePass::run(Function &F,
                                          FunctionAnalysisManager &AM) {
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
    return PreservedAnalyses::all();

  return PreservedAnalyses::none();
}

}  // namespace omill

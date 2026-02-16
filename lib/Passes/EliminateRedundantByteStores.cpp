#include "omill/Passes/EliminateRedundantByteStores.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#define DEBUG_TYPE "eliminate-redundant-byte-stores"

using namespace llvm;

namespace omill {

namespace {

/// Try to extract the State base pointer and byte offset from a pointer value.
/// Returns true if the pointer is `getelementptr i8, ptr %base, i64 <offset>`.
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
  // No GEP — the pointer itself is at offset 0.
  base = ptr;
  offset = 0;
  return true;
}

/// Get the byte value at a specific offset within a constant.
/// Returns true if the byte is known.
static bool getConstantByte(Constant *C, const DataLayout &DL,
                             unsigned byte_offset, uint8_t &out) {
  Type *ty = C->getType();
  unsigned total_bytes = DL.getTypeStoreSize(ty);
  if (byte_offset >= total_bytes)
    return false;

  if (auto *CI = dyn_cast<ConstantInt>(C)) {
    APInt val = CI->getValue();
    // Assuming little-endian (x86-64).
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

static bool runOnFunction(Function &F) {
  bool changed = false;
  const DataLayout &DL = F.getParent()->getDataLayout();

  // For each basic block, track wide constant stores and check if subsequent
  // narrow stores are redundant.
  for (auto &BB : F) {
    // Map: (base, offset) → (Constant*, store_size) for active wide stores.
    // We use a simple approach: collect wide stores, then check narrow stores.
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
      if (!SI)
        continue;

      Value *base = nullptr;
      uint64_t offset = 0;
      if (!getBaseAndOffset(SI->getPointerOperand(), base, offset))
        continue;

      unsigned store_size = DL.getTypeStoreSize(SI->getValueOperand()->getType());

      // If this is a wide store with a constant value, record it.
      if (auto *C = dyn_cast<Constant>(SI->getValueOperand())) {
        if (store_size > 1) {
          // Invalidate any wide store that this overlaps with.
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

        // Narrow constant store — check if it's subsumed by a wide store.
        if (store_size == 1) {
          auto *narrow_ci = dyn_cast<ConstantInt>(C);
          if (!narrow_ci)
            continue;
          uint8_t narrow_val = narrow_ci->getZExtValue() & 0xFF;

          for (auto &WS : wide_stores) {
            if (WS.base != base)
              continue;
            if (offset < WS.offset || offset >= WS.offset + WS.size)
              continue;
            // This narrow store falls within the wide store's range.
            uint8_t wide_byte = 0;
            if (getConstantByte(WS.value, DL,
                                 offset - WS.offset, wide_byte)) {
              if (wide_byte == narrow_val) {
                dead_stores.push_back(SI);
                break;
              }
            }
          }
          continue;
        }
      }

      // Non-constant store invalidates overlapping wide stores.
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

}  // namespace

PreservedAnalyses EliminateRedundantByteStoresPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  if (!runOnFunction(F))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

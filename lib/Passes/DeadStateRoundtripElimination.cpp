#include "omill/Passes/DeadStateRoundtripElimination.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Debug.h>

#define DEBUG_TYPE "dead-state-roundtrip-elimination"

using namespace llvm;

namespace omill {

namespace {

/// Extract the base pointer and constant byte offset from a GEP.
/// Returns false if the pointer is not a single-index constant GEP.
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

/// Check that there are no stores to the same (base, offset) or calls
/// between the load and the store.  Both must be in the same basic block.
static bool noInterveningClobber(LoadInst *LI, StoreInst *SI,
                                  Value *base, uint64_t offset) {
  if (LI->getParent() != SI->getParent())
    return false;

  for (auto it = std::next(LI->getIterator()); &*it != SI; ++it) {
    // Calls may modify memory through the base pointer.
    if (isa<CallBase>(&*it))
      return false;

    if (auto *S = dyn_cast<StoreInst>(&*it)) {
      Value *s_base = nullptr;
      uint64_t s_offset = 0;
      if (getGEPBaseAndOffset(S->getPointerOperand(), s_base, s_offset)) {
        if (s_base == base && s_offset == offset)
          return false;
      } else {
        // Non-GEP store — conservatively assume it may alias.
        // Only bail if it could alias our base pointer.
        // For safety, bail on any non-GEP store.
        return false;
      }
    }
  }
  return true;
}

static bool runOnFunction(Function &F) {
  bool changed = false;
  SmallVector<std::pair<LoadInst *, StoreInst *>, 16> to_remove;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *SI = dyn_cast<StoreInst>(&I);
      if (!SI || SI->isVolatile())
        continue;

      auto *LI = dyn_cast<LoadInst>(SI->getValueOperand());
      if (!LI || LI->isVolatile())
        continue;

      if (!LI->hasOneUse())
        continue;

      // Both must be GEPs with the same base and offset.
      Value *load_base = nullptr, *store_base = nullptr;
      uint64_t load_offset = 0, store_offset = 0;
      if (!getGEPBaseAndOffset(LI->getPointerOperand(), load_base, load_offset))
        continue;
      if (!getGEPBaseAndOffset(SI->getPointerOperand(), store_base, store_offset))
        continue;

      if (load_base != store_base || load_offset != store_offset)
        continue;

      if (!noInterveningClobber(LI, SI, load_base, load_offset))
        continue;

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

PreservedAnalyses DeadStateRoundtripEliminationPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  if (!runOnFunction(F))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

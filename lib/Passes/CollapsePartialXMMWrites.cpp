#include "omill/Passes/CollapsePartialXMMWrites.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>

#define DEBUG_TYPE "collapse-partial-xmm-writes"

using namespace llvm;

namespace omill {

namespace {

static bool runOnFunction(Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end(); ) {
      auto *EE = dyn_cast<ExtractElementInst>(&*it++);
      if (!EE)
        continue;

      auto *idx_ci = dyn_cast<ConstantInt>(EE->getIndexOperand());
      if (!idx_ci)
        continue;

      auto *SV = dyn_cast<ShuffleVectorInst>(EE->getVectorOperand());
      if (!SV)
        continue;

      // Both input operands have the same type.  The mask indexes into
      // [0, 2*N) where N is the INPUT element count.
      auto *in_ty = dyn_cast<FixedVectorType>(SV->getOperand(0)->getType());
      if (!in_ty)
        continue;

      unsigned lane = idx_ci->getZExtValue();
      int mask_val = SV->getMaskValue(lane);
      if (mask_val < 0)
        continue;  // undef lane

      unsigned num_in_elts = in_ty->getNumElements();
      unsigned mask_unsigned = static_cast<unsigned>(mask_val);

      Value *src_vec;
      unsigned src_lane;
      if (mask_unsigned < num_in_elts) {
        // Lane comes from operand 0.
        src_vec = SV->getOperand(0);
        src_lane = mask_unsigned;
      } else {
        // Lane comes from operand 1.
        src_vec = SV->getOperand(1);
        src_lane = mask_unsigned - num_in_elts;
      }

      // Skip if this is already a direct extract (identity shuffle for this
      // lane from the same operand — nothing to simplify).
      if (src_vec == EE->getVectorOperand() && src_lane == lane)
        continue;

      // Replace: extractelement(shufflevector(A, B, mask), idx)
      //      ->  extractelement(A_or_B, adjusted_idx)
      auto *new_idx = ConstantInt::get(idx_ci->getType(), src_lane);
      auto *new_ee = ExtractElementInst::Create(src_vec, new_idx);
      new_ee->insertBefore(EE->getIterator());
      EE->replaceAllUsesWith(new_ee);
      EE->eraseFromParent();
      changed = true;
    }
  }

  return changed;
}

}  // namespace

PreservedAnalyses CollapsePartialXMMWritesPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  if (!runOnFunction(F))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

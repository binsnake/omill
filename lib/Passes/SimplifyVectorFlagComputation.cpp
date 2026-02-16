#include "omill/Passes/SimplifyVectorFlagComputation.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>

#define DEBUG_TYPE "simplify-vector-flag-computation"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace omill {

namespace {

static bool runOnFunction(Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end(); ) {
      Instruction *I = &*it++;

      // Pattern 1: and(extractelement(sext <N x i1> to <N x iK>, idx), mask)
      // where mask is a power of 2.
      //
      // sext <N x i1> produces all-zeros (0x00) or all-ones (0xFF...).
      // `and i8 %sext_byte, 1` extracts the least significant bit, which
      // equals the original i1 value.  More generally, `and iK %sext_val, 2^n`
      // is equivalent to `shl(zext(extractelement <N x i1>, idx), n)`.
      Value *ee_val, *mask_val;
      if (!match(I, m_And(m_Value(ee_val), m_Value(mask_val))))
        continue;

      auto *mask_ci = dyn_cast<ConstantInt>(mask_val);
      if (!mask_ci)
        continue;

      APInt mask_ap = mask_ci->getValue();
      if (!mask_ap.isPowerOf2())
        continue;

      // The operand should be extractelement from a sext <N x i1>.
      auto *EE = dyn_cast<ExtractElementInst>(ee_val);
      if (!EE)
        continue;

      auto *sext = dyn_cast<SExtInst>(EE->getVectorOperand());
      if (!sext)
        continue;

      auto *src_vec_ty = dyn_cast<FixedVectorType>(sext->getOperand(0)->getType());
      if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
        continue;

      // Build replacement:
      //   %flag = extractelement <N x i1> %cmp, idx
      //   %zext = zext i1 %flag to iK
      //   %result = shl iK %zext, log2(mask)   [if mask != 1]
      IRBuilder<> Builder(I);
      Value *flag = Builder.CreateExtractElement(sext->getOperand(0),
                                                  EE->getIndexOperand());
      Value *zext_val = Builder.CreateZExt(flag, I->getType());

      Value *result;
      unsigned shift = mask_ap.logBase2();
      if (shift == 0) {
        result = zext_val;
      } else {
        result = Builder.CreateShl(zext_val, shift);
      }

      I->replaceAllUsesWith(result);
      I->eraseFromParent();
      changed = true;
    }
  }

  return changed;
}

}  // namespace

PreservedAnalyses SimplifyVectorFlagComputationPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  if (!runOnFunction(F))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

#include "omill/Passes/LowerFlagIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::PreservedAnalyses LowerFlagIntrinsicsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  llvm::SmallVector<llvm::CallInst *, 32> to_lower;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      auto kind = table.classifyCall(CI);
      auto cat = IntrinsicTable::categoryOf(kind);
      if (cat == IntrinsicCategory::kFlag ||
          cat == IntrinsicCategory::kComparison) {
        to_lower.push_back(CI);
      }
    }
  }

  if (to_lower.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto *CI : to_lower) {
    // The first argument to all flag computation and comparison intrinsics
    // IS the result. The remaining arguments are the operands that were used
    // to compute it (kept for tracing/debugging purposes in remill).
    //
    // __remill_flag_computation_zero(bool result, ...) -> result
    // __remill_compare_eq(bool result) -> result
    llvm::Value *result = CI->getArgOperand(0);

    // Replace all uses of the call with the first argument.
    CI->replaceAllUsesWith(result);
    CI->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

#include "omill/Passes/LowerUndefinedIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::PreservedAnalyses LowerUndefinedIntrinsicsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  llvm::SmallVector<llvm::CallInst *, 16> to_lower;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      if (IntrinsicTable::categoryOf(table.classifyCall(CI)) ==
          IntrinsicCategory::kUndefined) {
        to_lower.push_back(CI);
      }
    }
  }

  if (to_lower.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto *CI : to_lower) {
    // Replace __remill_undefined_*() with freeze(poison).
    // Using freeze(poison) rather than undef prevents UB propagation
    // while still allowing LLVM to reason about the value being
    // an arbitrary but fixed bit pattern.
    llvm::IRBuilder<> Builder(CI);
    auto *poison = llvm::PoisonValue::get(CI->getType());
    auto *frozen = Builder.CreateFreeze(poison);

    CI->replaceAllUsesWith(frozen);
    CI->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

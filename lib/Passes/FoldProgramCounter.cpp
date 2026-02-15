#include "omill/Passes/FoldProgramCounter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

llvm::PreservedAnalyses FoldProgramCounterPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  // Lifted functions have signature (ptr %state, i64 %pc, ptr %mem).
  if (F.arg_size() < 2)
    return llvm::PreservedAnalyses::all();

  auto *pc_arg = F.getArg(1);
  if (!pc_arg->getType()->isIntegerTy(64))
    return llvm::PreservedAnalyses::all();

  uint64_t entry_va = extractEntryVA(F.getName());
  if (entry_va == 0)
    return llvm::PreservedAnalyses::all();

  if (pc_arg->use_empty())
    return llvm::PreservedAnalyses::all();

  auto *constant = llvm::ConstantInt::get(pc_arg->getType(), entry_va);
  pc_arg->replaceAllUsesWith(constant);

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

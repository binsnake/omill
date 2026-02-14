#include "omill/Passes/FoldProgramCounter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>

namespace omill {

namespace {

/// Extract the entry VA from a function name like "sub_140001280" or
/// "sub_140001280.1".  Returns 0 on failure.
uint64_t extractEntryVA(llvm::StringRef name) {
  if (!name.starts_with("sub_"))
    return 0;
  llvm::StringRef hex = name.drop_front(4);
  auto dot = hex.find('.');
  if (dot != llvm::StringRef::npos)
    hex = hex.substr(0, dot);
  uint64_t va = 0;
  if (hex.getAsInteger(16, va))
    return 0;
  return va;
}

}  // namespace

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

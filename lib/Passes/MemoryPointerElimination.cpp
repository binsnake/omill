#include "omill/Passes/MemoryPointerElimination.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Constants.h>

namespace omill {

llvm::PreservedAnalyses MemoryPointerEliminationPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  // The Memory* pointer is the 3rd argument (index 2) of lifted functions.
  // After memory intrinsic lowering, it should have no meaningful uses.
  if (F.arg_size() < 3) {
    return llvm::PreservedAnalyses::all();
  }

  auto *mem_arg = F.getArg(2);

  if (mem_arg->use_empty()) {
    return llvm::PreservedAnalyses::all();
  }

  // Replace all uses with poison — the Memory* has no semantic meaning
  // after memory intrinsics are lowered to native load/store.
  auto *poison = llvm::PoisonValue::get(mem_arg->getType());

  llvm::SmallVector<llvm::Use *, 16> uses_to_replace;
  for (auto &use : mem_arg->uses()) {
    uses_to_replace.push_back(&use);
  }

  for (auto *use : uses_to_replace) {
    use->set(poison);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

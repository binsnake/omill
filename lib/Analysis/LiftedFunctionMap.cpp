#include "omill/Analysis/LiftedFunctionMap.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

llvm::AnalysisKey LiftedFunctionAnalysis::Key;

LiftedFunctionMap LiftedFunctionAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  LiftedFunctionMap result;

  for (auto &F : M) {
    if (!isLiftedFunction(F))
      continue;

    uint64_t pc = extractEntryVA(F.getName());
    if (pc == 0)
      continue;

    result.pc_to_func_[pc] = &F;
    result.lifted_set_.insert(&F);
  }

  return result;
}

}  // namespace omill

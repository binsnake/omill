#include "omill/Analysis/LiftedFunctionMap.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

llvm::AnalysisKey LiftedFunctionAnalysis::Key;

LiftedFunctionMap LiftedFunctionAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  LiftedFunctionMap result;
  result.module_ = &M;

  for (auto &F : M) {
    if (!isLiftedFunction(F))
      continue;

    uint64_t pc = extractEntryVA(F.getName());
    if (pc == 0)
      continue;

    auto name = F.getName().str();
    result.pc_to_name_[pc] = name;
    result.lifted_names_.insert(std::move(name));
  }

  return result;
}

}  // namespace omill

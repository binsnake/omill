#include "omill/Analysis/ExceptionInfo.h"

namespace omill {

llvm::AnalysisKey ExceptionInfoAnalysis::Key;

ExceptionInfoAnalysis::Result ExceptionInfoAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  return std::move(info_);
}

}  // namespace omill

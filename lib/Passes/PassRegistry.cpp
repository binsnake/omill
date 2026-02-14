#include "omill/Passes/PassRegistry.h"

#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/RemillIntrinsicAnalysis.h"

namespace omill {

void registerAnalyses(llvm::FunctionAnalysisManager &FAM) {
  FAM.registerPass([&] { return RemillIntrinsicAnalysis(); });
}

void registerPassBuilderCallbacks(llvm::PassBuilder &PB) {
  PB.registerAnalysisRegistrationCallback(
      [](llvm::FunctionAnalysisManager &FAM) { registerAnalyses(FAM); });
}

}  // namespace omill

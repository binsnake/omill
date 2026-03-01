#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates dead obfuscation trace counters (NEXT_PC phi chains and their
/// select+add feeder instructions) by converting __omill_error_handler calls
/// to unreachable, then running DCE to clean up the now-dead counter chains.
class EliminateDeadTraceCountersPass
    : public llvm::PassInfoMixin<EliminateDeadTraceCountersPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);
};

}  // namespace omill

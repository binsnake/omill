#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates dead stores to any State struct field (not just flags).
///
/// Generalizes DeadStateFlagElimination to all register fields. Identifies
/// stores that are overwritten before the next read. Particularly effective
/// for caller-saved registers that are written then immediately clobbered.
class DeadStateStoreEliminationPass
    : public llvm::PassInfoMixin<DeadStateStoreEliminationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "DeadStateStoreEliminationPass"; }
};

}  // namespace omill

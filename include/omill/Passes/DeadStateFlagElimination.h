#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates dead stores to x86 flag fields in the State struct.
///
/// x86 instructions compute flags (CF, ZF, SF, OF, PF, AF) on nearly
/// every arithmetic operation, but most flag values are never consumed
/// (overwritten by the next ALU op before any conditional reads them).
///
/// This pass identifies flag stores that are overwritten before being
/// read and removes them. Trail of Bits measured ~50% store elimination
/// on real binaries with this technique.
class DeadStateFlagEliminationPass
    : public llvm::PassInfoMixin<DeadStateFlagEliminationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "DeadStateFlagEliminationPass"; }
};

}  // namespace omill

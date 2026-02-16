#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Fallback pass for resolving dispatch_jump targets that RecoverJumpTables
/// misses.  Uses ScalarEvolution and computeKnownBits to bound the index
/// variable, and accepts broader address-decomposition patterns by doing
/// arithmetic evaluation rather than rigid pattern matching.
///
/// Runs after RecoverJumpTables in the iterative target resolution loop.
class SymbolicJumpTableSolverPass
    : public llvm::PassInfoMixin<SymbolicJumpTableSolverPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "SymbolicJumpTableSolverPass"; }
};

}  // namespace omill

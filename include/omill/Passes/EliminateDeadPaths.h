#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates branches whose conditions are provably constant using
/// LLVM's computeKnownBits and algebraic identities (opaque predicates).
///
/// Layered analysis from cheap to expensive:
///   1. KnownBits: if enough bits are known to determine comparison result
///   2. Number-theoretic patterns: (X*(X+1))&1 == 0, X|~X == -1, etc.
///   3. Constant branch folding + dead successor removal
class EliminateDeadPathsPass
    : public llvm::PassInfoMixin<EliminateDeadPathsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "EliminateDeadPathsPass"; }
};

}  // namespace omill

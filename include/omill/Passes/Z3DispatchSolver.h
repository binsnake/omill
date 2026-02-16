#pragma once

#if OMILL_ENABLE_Z3

#include <llvm/IR/PassManager.h>

namespace omill {

/// Constraint-based dispatch resolution using Z3 SMT solving.
///
/// This is the most expensive and most powerful dispatch resolver.  It handles
/// cases where the jump index bound depends on path constraints (branch
/// conditions along the execution path) rather than local bit properties,
/// and where the target computation involves complex arithmetic that SCEV
/// can't model.
///
/// Algorithm (ported from Dna's PreciseJmpTableSolver):
///   1. Find unresolved dispatch_jump calls with non-constant targets.
///   2. Walk the LLVM IR def-use chain to build Z3 bitvector expressions.
///   3. Walk backward through the CFG to collect path constraints.
///   4. Enumerate valid solutions via Z3 SMT solving.
///   5. Build a switch from the valid solutions.
///
/// Runs after SymbolicJumpTableSolver in the iterative resolution loop.
class Z3DispatchSolverPass
    : public llvm::PassInfoMixin<Z3DispatchSolverPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "Z3DispatchSolverPass"; }
};

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

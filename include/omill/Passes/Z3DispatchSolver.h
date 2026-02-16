#pragma once

#if OMILL_ENABLE_SOUPER

#include <llvm/IR/PassManager.h>

namespace omill {

/// Constraint-based dispatch resolution using Souper expression extraction
/// and Z3 SMT solving.
///
/// This is the most expensive and most powerful dispatch resolver.  It handles
/// cases where the jump index bound depends on path constraints (branch
/// conditions along the execution path) rather than local bit properties,
/// and where the target computation involves complex arithmetic that SCEV
/// can't model.
///
/// Algorithm (ported from Dna's PreciseJmpTableSolver):
///   1. Find unresolved dispatch_jump calls with non-constant targets.
///   2. Use Souper ExprBuilder to extract expression DAGs from LLVM IR.
///   3. Walk backward through the CFG to collect path constraints.
///   4. Translate everything to Z3 bitvectors and enumerate solutions.
///   5. Build a switch from the valid solutions.
///   6. If unboundable, recurse on the root-cause variable (depth limit 4).
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

#endif  // OMILL_ENABLE_SOUPER

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

namespace ResolvePhases {
enum : uint32_t {
  ResolveTargets = 1 << 0,   // constant PC -> import/function
  RecoverTables = 1 << 1,    // dispatch_jump + table pattern -> switch
  SymbolicSolve = 1 << 2,    // SCEV/KnownBits fallback
  All = 0xFFFFFFFF,
};
}  // namespace ResolvePhases

/// Consolidated pass that resolves dispatch_call/dispatch_jump targets.
///
/// Phases (controlled by bitmask):
///   ResolveTargets — resolve constant-PC dispatch_call/dispatch_jump to
///     direct calls, branches, or IAT imports.
///   RecoverTables — pattern-match table loads from dispatch_jump and emit
///     LLVM switch instructions.
///   SymbolicSolve — fallback: use ScalarEvolution and KnownBits to bound
///     the table index when pattern matching fails.
///
/// Replaces: ResolveDispatchTargetsPass, RecoverJumpTablesPass,
///           SymbolicJumpTableSolverPass.
class ResolveAndLowerControlFlowPass
    : public llvm::PassInfoMixin<ResolveAndLowerControlFlowPass> {
 public:
  explicit ResolveAndLowerControlFlowPass(
      uint32_t phases = ResolvePhases::All)
      : phases_(phases) {}

  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveAndLowerControlFlowPass"; }

 private:
  uint32_t phases_;
};

}  // namespace omill

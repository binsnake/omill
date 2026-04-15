#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Function pass that splits dispatch_jump/dispatch_call intrinsics whose
/// target PC is a SelectInst or small PHINode into conditional branches
/// with constant-target dispatch calls.
///
/// Handles three patterns:
///   1. dispatch_jump(state, select(cond, A, B), mem) where A, B are
///      ConstantInt → splits into br cond, dispatch_jump(A), dispatch_jump(B)
///   2. PHINode with exactly 2 constant incoming values → same as select
///   3. PHINode with N <= 8 constant incoming values → switch on the PHI
///
/// This pass runs before ResolveAndLowerControlFlowPass so that the
/// now-constant dispatch targets can be resolved normally.
class SplitSelectDispatchPass
    : public llvm::PassInfoMixin<SplitSelectDispatchPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "SplitSelectDispatchPass"; }
};

}  // namespace omill

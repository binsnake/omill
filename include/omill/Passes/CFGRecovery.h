#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Aggressive CFG simplification for remill-lifted code.
///
/// After lowering control flow intrinsics, the CFG contains artifacts
/// from remill's one-basic-block-per-instruction model:
/// - Single-successor chains that should be merged
/// - Branches on constants that should be folded
/// - Unreachable blocks from __remill_error
/// - Empty blocks that just branch to the next block
///
/// This pass aggressively merges and simplifies the CFG.
class CFGRecoveryPass : public llvm::PassInfoMixin<CFGRecoveryPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "CFGRecoveryPass"; }
};

}  // namespace omill

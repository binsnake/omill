#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers __remill_jump to native LLVM branch/switch instructions.
///
/// Constant intra-function target -> br to target basic block
/// Multiple known targets -> switch
/// Dynamic target -> indirectbr or dispatcher
/// Inter-function jump -> tail call
class LowerJumpPass : public llvm::PassInfoMixin<LowerJumpPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerJumpPass"; }
};

}  // namespace omill

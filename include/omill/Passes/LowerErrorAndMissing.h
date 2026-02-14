#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers __remill_error and __remill_missing_block intrinsics.
///
/// __remill_error -> call to __omill_error_handler + unreachable
/// __remill_missing_block -> call to __omill_missing_block_handler + unreachable
class LowerErrorAndMissingPass
    : public llvm::PassInfoMixin<LowerErrorAndMissingPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerErrorAndMissingPass"; }
};

}  // namespace omill

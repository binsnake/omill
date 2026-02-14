#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers __remill_function_return to native LLVM return instructions.
///
/// __remill_function_return(state, pc, mem) -> ret (with state write-back)
class LowerFunctionReturnPass
    : public llvm::PassInfoMixin<LowerFunctionReturnPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerFunctionReturnPass"; }
};

}  // namespace omill

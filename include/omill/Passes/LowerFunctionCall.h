#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers __remill_function_call to native LLVM call instructions.
///
/// __remill_function_call(state, target_pc, mem) with constant target ->
///   direct call to sub_<target_pc>
/// With dynamic target -> indirect call or dispatcher
class LowerFunctionCallPass
    : public llvm::PassInfoMixin<LowerFunctionCallPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerFunctionCallPass"; }
};

}  // namespace omill

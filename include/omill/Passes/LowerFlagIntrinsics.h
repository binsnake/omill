#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers remill flag computation and comparison intrinsics.
///
/// __remill_flag_computation_*(result, ...) -> result (first arg)
/// __remill_compare_*(result) -> result (first arg)
///
/// These intrinsics wrap the computed flag/comparison value as the first
/// argument, with additional operands for tracing. Lowering simply replaces
/// the call with its first argument, exposing the flag as an SSA value.
class LowerFlagIntrinsicsPass
    : public llvm::PassInfoMixin<LowerFlagIntrinsicsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerFlagIntrinsicsPass"; }
};

}  // namespace omill

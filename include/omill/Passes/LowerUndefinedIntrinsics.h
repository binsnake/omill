#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers remill undefined value intrinsics.
///
/// __remill_undefined_N() -> freeze(poison) of matching type
///
/// This pass should run LATE in the pipeline — after dead code elimination
/// has removed most undefined values that were never actually used.
/// We use freeze(poison) rather than undef to avoid undefined behavior
/// propagation while still allowing LLVM to optimize.
class LowerUndefinedIntrinsicsPass
    : public llvm::PassInfoMixin<LowerUndefinedIntrinsicsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerUndefinedIntrinsicsPass"; }
};

}  // namespace omill

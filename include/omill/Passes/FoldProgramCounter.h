#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Replaces all uses of the function's second argument (program_counter)
/// with a constant derived from the function name (sub_<hex>).
///
/// This must run before ABI recovery, which eliminates program_counter
/// as a non-ABI parameter.  Without this substitution, program_counter
/// becomes 0 and all RIP-relative address computations break.
class FoldProgramCounterPass
    : public llvm::PassInfoMixin<FoldProgramCounterPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "FoldProgramCounterPass"; }
};

}  // namespace omill

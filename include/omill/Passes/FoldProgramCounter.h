#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Replaces safe address-only uses of the function's second argument
/// (program_counter) with a constant derived from the function name
/// (sub_<hex>).
///
/// This must run before ABI recovery, which eliminates program_counter
/// as a non-ABI parameter.  Without this substitution, program_counter
/// becomes 0 and all RIP-relative address computations break.
///
/// Set `OMILL_SKIP_FOLD_PC=1` to disable this pass for diagnostics.
class FoldProgramCounterPass
    : public llvm::PassInfoMixin<FoldProgramCounterPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "FoldProgramCounterPass"; }
};

}  // namespace omill

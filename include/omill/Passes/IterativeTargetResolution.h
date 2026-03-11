#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Module pass that iteratively alternates dispatch target resolution
/// with LLVM optimization until a fixpoint is reached (no more dispatches
/// are resolved) or a maximum iteration count is hit.
///
/// Each iteration runs:
///   ResolveDispatchTargets → LowerResolvedDispatchCalls →
///   InstCombine → GVN → SimplifyCFG → ConstantMemoryFolding → InstCombine
///
/// This catches targets that only become constant after optimization,
/// such as obfuscated arithmetic (xor/add of constants loaded from binary
/// memory) or chained indirect references.
class IterativeTargetResolutionPass
    : public llvm::PassInfoMixin<IterativeTargetResolutionPass> {
 public:
  explicit IterativeTargetResolutionPass(unsigned max_iterations = 32,
                                         bool run_ipcp_inside_resolution = true)
      : max_iterations_(max_iterations),
        run_ipcp_inside_resolution_(run_ipcp_inside_resolution) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);

  static llvm::StringRef name() { return "IterativeTargetResolutionPass"; }

 private:
  unsigned max_iterations_;
  bool run_ipcp_inside_resolution_;
};

}  // namespace omill

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves remill trace stubs (sub_XXX declares) to their defined
/// implementations (sub_XXX.N defines) and inlines callee traces that
/// exit via __remill_jump into their callers.
///
/// This creates a single merged function where the caller and all its
/// jump-exiting callees share the same CFG, enabling the jump targets
/// to be resolved as intra-function branches (br selector pattern).
///
/// Must run BEFORE state optimization so that the optimizer sees the
/// full function body.
class InlineJumpTargetsPass
    : public llvm::PassInfoMixin<InlineJumpTargetsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);
};

}  // namespace omill

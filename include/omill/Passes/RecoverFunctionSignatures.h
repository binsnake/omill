#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recovers native function signatures from lifted functions.
///
/// After calling convention analysis determines which State fields are
/// parameters and return values, this pass:
/// 1. Creates new function declarations with native signatures
/// 2. Builds wrapper bodies that marshal between State-based and native ABI
/// 3. Rewrites call sites to use the new signatures
///
/// This is a module pass because it needs cross-function information
/// (calling convention analysis results) and modifies function signatures.
class RecoverFunctionSignaturesPass
    : public llvm::PassInfoMixin<RecoverFunctionSignaturesPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "RecoverFunctionSignaturesPass"; }
};

}  // namespace omill

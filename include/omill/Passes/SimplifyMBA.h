#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Simplifies MBA (Mixed Boolean-Arithmetic) obfuscated expressions using
/// equality saturation.  Translates integer expression trees to the EqSat
/// AST, simplifies via ContextRecursiveSimplify, and reconstructs.
class SimplifyMBAPass : public llvm::PassInfoMixin<SimplifyMBAPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "SimplifyMBAPass"; }
};

}  // namespace omill

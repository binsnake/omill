#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recovers global string constants from inttoptr(constant) patterns.
///
/// When an inttoptr instruction uses a constant address that points to
/// a valid ASCII or UTF-16LE string in the BinaryMemoryMap, this pass
/// creates a global constant and replaces the inttoptr with a reference
/// to it.
///
/// Requires BinaryMemoryAnalysis to be cached.
class RecoverGlobalTypesPass
    : public llvm::PassInfoMixin<RecoverGlobalTypesPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "RecoverGlobalTypesPass"; }
};

}  // namespace omill

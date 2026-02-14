#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Final ABI recovery pass: removes the State struct pointer from function
/// signatures entirely.
///
/// After RecoverFunctionSignatures has created native-ABI wrappers,
/// remaining State accesses in functions that weren't fully recovered
/// are converted to local allocas. Functions that were fully recovered
/// have their State parameter removed.
///
/// This is a module pass because it rewrites function signatures and
/// updates all call sites.
class EliminateStateStructPass
    : public llvm::PassInfoMixin<EliminateStateStructPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "EliminateStateStructPass"; }
};

}  // namespace omill

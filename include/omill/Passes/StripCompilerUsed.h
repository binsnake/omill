#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Strips @llvm.compiler.used so that GlobalDCE can remove dead ISEL stubs.
class StripCompilerUsedPass
    : public llvm::PassInfoMixin<StripCompilerUsedPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);
};

}  // namespace omill

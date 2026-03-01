#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

class ExpandI128DivRemPass
    : public llvm::PassInfoMixin<ExpandI128DivRemPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);
};

}  // namespace omill

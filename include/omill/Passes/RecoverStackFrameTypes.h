#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recovers typed struct layouts from [N x i8] stack frame allocas.
///
/// After RecoverStackFramePass creates byte-array allocas, this pass
/// analyzes constant-offset GEP users to determine access patterns
/// (offset + type) and builds a StructType with appropriate fields
/// and padding. The alloca is then retyped and GEPs are rewritten
/// to use struct field indices.
class RecoverStackFrameTypesPass
    : public llvm::PassInfoMixin<RecoverStackFrameTypesPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "RecoverStackFrameTypesPass"; }
};

}  // namespace omill

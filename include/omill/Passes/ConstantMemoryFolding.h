#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Replaces loads from constant addresses (within mapped binary regions)
/// with actual constant values. This naturally enables xorstr recovery:
/// after folding, `xor const1, const2` is simplified to plaintext by
/// InstCombine.
class ConstantMemoryFoldingPass
    : public llvm::PassInfoMixin<ConstantMemoryFoldingPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ConstantMemoryFoldingPass"; }
};

}  // namespace omill

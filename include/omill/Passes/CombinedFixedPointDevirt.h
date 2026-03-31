#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// A devirtualization-oriented fixed-point pass that keeps three tightly
/// coupled transforms in one local loop:
/// 1. lightweight store-to-load forwarding for exact same-address reloads
/// 2. binary-section/Remill load concretization via ConstantMemoryFolding
/// 3. instruction simplification / local constant propagation
///
/// This is intentionally narrower than a full LLVM optimization pipeline.
/// Its purpose is to reduce phase-ordering issues in iterative discovery and
/// late devirtualization cleanup, where newly concretized values should
/// immediately participate in later simplification within the same round.
class CombinedFixedPointDevirtPass
    : public llvm::PassInfoMixin<CombinedFixedPointDevirtPass> {
 public:
  explicit CombinedFixedPointDevirtPass(unsigned max_rounds = 8)
      : max_rounds_(max_rounds) {}

  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "CombinedFixedPointDevirtPass"; }

 private:
  unsigned max_rounds_ = 8;
};

}  // namespace omill

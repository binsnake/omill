#pragma once

#include <llvm/IR/PassManager.h>

#include <cstdint>

namespace omill {

/// Module pass that iteratively optimizes block-functions, scans for
/// newly-resolvable dispatch targets, lifts the discovered blocks, and
/// repeats until a fixed point or an iteration limit is reached.
///
/// This pass is the core of the blocks-as-functions architecture: after
/// BlockLifter produces one function per basic block (with indirect
/// jumps represented as unresolved dispatch jump/call intrinsics),
/// IterativeBlockDiscovery runs lightweight per-function optimization
/// (InstCombine + ConstantMemoryFolding) and then scans all dispatch
/// call sites for constant PC arguments.  Newly discovered PCs are
/// lifted by BlockLifter, the optimization is re-run, and the cycle
/// continues.
///
/// Requires OMILL_ENABLE_REMILL — the pass calls BlockLifter internally.
class IterativeBlockDiscoveryPass
    : public llvm::PassInfoMixin<IterativeBlockDiscoveryPass> {
 public:
  explicit IterativeBlockDiscoveryPass(unsigned max_iterations = 10)
      : max_iterations_(max_iterations) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);

  static llvm::StringRef name() { return "IterativeBlockDiscoveryPass"; }

 private:
  unsigned max_iterations_;
};

}  // namespace omill

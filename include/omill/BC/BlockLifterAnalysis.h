#pragma once

#include <llvm/IR/PassManager.h>

#include <functional>
#include <memory>

namespace omill {

class BlockLifter;
class BlockManager;

/// Callback type that lifts a block at a given PC and returns the successors.
/// This is the interface between the IterativeBlockDiscoveryPass and the
/// actual BlockLifter.  The callback is invoked with a PC to lift; it
/// returns true if the block was successfully lifted (or already existed).
using BlockLiftCallback = std::function<bool(uint64_t pc)>;

/// Callback to inject synthetic code bytes at a given PC, making them
/// readable by the block lifter's TryReadExecutableByte.
using AddCodeCallback = std::function<void(uint64_t pc, const uint8_t *data,
                                           size_t size)>;

/// Module-level analysis that provides a block-lifting callback.
///
/// The consumer (e.g. omill-lift main.cpp) registers this analysis with
/// a pre-built callback that wraps BlockLifter::LiftBlock.  If not
/// registered, IterativeBlockDiscoveryPass skips the lift-new-blocks step
/// and only resolves dispatches to existing block-functions.
///
/// This decouples the pass from remill: the pass itself is pure LLVM IR
/// manipulation; only the callback (registered externally) touches remill.
class BlockLiftAnalysis
    : public llvm::AnalysisInfoMixin<BlockLiftAnalysis> {
  friend llvm::AnalysisInfoMixin<BlockLiftAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  struct Result {
    BlockLiftCallback lift_block;
    AddCodeCallback add_code;

    /// LLVM analysis invalidation — the callback is always valid.
    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      return false;
    }
  };

  BlockLiftAnalysis() = default;

  explicit BlockLiftAnalysis(BlockLiftCallback cb,
                             AddCodeCallback add_code = nullptr)
      : callback_(std::move(cb)), add_code_(std::move(add_code)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    return {callback_, add_code_};
  }

 private:
  BlockLiftCallback callback_;
  AddCodeCallback add_code_;
};

}  // namespace omill

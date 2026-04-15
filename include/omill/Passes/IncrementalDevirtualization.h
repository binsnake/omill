#pragma once

#include <llvm/IR/PassManager.h>

#include <cstdint>

namespace omill {

struct SessionGraphState;

/// Unified incremental devirtualization pass that combines
/// IterativeBlockDiscovery and VirtualCFGMaterialization into a single
/// fixpoint loop.
///
/// Each round:
///   A. IterativeBlockDiscovery: optimize → scan → lift → resolve (with
///      JumpTableConcretizer and IPCP affine pass-through)
///   B. VirtualCFGMaterialization: rebuild VirtualMachineModel → refine
///      RegisterRoleMap → materialize VM frontier edges → lift targets
///
/// The loop continues until neither phase makes progress or the iteration
/// limit is reached.  This eliminates the gap where IterativeBlockDiscovery
/// stalls on targets only resolvable with VM model knowledge, and where
/// VirtualCFGMaterialization misses targets that IPCP could resolve.
///
/// Used when both `--use-block-lifting` and `--generic-static-devirtualize`
/// are active.
class IncrementalDevirtualizationPass
    : public llvm::PassInfoMixin<IncrementalDevirtualizationPass> {
 public:
  explicit IncrementalDevirtualizationPass(
      const SessionGraphState *session_graph = nullptr,
      unsigned max_outer_rounds = 8)
      : session_graph_(session_graph),
        max_outer_rounds_(max_outer_rounds) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);

  static llvm::StringRef name() { return "IncrementalDevirtualizationPass"; }

 private:
  const SessionGraphState *session_graph_ = nullptr;
  unsigned max_outer_rounds_;
};

}  // namespace omill

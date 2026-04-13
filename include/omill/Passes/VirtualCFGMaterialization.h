#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

struct SessionGraphState;

/// Generic static-devirtualization pass that consumes VirtualMachineModel
/// summaries and lowers proven constant virtual dispatches to direct CFG edges.
///
/// This is intentionally VM-agnostic: it only relies on the generic symbolic
/// slot facts recovered by VirtualMachineModelAnalysis.
class VirtualCFGMaterializationPass
    : public llvm::PassInfoMixin<VirtualCFGMaterializationPass> {
 public:
  explicit VirtualCFGMaterializationPass(
      const SessionGraphState *session_graph = nullptr)
      : session_graph_(session_graph) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);

  static llvm::StringRef name() { return "VirtualCFGMaterializationPass"; }

 private:
  const SessionGraphState *session_graph_ = nullptr;
};

/// Validation wrapper for VirtualCFGMaterializationPass.
/// When Z3-backed semantic validation is available, this snapshots affected
/// functions, runs the materialization rewrite, and verifies the resulting
/// functions are semantically equivalent to their pre-rewrite form.
class VerifiedVirtualCFGMaterializationPass
    : public llvm::PassInfoMixin<VerifiedVirtualCFGMaterializationPass> {
 public:
  explicit VerifiedVirtualCFGMaterializationPass(
      const SessionGraphState *session_graph = nullptr)
      : session_graph_(session_graph) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);

  static llvm::StringRef name() {
    return "VerifiedVirtualCFGMaterializationPass";
  }

 private:
  const SessionGraphState *session_graph_ = nullptr;
};

}  // namespace omill

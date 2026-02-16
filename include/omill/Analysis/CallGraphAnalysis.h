#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>

namespace llvm {
class CallInst;
class Function;
class Module;
}  // namespace llvm

namespace omill {

/// Describes a single call site in the lifted call graph.
struct CallSite {
  llvm::CallInst *inst;
  llvm::Function *caller;
  llvm::Function *callee;  // nullptr if unresolved
  uint64_t target_pc;      // 0 if dynamic
  bool is_tail_call;
  bool is_dispatch;  // still __omill_dispatch_{call,jump}
};

/// A node in the lifted call graph representing one function.
struct CallGraphNode {
  llvm::Function *func;
  llvm::SmallVector<CallSite, 4> callees;      // outgoing edges
  llvm::SmallVector<CallSite *, 8> callers;     // incoming (ptrs into other nodes)
  unsigned unresolved_count = 0;
};

/// Module-level call graph built from lifted functions.
///
/// Edges are derived from:
/// - Direct calls to sub_* functions
/// - __omill_dispatch_call with constant target resolved via LiftedFunctionMap
/// - musttail calls (tail-call edges)
/// - Dynamic/unresolved dispatch targets
///
/// Also computes SCCs in bottom-up order for use by inter-procedural passes.
class LiftedCallGraph {
 public:
  /// Look up the call graph node for a function.
  CallGraphNode *getNode(const llvm::Function *F) {
    auto it = nodes_.find(F);
    return it != nodes_.end() ? &it->second : nullptr;
  }

  const CallGraphNode *getNode(const llvm::Function *F) const {
    auto it = nodes_.find(F);
    return it != nodes_.end() ? &it->second : nullptr;
  }

  /// SCCs in bottom-up order (leaves first).
  const llvm::SmallVector<llvm::SmallVector<llvm::Function *, 4>, 16> &
  getBottomUpSCCs() const {
    return sccs_;
  }

  /// Total number of unresolved call sites across all functions.
  unsigned totalUnresolved() const { return total_unresolved_; }

  /// Number of nodes in the graph.
  size_t size() const { return nodes_.size(); }

  /// Always recomputed — never cached across invalidation.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return true;
  }

 private:
  friend class CallGraphAnalysis;
  llvm::DenseMap<const llvm::Function *, CallGraphNode> nodes_;
  llvm::SmallVector<llvm::SmallVector<llvm::Function *, 4>, 16> sccs_;
  unsigned total_unresolved_ = 0;
};

/// Module analysis that builds a LiftedCallGraph.
class CallGraphAnalysis
    : public llvm::AnalysisInfoMixin<CallGraphAnalysis> {
  friend llvm::AnalysisInfoMixin<CallGraphAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = LiftedCallGraph;

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

}  // namespace omill

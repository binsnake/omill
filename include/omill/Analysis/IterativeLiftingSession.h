#pragma once

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "omill/Analysis/BinaryRegion.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/BC/TraceLiftAnalysis.h"

namespace llvm {
class Module;
}

namespace omill {

enum class LiftEdgeKind {
  kDirectBranch,
  kDirectCall,
  kIndirectBranch,
  kIndirectCall,
  kReturn,
  kVmTrace,
};

struct LiftNode {
  uint64_t pc = 0;
  bool lifted = false;
  bool merged = false;
  bool dirty = true;
};

struct LiftEdge {
  LiftEdgeKind kind = LiftEdgeKind::kIndirectBranch;
  std::string edge_identity;
  uint64_t source_pc = 0;
  uint64_t target_pc = 0;
  std::optional<uint64_t> effective_target_pc;
  std::optional<uint64_t> canonical_owner_pc;
  bool resolved = false;
  bool native_boundary = false;
  EdgeResolutionStatus resolution_status = EdgeResolutionStatus::kUnknown;
  EdgeRestatementKind restatement_kind = EdgeRestatementKind::kUnknown;
  std::vector<LearnedOutgoingEdge> learned_outgoing_edges;
  std::optional<std::string> binary_region_snapshot_key;
};

struct IterativeRoundSummary {
  std::string pipeline;
  unsigned iteration = 0;
  unsigned dirty_functions = 0;
  unsigned dirty_functions_after = 0;
  unsigned affected_functions = 0;
  unsigned optimized_functions = 0;
  unsigned unresolved_before = 0;
  unsigned unresolved_after = 0;
  unsigned new_targets = 0;
  unsigned pending_targets = 0;
  unsigned dynamic_unresolved = 0;
  unsigned missing_targets = 0;
  unsigned blocked_unresolved = 0;
  uint64_t total_ms = 0;
  uint64_t optimize_ms = 0;
  uint64_t resolve_ms = 0;
  uint64_t ipcp_ms = 0;
  uint64_t lift_ms = 0;
  uint64_t lower_ms = 0;
  uint64_t inline_ms = 0;
  uint64_t reverse_inline_ms = 0;
  bool ipcp_changed = false;
  bool lifted_new = false;
  bool stalled = false;
};

struct VirtualContextSummary {
  llvm::DenseSet<unsigned> live_ins;
  llvm::DenseSet<unsigned> live_outs;
  llvm::DenseSet<unsigned> killed_slots;
  llvm::DenseSet<unsigned> escaped_slots;
  llvm::DenseMap<unsigned, uint64_t> constant_slots;
};

class LiftGraph {
 public:
  LiftNode &getOrCreateNode(uint64_t pc);
  const LiftNode *lookupNode(uint64_t pc) const;

  LiftEdge &addOrUpdateEdge(const LiftEdge &edge);
  void syncOutgoingEdges(uint64_t source_pc, llvm::ArrayRef<LiftEdge> edges);
  void recordLearnedOutgoingEdges(
      uint64_t source_pc, llvm::ArrayRef<LearnedOutgoingEdge> edges,
      EdgeResolutionStatus resolution_status,
      EdgeRestatementKind restatement_kind,
      std::optional<std::string> snapshot_key = std::nullopt);
  llvm::ArrayRef<LiftEdge> edges() const { return edges_; }
  llvm::SmallVector<const LiftEdge *, 4> outgoingEdges(uint64_t source_pc) const;
  llvm::SmallVector<const LiftEdge *, 8> unresolvedEdges() const;
  size_t unresolvedEdgeCount() const;

  void markDirty(uint64_t pc);
  void clearDirty(uint64_t pc);
  bool isDirty(uint64_t pc) const;
  llvm::SmallVector<uint64_t, 8> dirtyNodes() const;

  size_t nodeCount() const { return nodes_.size(); }
  size_t edgeCount() const { return edges_.size(); }

 private:
  llvm::DenseMap<uint64_t, LiftNode> nodes_;
  llvm::SmallVector<LiftEdge, 16> edges_;
  llvm::DenseSet<uint64_t> dirty_nodes_;
};

class IterativeLiftingSession {
 public:
  explicit IterativeLiftingSession(std::string name = "default");

  llvm::StringRef name() const { return name_; }

  LiftGraph &graph() { return graph_; }
  const LiftGraph &graph() const { return graph_; }

  void setBlockLiftingEnabled(bool enabled) { use_block_lifting_ = enabled; }
  bool useBlockLifting() const { return use_block_lifting_; }

  void setTraceLiftCallback(TraceLiftCallback callback) {
    trace_lift_callback_ = std::move(callback);
  }
  void setBlockLiftCallback(BlockLiftCallback callback) {
    block_lift_callback_ = std::move(callback);
  }

  const TraceLiftCallback &traceLiftCallback() const {
    return trace_lift_callback_;
  }
  const BlockLiftCallback &blockLiftCallback() const {
    return block_lift_callback_;
  }

  void queueTarget(uint64_t pc);
  std::optional<uint64_t> popPendingTarget();
  bool hasPendingTargets() const { return !pending_targets_.empty(); }
  size_t pendingTargetCount() const { return pending_targets_.size(); }

  bool noteLiftedTarget(uint64_t pc, bool merged = false);

  VirtualContextSummary &summaryFor(uint64_t pc);
  const VirtualContextSummary *lookupSummary(uint64_t pc) const;
  void recordBinaryRegionSnapshot(BinaryRegionSnapshot snapshot);
  const BinaryRegionSnapshot *lookupBinaryRegionSnapshot(
      llvm::StringRef snapshot_key) const;

  void clearRoundSummaries();
  void recordRoundSummary(IterativeRoundSummary summary);
  llvm::ArrayRef<IterativeRoundSummary> roundSummaries() const {
    return round_summaries_;
  }

 private:
  std::string name_;
  bool use_block_lifting_ = false;
  LiftGraph graph_;
  llvm::DenseSet<uint64_t> queued_targets_;
  llvm::SmallVector<uint64_t, 16> pending_targets_;
  llvm::DenseMap<uint64_t, VirtualContextSummary> summaries_;
  std::map<std::string, BinaryRegionSnapshot> binary_region_snapshots_;
  llvm::SmallVector<IterativeRoundSummary, 16> round_summaries_;
  TraceLiftCallback trace_lift_callback_;
  BlockLiftCallback block_lift_callback_;
};

class IterativeLiftingSessionAnalysis
    : public llvm::AnalysisInfoMixin<IterativeLiftingSessionAnalysis> {
  friend llvm::AnalysisInfoMixin<IterativeLiftingSessionAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  struct Result {
    std::shared_ptr<IterativeLiftingSession> session;

    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      return false;
    }
  };

  IterativeLiftingSessionAnalysis() = default;

  explicit IterativeLiftingSessionAnalysis(
      std::shared_ptr<IterativeLiftingSession> session)
      : session_(std::move(session)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);

 private:
  std::shared_ptr<IterativeLiftingSession> session_;
};

}  // namespace omill

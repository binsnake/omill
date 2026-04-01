#include "omill/Analysis/IterativeLiftingSession.h"

#include <llvm/ADT/StringExtras.h>

#include <utility>

namespace omill {

llvm::AnalysisKey IterativeLiftingSessionAnalysis::Key;

namespace {

bool sameEdge(const LiftEdge &lhs, const LiftEdge &rhs) {
  return lhs.kind == rhs.kind && lhs.source_pc == rhs.source_pc &&
         lhs.target_pc == rhs.target_pc &&
         lhs.effective_target_pc == rhs.effective_target_pc &&
         lhs.canonical_owner_pc == rhs.canonical_owner_pc &&
         lhs.resolved == rhs.resolved &&
         lhs.native_boundary == rhs.native_boundary &&
         lhs.resolution_status == rhs.resolution_status &&
         lhs.restatement_kind == rhs.restatement_kind &&
         lhs.learned_outgoing_edges == rhs.learned_outgoing_edges &&
         lhs.binary_region_snapshot_key == rhs.binary_region_snapshot_key;
}

}  // namespace

LiftNode &LiftGraph::getOrCreateNode(uint64_t pc) {
  auto [it, inserted] = nodes_.try_emplace(pc, LiftNode{pc, false, false, true});
  if (inserted)
    dirty_nodes_.insert(pc);
  return it->second;
}

const LiftNode *LiftGraph::lookupNode(uint64_t pc) const {
  auto it = nodes_.find(pc);
  return (it != nodes_.end()) ? &it->second : nullptr;
}

LiftEdge &LiftGraph::addOrUpdateEdge(const LiftEdge &edge) {
  for (auto &existing : edges_) {
    if (existing.kind != edge.kind || existing.source_pc != edge.source_pc ||
        existing.target_pc != edge.target_pc) {
      continue;
    }
    bool changed = false;
    if (edge.resolved && !existing.resolved) {
      existing.resolved = true;
      changed = true;
    }
    if (edge.native_boundary && !existing.native_boundary) {
      existing.native_boundary = true;
      changed = true;
    }
    if (edge.effective_target_pc && existing.effective_target_pc != edge.effective_target_pc) {
      existing.effective_target_pc = edge.effective_target_pc;
      changed = true;
    }
    if (edge.canonical_owner_pc &&
        existing.canonical_owner_pc != edge.canonical_owner_pc) {
      existing.canonical_owner_pc = edge.canonical_owner_pc;
      changed = true;
    }
    if (edge.resolution_status != EdgeResolutionStatus::kUnknown &&
        existing.resolution_status != edge.resolution_status) {
      existing.resolution_status = edge.resolution_status;
      changed = true;
    }
    if (edge.restatement_kind != EdgeRestatementKind::kUnknown &&
        existing.restatement_kind != edge.restatement_kind) {
      existing.restatement_kind = edge.restatement_kind;
      changed = true;
    }
    if (!edge.learned_outgoing_edges.empty() &&
        existing.learned_outgoing_edges != edge.learned_outgoing_edges) {
      existing.learned_outgoing_edges = edge.learned_outgoing_edges;
      changed = true;
    }
    if (edge.binary_region_snapshot_key &&
        existing.binary_region_snapshot_key != edge.binary_region_snapshot_key) {
      existing.binary_region_snapshot_key = edge.binary_region_snapshot_key;
      changed = true;
    }
    if (!edge.edge_identity.empty() && existing.edge_identity.empty()) {
      existing.edge_identity = edge.edge_identity;
      changed = true;
    }
    if (changed)
      markDirty(edge.source_pc);
    if (edge.target_pc != 0)
      getOrCreateNode(edge.target_pc);
    return existing;
  }

  getOrCreateNode(edge.source_pc);
  if (edge.target_pc != 0)
    getOrCreateNode(edge.target_pc);
  edges_.push_back(edge);
  markDirty(edge.source_pc);
  return edges_.back();
}

void LiftGraph::syncOutgoingEdges(uint64_t source_pc,
                                  llvm::ArrayRef<LiftEdge> new_edges) {
  getOrCreateNode(source_pc);

  llvm::SmallVector<LiftEdge, 16> normalized;
  normalized.reserve(new_edges.size());
  for (const auto &edge : new_edges) {
    LiftEdge normalized_edge = edge;
    normalized_edge.source_pc = source_pc;
    normalized.push_back(normalized_edge);
    if (normalized_edge.target_pc != 0)
      getOrCreateNode(normalized_edge.target_pc);
  }

  llvm::SmallVector<LiftEdge, 16> existing;
  existing.reserve(edges_.size());
  for (const auto &edge : edges_) {
    if (edge.source_pc == source_pc)
      existing.push_back(edge);
  }

  bool changed = existing.size() != normalized.size();
  if (!changed) {
    for (const auto &edge : existing) {
      bool matched = false;
      for (const auto &candidate : normalized) {
        if (sameEdge(edge, candidate)) {
          matched = true;
          break;
        }
      }
      if (!matched) {
        changed = true;
        break;
      }
    }
  }

  if (!changed)
    return;

  llvm::SmallVector<LiftEdge, 16> rebuilt;
  rebuilt.reserve(edges_.size() - existing.size() + normalized.size());
  for (const auto &edge : edges_) {
    if (edge.source_pc != source_pc)
      rebuilt.push_back(edge);
  }
  rebuilt.append(normalized.begin(), normalized.end());
  edges_.swap(rebuilt);
  markDirty(source_pc);
}

void LiftGraph::recordLearnedOutgoingEdges(
    uint64_t source_pc, llvm::ArrayRef<LearnedOutgoingEdge> edges,
    EdgeResolutionStatus resolution_status,
    EdgeRestatementKind restatement_kind,
    std::optional<std::string> snapshot_key) {
  llvm::SmallVector<LiftEdge, 8> lifted_edges;
  lifted_edges.reserve(edges.size());
  for (const auto &edge : edges) {
    LiftEdge lifted_edge;
    lifted_edge.source_pc = source_pc;
    lifted_edge.target_pc = edge.target_pc.value_or(0);
    lifted_edge.effective_target_pc = edge.target_pc;
    lifted_edge.resolved = edge.resolution_status == EdgeResolutionStatus::kResolved ||
                           edge.resolution_status == EdgeResolutionStatus::kBoundary ||
                           edge.resolution_status == EdgeResolutionStatus::kTerminal;
    lifted_edge.native_boundary = edge.is_boundary;
    lifted_edge.resolution_status = edge.resolution_status;
    lifted_edge.restatement_kind = edge.restatement_kind;
    lifted_edge.learned_outgoing_edges = {edge};
    lifted_edge.binary_region_snapshot_key = snapshot_key;
    if (edge.is_boundary) {
      lifted_edge.kind = LiftEdgeKind::kIndirectCall;
    } else if (edge.is_terminal) {
      lifted_edge.kind = LiftEdgeKind::kReturn;
    } else if (edge.is_unresolved_indirect) {
      lifted_edge.kind = LiftEdgeKind::kIndirectBranch;
    } else {
      lifted_edge.kind = LiftEdgeKind::kDirectBranch;
    }
    lifted_edges.push_back(std::move(lifted_edge));
  }

  if (lifted_edges.empty()) {
    LiftEdge marker;
    marker.kind = LiftEdgeKind::kIndirectBranch;
    marker.source_pc = source_pc;
    marker.target_pc = 0;
    marker.resolution_status = resolution_status;
    marker.restatement_kind = restatement_kind;
    marker.binary_region_snapshot_key = std::move(snapshot_key);
    addOrUpdateEdge(marker);
    return;
  }

  syncOutgoingEdges(source_pc, lifted_edges);
}

llvm::SmallVector<const LiftEdge *, 4> LiftGraph::outgoingEdges(
    uint64_t source_pc) const {
  llvm::SmallVector<const LiftEdge *, 4> result;
  for (const auto &edge : edges_) {
    if (edge.source_pc == source_pc)
      result.push_back(&edge);
  }
  return result;
}

llvm::SmallVector<const LiftEdge *, 8> LiftGraph::unresolvedEdges() const {
  llvm::SmallVector<const LiftEdge *, 8> result;
  for (const auto &edge : edges_) {
    if (!edge.resolved)
      result.push_back(&edge);
  }
  return result;
}

size_t LiftGraph::unresolvedEdgeCount() const {
  size_t count = 0;
  for (const auto &edge : edges_) {
    if (!edge.resolved)
      ++count;
  }
  return count;
}

void LiftGraph::markDirty(uint64_t pc) {
  auto &node = getOrCreateNode(pc);
  node.dirty = true;
  dirty_nodes_.insert(pc);
}

void LiftGraph::clearDirty(uint64_t pc) {
  auto it = nodes_.find(pc);
  if (it == nodes_.end())
    return;
  it->second.dirty = false;
  dirty_nodes_.erase(pc);
}

bool LiftGraph::isDirty(uint64_t pc) const {
  return dirty_nodes_.contains(pc);
}

llvm::SmallVector<uint64_t, 8> LiftGraph::dirtyNodes() const {
  llvm::SmallVector<uint64_t, 8> result;
  result.reserve(dirty_nodes_.size());
  for (uint64_t pc : dirty_nodes_)
    result.push_back(pc);
  return result;
}

IterativeLiftingSession::IterativeLiftingSession(std::string name)
    : name_(std::move(name)) {}

void IterativeLiftingSession::queueTarget(uint64_t pc) {
  if (pc == 0 || !queued_targets_.insert(pc).second)
    return;
  pending_targets_.push_back(pc);
  graph_.getOrCreateNode(pc);
}

std::optional<uint64_t> IterativeLiftingSession::popPendingTarget() {
  if (pending_targets_.empty())
    return std::nullopt;
  uint64_t pc = pending_targets_.front();
  pending_targets_.erase(pending_targets_.begin());
  return pc;
}

bool IterativeLiftingSession::noteLiftedTarget(uint64_t pc, bool merged) {
  if (pc == 0)
    return false;
  auto &node = graph_.getOrCreateNode(pc);
  bool changed = !node.lifted || (merged && !node.merged);
  node.lifted = true;
  node.merged = node.merged || merged;
  if (changed)
    graph_.markDirty(pc);
  return changed;
}

VirtualContextSummary &IterativeLiftingSession::summaryFor(uint64_t pc) {
  graph_.getOrCreateNode(pc);
  return summaries_[pc];
}

const VirtualContextSummary *IterativeLiftingSession::lookupSummary(
    uint64_t pc) const {
  auto it = summaries_.find(pc);
  return (it != summaries_.end()) ? &it->second : nullptr;
}

void IterativeLiftingSession::recordBinaryRegionSnapshot(
    BinaryRegionSnapshot snapshot) {
  if (snapshot.snapshot_key.empty()) {
    snapshot.snapshot_key = "region:" + llvm::utohexstr(snapshot.entry_pc);
  }
  for (const auto &[block_pc, block] : snapshot.blocks_by_pc) {
    graph_.recordLearnedOutgoingEdges(block_pc, block.outgoing_edges,
                                      snapshot.closure_kind ==
                                              BinaryRegionClosureKind::kClosed
                                          ? EdgeResolutionStatus::kResolved
                                          : EdgeResolutionStatus::kUnresolved,
                                      EdgeRestatementKind::kProofSupplied,
                                      snapshot.snapshot_key);
  }
  binary_region_snapshots_[snapshot.snapshot_key] = std::move(snapshot);
}

const BinaryRegionSnapshot *IterativeLiftingSession::lookupBinaryRegionSnapshot(
    llvm::StringRef snapshot_key) const {
  auto it = binary_region_snapshots_.find(snapshot_key.str());
  return (it != binary_region_snapshots_.end()) ? &it->second : nullptr;
}

void IterativeLiftingSession::clearRoundSummaries() {
  round_summaries_.clear();
}

void IterativeLiftingSession::recordRoundSummary(IterativeRoundSummary summary) {
  round_summaries_.push_back(std::move(summary));
}

IterativeLiftingSessionAnalysis::Result IterativeLiftingSessionAnalysis::run(
    llvm::Module &, llvm::ModuleAnalysisManager &) {
  if (!session_)
    session_ = std::make_shared<IterativeLiftingSession>();
  return {session_};
}

}  // namespace omill

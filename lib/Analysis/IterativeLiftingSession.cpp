#include "omill/Analysis/IterativeLiftingSession.h"

#include <utility>

namespace omill {

llvm::AnalysisKey IterativeLiftingSessionAnalysis::Key;

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
    existing.resolved = existing.resolved || edge.resolved;
    existing.native_boundary = existing.native_boundary || edge.native_boundary;
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

llvm::SmallVector<const LiftEdge *, 4> LiftGraph::outgoingEdges(
    uint64_t source_pc) const {
  llvm::SmallVector<const LiftEdge *, 4> result;
  for (const auto &edge : edges_) {
    if (edge.source_pc == source_pc)
      result.push_back(&edge);
  }
  return result;
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

IterativeLiftingSessionAnalysis::Result IterativeLiftingSessionAnalysis::run(
    llvm::Module &, llvm::ModuleAnalysisManager &) {
  if (!session_)
    session_ = std::make_shared<IterativeLiftingSession>();
  return {session_};
}

}  // namespace omill

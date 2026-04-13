#include "omill/BC/LiftDatabaseProjection.h"

#include <algorithm>
#include <deque>
#include <set>

namespace omill {
namespace {

template <typename T>
static void PushUnique(std::vector<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

static void SortAndUnique(std::vector<uint64_t> &values) {
  std::sort(values.begin(), values.end());
  values.erase(std::unique(values.begin(), values.end()), values.end());
}

static LiftDbProjectionBlock MakeProjectedBlock(
    const LiftDbBasicBlockRecord &source) {
  LiftDbProjectionBlock block;
  block.entry_va = source.entry_va;
  block.function_entry_va = source.function_entry_va;
  block.from_overlay_split = source.from_overlay_split;
  block.instruction_vas = source.instruction_vas;
  block.successors = source.successors;
  block.predecessors = source.predecessors;
  return block;
}

static LiftDbProjectionBlock MakePlaceholderBlock(uint64_t entry_va,
                                                  uint64_t function_entry_va) {
  LiftDbProjectionBlock block;
  block.entry_va = entry_va;
  block.function_entry_va = function_entry_va;
  block.from_overlay_split = true;
  return block;
}

static void RebuildPredecessors(LiftDbProjection &projection) {
  for (auto &[_, block] : projection.blocks) {
    block.predecessors.clear();
  }

  for (auto &[source_va, block] : projection.blocks) {
    for (const auto &edge : block.successors) {
      auto it = projection.blocks.find(edge.target_block_va);
      if (it == projection.blocks.end()) {
        continue;
      }
      PushUnique(it->second.predecessors, source_va);
    }
  }
}

}  // namespace

const LiftDbProjectionBlock *FindProjectionBlockContaining(
    const LiftDbProjection &projection, uint64_t pc) {
  if (auto it = projection.blocks.find(pc); it != projection.blocks.end())
    return &it->second;

  for (auto block_entry_va : projection.block_order) {
    auto block_it = projection.blocks.find(block_entry_va);
    if (block_it == projection.blocks.end())
      continue;
    const auto &instruction_vas = block_it->second.instruction_vas;
    if (std::find(instruction_vas.begin(), instruction_vas.end(), pc) !=
        instruction_vas.end()) {
      return &block_it->second;
    }
  }

  return nullptr;
}


LiftDatabaseProjector::LiftDatabaseProjector(const LiftDatabase &db) : db_(db) {}

std::optional<LiftDbProjection> LiftDatabaseProjector::projectFunction(
    uint64_t entry_va) const {
  const auto *function = db_.function(entry_va);
  if (!function) {
    return std::nullopt;
  }

  LiftDbProjection projection;
  projection.kind = LiftDbProjection::Kind::kFunction;
  projection.root_va = entry_va;

  std::deque<uint64_t> pending;
  std::set<uint64_t> visited;
  std::set<uint64_t> function_blocks(function->block_entries.begin(),
                                     function->block_entries.end());

  pending.push_back(entry_va);
  while (!pending.empty()) {
    const auto block_entry_va = pending.front();
    pending.pop_front();
    if (!visited.insert(block_entry_va).second) {
      continue;
    }

    const auto *source = db_.block(block_entry_va);
    if (source) {
      projection.blocks.emplace(block_entry_va, MakeProjectedBlock(*source));
    } else {
      projection.blocks.emplace(block_entry_va,
                                MakePlaceholderBlock(block_entry_va, entry_va));
    }
    projection.block_order.push_back(block_entry_va);

    if (!source) {
      continue;
    }

    for (const auto &edge : source->successors) {
      if (function_blocks.count(edge.target_block_va) &&
          !visited.count(edge.target_block_va)) {
        pending.push_back(edge.target_block_va);
      }
    }
  }

  std::vector<uint64_t> remaining(function->block_entries.begin(),
                                  function->block_entries.end());
  SortAndUnique(remaining);
  for (auto block_entry_va : remaining) {
    if (visited.count(block_entry_va)) {
      continue;
    }
    const auto *source = db_.block(block_entry_va);
    if (source) {
      projection.blocks.emplace(block_entry_va, MakeProjectedBlock(*source));
    } else {
      projection.blocks.emplace(block_entry_va,
                                MakePlaceholderBlock(block_entry_va, entry_va));
    }
    projection.block_order.push_back(block_entry_va);
  }

  RebuildPredecessors(projection);
  return projection;
}

std::optional<LiftDbProjection> LiftDatabaseProjector::projectBlock(
    uint64_t block_entry_va) const {
  const auto *block = db_.block(block_entry_va);
  if (!block) {
    return std::nullopt;
  }

  LiftDbProjection projection;
  projection.kind = LiftDbProjection::Kind::kBlock;
  projection.root_va = block_entry_va;
  projection.block_order.push_back(block_entry_va);
  projection.blocks.emplace(block_entry_va, MakeProjectedBlock(*block));
  RebuildPredecessors(projection);
  return projection;
}

std::optional<LiftDbProjection> LiftDatabaseProjector::projectOverlay(
    llvm::StringRef overlay_key) const {
  const auto *overlay = db_.traceOverlay(overlay_key.str());
  if (!overlay) {
    return std::nullopt;
  }

  LiftDbProjection projection;
  projection.kind = LiftDbProjection::Kind::kOverlay;
  projection.root_va = overlay->function_entry_va;
  projection.overlay_key = overlay->overlay_key;

  std::set<uint64_t> allowed_blocks(overlay->path_block_entries.begin(),
                                    overlay->path_block_entries.end());

  for (auto block_entry_va : overlay->path_block_entries) {
    const auto *source = db_.block(block_entry_va);
    if (source) {
      projection.blocks.emplace(block_entry_va, MakeProjectedBlock(*source));
    } else {
      projection.blocks.emplace(
          block_entry_va,
          MakePlaceholderBlock(block_entry_va, overlay->function_entry_va));
    }
    projection.block_order.push_back(block_entry_va);
  }

  for (auto &[block_entry_va, block] : projection.blocks) {
    std::vector<LiftDbEdgeRecord> overlay_edges;
    for (const auto &edge : overlay->constrained_edges) {
      if (edge.source_block_va == block_entry_va &&
          allowed_blocks.count(edge.target_block_va)) {
        overlay_edges.push_back(edge);
      }
    }

    if (!overlay_edges.empty()) {
      block.successors = std::move(overlay_edges);
      continue;
    }

    std::vector<LiftDbEdgeRecord> filtered_edges;
    for (const auto &edge : block.successors) {
      if (allowed_blocks.count(edge.target_block_va)) {
        filtered_edges.push_back(edge);
      }
    }
    block.successors = std::move(filtered_edges);
  }

  RebuildPredecessors(projection);
  return projection;
}

}  // namespace omill

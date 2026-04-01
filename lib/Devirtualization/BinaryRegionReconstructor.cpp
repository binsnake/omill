#include "omill/Devirtualization/BinaryRegionReconstructor.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>

#include <cstring>

namespace omill {

namespace {

LearnedOutgoingEdge makeResolvedEdge(uint64_t source_pc, uint64_t target_pc,
                                     EdgeRestatementKind restatement_kind) {
  LearnedOutgoingEdge edge;
  edge.source_pc = source_pc;
  edge.target_pc = target_pc;
  edge.restatement_kind = restatement_kind;
  edge.resolution_status = EdgeResolutionStatus::kResolved;
  return edge;
}

LearnedOutgoingEdge makeBoundaryEdge(uint64_t source_pc, uint64_t target_pc) {
  LearnedOutgoingEdge edge;
  edge.source_pc = source_pc;
  edge.target_pc = target_pc;
  edge.restatement_kind = EdgeRestatementKind::kBoundaryModeled;
  edge.resolution_status = EdgeResolutionStatus::kBoundary;
  edge.is_boundary = true;
  return edge;
}

LearnedOutgoingEdge makeTerminalEdge(uint64_t source_pc) {
  LearnedOutgoingEdge edge;
  edge.source_pc = source_pc;
  edge.restatement_kind = EdgeRestatementKind::kBinaryDirect;
  edge.resolution_status = EdgeResolutionStatus::kTerminal;
  edge.is_terminal = true;
  return edge;
}

LearnedOutgoingEdge makeUnresolvedEdge(uint64_t source_pc,
                                       EdgeRestatementKind kind) {
  LearnedOutgoingEdge edge;
  edge.source_pc = source_pc;
  edge.restatement_kind = kind;
  edge.resolution_status = EdgeResolutionStatus::kUnresolved;
  edge.is_unresolved_indirect = true;
  return edge;
}

void appendUnique(std::vector<uint64_t> &values, uint64_t pc) {
  if (!pc)
    return;
  if (llvm::find(values, pc) == values.end())
    values.push_back(pc);
}

std::optional<FrontierCallbacks::DecodedTargetSummary> decodeWithFallback(
    uint64_t pc, const FrontierCallbacks &callbacks) {
  const bool exact_fallthrough_target =
      callbacks.is_exact_call_fallthrough_target &&
      callbacks.is_exact_call_fallthrough_target(pc);
  if (callbacks.can_decode_target && !callbacks.can_decode_target(pc) &&
      !exact_fallthrough_target)
    return std::nullopt;

  if (callbacks.decode_target_summary &&
      (!callbacks.can_decode_target || callbacks.can_decode_target(pc)))
    return callbacks.decode_target_summary(pc);

  if (!callbacks.read_target_bytes)
    return std::nullopt;

  uint8_t bytes[6] = {};
  if (!callbacks.read_target_bytes(pc, bytes, sizeof(bytes)))
    return std::nullopt;

  FrontierCallbacks::DecodedTargetSummary summary;
  summary.pc = pc;

  switch (bytes[0]) {
    case 0xC3:
    case 0xC2:
      summary.is_control_flow = true;
      summary.is_return = true;
      summary.is_terminal = true;
      summary.next_pc = pc + (bytes[0] == 0xC3 ? 1 : 3);
      return summary;
    case 0xE9: {
      int32_t disp = 0;
      std::memcpy(&disp, &bytes[1], sizeof(disp));
      summary.is_control_flow = true;
      summary.branch_taken_pc = pc + 5 + static_cast<int64_t>(disp);
      summary.next_pc = pc + 5;
      return summary;
    }
    case 0xEB: {
      int8_t disp = static_cast<int8_t>(bytes[1]);
      summary.is_control_flow = true;
      summary.branch_taken_pc = pc + 2 + disp;
      summary.next_pc = pc + 2;
      return summary;
    }
    case 0xE8: {
      int32_t disp = 0;
      std::memcpy(&disp, &bytes[1], sizeof(disp));
      summary.is_control_flow = true;
      summary.is_call = true;
      summary.branch_taken_pc = pc + 5 + static_cast<int64_t>(disp);
      summary.branch_not_taken_pc = pc + 5;
      summary.next_pc = pc + 5;
      return summary;
    }
    default:
      if (bytes[0] >= 0x70 && bytes[0] <= 0x7F) {
        int8_t disp = static_cast<int8_t>(bytes[1]);
        summary.is_control_flow = true;
        summary.is_conditional = true;
        summary.branch_taken_pc = pc + 2 + disp;
        summary.branch_not_taken_pc = pc + 2;
        summary.next_pc = pc + 2;
        return summary;
      }
      if (bytes[0] == 0x0F && bytes[1] >= 0x80 && bytes[1] <= 0x8F) {
        int32_t disp = 0;
        std::memcpy(&disp, &bytes[2], sizeof(disp));
        summary.is_control_flow = true;
        summary.is_conditional = true;
        summary.branch_taken_pc = pc + 6 + static_cast<int64_t>(disp);
        summary.branch_not_taken_pc = pc + 6;
        summary.next_pc = pc + 6;
        return summary;
      }
      if (bytes[0] == 0xFF) {
        summary.is_control_flow = true;
        summary.is_indirect = true;
        summary.next_pc = pc + 1;
        return summary;
      }
      summary.next_pc = pc + 1;
      return summary;
  }
}

}  // namespace

BinaryRegionSnapshot BinaryRegionReconstructor::reconstruct(
    const BinaryRegionReconstructionRequest &request,
    const FrontierCallbacks &callbacks) const {
  BinaryRegionSnapshot snapshot;
  snapshot.entry_pc = request.root_target_pc;
  snapshot.snapshot_key = "region:" + llvm::utohexstr(request.root_target_pc);

  if (!request.root_target_pc)
    return snapshot;

  llvm::DenseSet<uint64_t> visited;
  llvm::SmallVector<uint64_t, 16> worklist = {request.root_target_pc};
  unsigned steps = 0;
  bool saw_unresolved = false;
  bool saw_boundary = false;

  while (!worklist.empty() && steps < request.policy.max_steps &&
         snapshot.blocks_by_pc.size() < request.policy.max_blocks) {
    const uint64_t pc = worklist.pop_back_val();
    if (!visited.insert(pc).second) {
      snapshot.has_structural_loop = true;
      continue;
    }
    ++steps;
    appendUnique(snapshot.visited_block_pcs, pc);

    BinaryRegionBlockSummary block;
    block.pc = pc;

    if (pc == request.root_target_pc &&
        ((request.proof && request.proof->is_exact_fallthrough) ||
         (callbacks.is_exact_call_fallthrough_target &&
          callbacks.is_exact_call_fallthrough_target(pc)))) {
      snapshot.preserved_exact_call_fallthrough = true;
    }

    auto learned_it = request.learned_edges_by_source.find(pc);
    if (learned_it != request.learned_edges_by_source.end()) {
      block.outgoing_edges = learned_it->second;
      for (const auto &edge : block.outgoing_edges) {
        if (edge.target_pc)
          worklist.push_back(*edge.target_pc);
        if (edge.is_boundary) {
          saw_boundary = true;
          if (edge.target_pc)
            appendUnique(snapshot.boundary_target_pcs, *edge.target_pc);
        }
        if (edge.is_unresolved_indirect) {
          saw_unresolved = true;
          appendUnique(snapshot.unresolved_edge_pcs, pc);
        }
      }
      snapshot.blocks_by_pc.emplace(pc, std::move(block));
      continue;
    }

    auto decoded = decodeWithFallback(pc, callbacks);
    if (!decoded) {
      block.outgoing_edges.push_back(
          makeUnresolvedEdge(pc, EdgeRestatementKind::kUnresolvedIndirect));
      saw_unresolved = true;
      appendUnique(snapshot.unresolved_edge_pcs, pc);
      snapshot.blocks_by_pc.emplace(pc, std::move(block));
      continue;
    }

    if (decoded->is_return || decoded->is_terminal) {
      block.outgoing_edges.push_back(makeTerminalEdge(pc));
      snapshot.blocks_by_pc.emplace(pc, std::move(block));
      continue;
    }

    if (decoded->is_indirect) {
      block.outgoing_edges.push_back(
          makeUnresolvedEdge(pc, EdgeRestatementKind::kUnresolvedIndirect));
      saw_unresolved = true;
      appendUnique(snapshot.unresolved_edge_pcs, pc);
      snapshot.blocks_by_pc.emplace(pc, std::move(block));
      continue;
    }

    if (decoded->branch_taken_pc) {
      const uint64_t target = *decoded->branch_taken_pc;
      if (callbacks.is_protected_boundary && callbacks.is_protected_boundary(target)) {
        block.outgoing_edges.push_back(makeBoundaryEdge(pc, target));
        saw_boundary = true;
        appendUnique(snapshot.boundary_target_pcs, target);
      } else {
        block.outgoing_edges.push_back(
            makeResolvedEdge(pc, target, EdgeRestatementKind::kBinaryDirect));
        if (visited.contains(target))
          snapshot.has_structural_loop = true;
        worklist.push_back(target);
      }
    }
    if (decoded->branch_not_taken_pc) {
      const uint64_t target = *decoded->branch_not_taken_pc;
      block.outgoing_edges.push_back(
          makeResolvedEdge(pc, target, EdgeRestatementKind::kBinaryDirect));
      if (visited.contains(target))
        snapshot.has_structural_loop = true;
      worklist.push_back(target);
    } else if (!decoded->is_control_flow && decoded->next_pc &&
               (!callbacks.is_executable_target ||
                callbacks.is_executable_target(decoded->next_pc))) {
      block.outgoing_edges.push_back(makeResolvedEdge(
          pc, decoded->next_pc, EdgeRestatementKind::kBinaryDirect));
      if (visited.contains(decoded->next_pc))
        snapshot.has_structural_loop = true;
      worklist.push_back(decoded->next_pc);
    } else if (decoded->is_call && decoded->next_pc) {
      block.outgoing_edges.push_back(makeResolvedEdge(
          pc, decoded->next_pc, EdgeRestatementKind::kBinaryDirect));
      worklist.push_back(decoded->next_pc);
    } else if (block.outgoing_edges.empty()) {
      block.outgoing_edges.push_back(makeTerminalEdge(pc));
    }

    snapshot.blocks_by_pc.emplace(pc, std::move(block));
  }

  if (saw_unresolved) {
    snapshot.closure_kind = snapshot.blocks_by_pc.size() > 1
                                ? BinaryRegionClosureKind::kPartial
                                : BinaryRegionClosureKind::kOpen;
  } else if (saw_boundary) {
    snapshot.closure_kind = BinaryRegionClosureKind::kPartial;
  } else {
    snapshot.closure_kind = BinaryRegionClosureKind::kClosed;
  }

  return snapshot;
}

}  // namespace omill

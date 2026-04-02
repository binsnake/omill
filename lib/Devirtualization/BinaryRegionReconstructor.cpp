#include "omill/Devirtualization/BinaryRegionReconstructor.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>

#include <cstring>
#include <set>
#include <tuple>

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

LearnedOutgoingEdge makeControlledReturnEdge(uint64_t source_pc,
                                             uint64_t target_pc) {
  LearnedOutgoingEdge edge;
  edge.source_pc = source_pc;
  edge.target_pc = target_pc;
  edge.restatement_kind = EdgeRestatementKind::kControlledReturn;
  edge.resolution_status = EdgeResolutionStatus::kResolved;
  edge.is_controlled_return = true;
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

LearnedOutgoingEdge makeUnresolvedControlledReturnEdge(uint64_t source_pc) {
  LearnedOutgoingEdge edge;
  edge.source_pc = source_pc;
  edge.restatement_kind = EdgeRestatementKind::kControlledReturnUnresolved;
  edge.resolution_status = EdgeResolutionStatus::kUnresolved;
  edge.is_controlled_return = true;
  edge.is_unresolved_indirect = true;
  return edge;
}

void appendUnique(std::vector<uint64_t> &values, uint64_t pc) {
  if (!pc)
    return;
  if (llvm::find(values, pc) == values.end())
    values.push_back(pc);
}

struct DescentVisitKey {
  uint64_t pc = 0;
  uint64_t call_site_pc = 0;
  uint64_t original_return_pc = 0;
  uint64_t effective_return_pc = 0;
  unsigned return_slot_id = 0;
  unsigned return_stack_cell_id = 0;
  unsigned return_owner_id = 0;
  VirtualStackOwnerKind return_owner_kind = VirtualStackOwnerKind::kUnknown;
  int64_t return_owner_delta = 0;
  VirtualReturnAddressControlKind control_kind =
      VirtualReturnAddressControlKind::kUnknown;
  bool suppresses_normal_fallthrough = false;

  bool operator<(const DescentVisitKey &other) const {
    return std::tie(pc, call_site_pc, original_return_pc, effective_return_pc,
    return_slot_id, return_stack_cell_id, return_owner_id, return_owner_kind,
    return_owner_delta, control_kind,
                    suppresses_normal_fallthrough) <
           std::tie(other.pc, other.call_site_pc, other.original_return_pc,
                    other.effective_return_pc, other.return_slot_id,
                    other.return_stack_cell_id, other.return_owner_id,
                    other.return_owner_kind, other.return_owner_delta,
                    other.control_kind,
                    other.suppresses_normal_fallthrough);
  }
};

DescentVisitKey makeVisitKey(const RecursiveDescentFrame &frame) {
  DescentVisitKey key;
  key.pc = frame.pc;
  if (!frame.return_address_state)
    return key;
  key.call_site_pc = frame.return_address_state->call_site_pc;
  key.original_return_pc = frame.return_address_state->original_return_pc.value_or(0);
  key.effective_return_pc =
      frame.return_address_state->effective_return_pc.value_or(0);
  key.return_slot_id = frame.return_address_state->return_slot_id.value_or(0);
  key.return_stack_cell_id =
      frame.return_address_state->return_stack_cell_id.value_or(0);
  key.return_owner_id = frame.return_address_state->return_owner_id.value_or(0);
  key.return_owner_kind = frame.return_address_state->return_owner_kind;
  key.return_owner_delta =
      frame.return_address_state->return_owner_delta.value_or(0);
  key.control_kind = frame.return_address_state->control_kind;
  key.suppresses_normal_fallthrough =
      frame.return_address_state->suppresses_normal_fallthrough;
  return key;
}

RecursiveDescentFrame makeFrame(
    uint64_t pc,
    std::optional<DescentReturnAddressState> return_address_state = std::nullopt) {
  RecursiveDescentFrame frame;
  frame.pc = pc;
  frame.return_address_state = std::move(return_address_state);
  return frame;
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

  std::set<DescentVisitKey> visited;
  llvm::SmallVector<RecursiveDescentFrame, 16> worklist = {
      makeFrame(request.root_target_pc, request.initial_return_address_state)};
  unsigned steps = 0;
  bool saw_unresolved = false;
  bool saw_boundary = false;

  while (!worklist.empty() && steps < request.policy.max_steps &&
         snapshot.blocks_by_pc.size() < request.policy.max_blocks) {
    const RecursiveDescentFrame frame = worklist.pop_back_val();
    const uint64_t pc = frame.pc;
    if (!visited.insert(makeVisitKey(frame)).second) {
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
          worklist.push_back(makeFrame(*edge.target_pc, frame.return_address_state));
        if (edge.is_boundary) {
          saw_boundary = true;
          if (edge.target_pc)
            appendUnique(snapshot.boundary_target_pcs, *edge.target_pc);
        }
        if (edge.is_controlled_return && edge.is_unresolved_indirect) {
          saw_unresolved = true;
          appendUnique(snapshot.controlled_return_unresolved_pcs, pc);
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

    if (decoded->is_return) {
      if (frame.return_address_state &&
          frame.return_address_state->suppresses_normal_fallthrough) {
        if (frame.return_address_state->effective_return_pc) {
          block.outgoing_edges.push_back(makeControlledReturnEdge(
              pc, *frame.return_address_state->effective_return_pc));
          if (visited.find(makeVisitKey(makeFrame(
                              *frame.return_address_state
                                   ->effective_return_pc))) != visited.end()) {
            snapshot.has_structural_loop = true;
          }
          worklist.push_back(makeFrame(
              *frame.return_address_state->effective_return_pc));
        } else {
          block.outgoing_edges.push_back(makeUnresolvedControlledReturnEdge(pc));
          saw_unresolved = true;
          appendUnique(snapshot.unresolved_edge_pcs, pc);
          appendUnique(snapshot.controlled_return_unresolved_pcs, pc);
        }
      } else if (frame.return_address_state &&
                 frame.return_address_state->original_return_pc) {
        block.outgoing_edges.push_back(makeResolvedEdge(
            pc, *frame.return_address_state->original_return_pc,
            EdgeRestatementKind::kBinaryDirect));
        if (visited.find(makeVisitKey(
                makeFrame(*frame.return_address_state->original_return_pc))) !=
            visited.end()) {
          snapshot.has_structural_loop = true;
        }
        worklist.push_back(
            makeFrame(*frame.return_address_state->original_return_pc));
      } else {
        block.outgoing_edges.push_back(makeTerminalEdge(pc));
      }
      snapshot.blocks_by_pc.emplace(pc, std::move(block));
      continue;
    }

    if (decoded->is_terminal) {
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
        if (visited.find(makeVisitKey(makeFrame(target))) != visited.end())
          snapshot.has_structural_loop = true;
        if (decoded->is_call) {
          DescentReturnAddressState return_state;
          return_state.call_site_pc = pc;
          return_state.original_return_pc = decoded->next_pc;
          return_state.effective_return_pc = decoded->next_pc;
          return_state.return_owner_kind =
              VirtualStackOwnerKind::kNativeStackPointer;
          return_state.control_kind =
              VirtualReturnAddressControlKind::kPreserved;
          return_state.suppresses_normal_fallthrough = false;
          worklist.push_back(makeFrame(target, return_state));
        } else {
          worklist.push_back(makeFrame(target, frame.return_address_state));
        }
      }
    }
    if (decoded->branch_not_taken_pc && !decoded->is_call) {
      const uint64_t target = *decoded->branch_not_taken_pc;
      block.outgoing_edges.push_back(
          makeResolvedEdge(pc, target, EdgeRestatementKind::kBinaryDirect));
      if (visited.find(
              makeVisitKey(makeFrame(target, frame.return_address_state))) !=
          visited.end())
        snapshot.has_structural_loop = true;
      worklist.push_back(makeFrame(target, frame.return_address_state));
    } else if (!decoded->is_control_flow && decoded->next_pc &&
               (!callbacks.is_executable_target ||
                callbacks.is_executable_target(decoded->next_pc))) {
      block.outgoing_edges.push_back(makeResolvedEdge(
          pc, decoded->next_pc, EdgeRestatementKind::kBinaryDirect));
      if (visited.find(makeVisitKey(
              makeFrame(decoded->next_pc, frame.return_address_state))) !=
          visited.end())
        snapshot.has_structural_loop = true;
      worklist.push_back(makeFrame(decoded->next_pc, frame.return_address_state));
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

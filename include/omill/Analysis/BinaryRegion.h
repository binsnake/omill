#pragma once

#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace omill {

enum class EdgeRestatementKind {
  kUnknown,
  kBinaryDirect,
  kProofSupplied,
  kBoundaryModeled,
  kUnresolvedIndirect,
};

enum class EdgeResolutionStatus {
  kUnknown,
  kResolved,
  kBoundary,
  kTerminal,
  kUnresolved,
};

enum class BinaryRegionClosureKind {
  kClosed,
  kPartial,
  kOpen,
};

struct LearnedOutgoingEdge {
  uint64_t source_pc = 0;
  std::optional<uint64_t> target_pc;
  EdgeRestatementKind restatement_kind = EdgeRestatementKind::kUnknown;
  EdgeResolutionStatus resolution_status = EdgeResolutionStatus::kUnknown;
  bool is_boundary = false;
  bool is_terminal = false;
  bool is_unresolved_indirect = false;

  bool operator==(const LearnedOutgoingEdge &other) const {
    return source_pc == other.source_pc && target_pc == other.target_pc &&
           restatement_kind == other.restatement_kind &&
           resolution_status == other.resolution_status &&
           is_boundary == other.is_boundary &&
           is_terminal == other.is_terminal &&
           is_unresolved_indirect == other.is_unresolved_indirect;
  }
};

struct BinaryRegionBlockSummary {
  uint64_t pc = 0;
  std::vector<LearnedOutgoingEdge> outgoing_edges;
};

struct BinaryRegionSnapshot {
  std::string snapshot_key;
  uint64_t entry_pc = 0;
  std::vector<uint64_t> visited_block_pcs;
  std::map<uint64_t, BinaryRegionBlockSummary> blocks_by_pc;
  std::vector<uint64_t> unresolved_edge_pcs;
  std::vector<uint64_t> boundary_target_pcs;
  BinaryRegionClosureKind closure_kind = BinaryRegionClosureKind::kOpen;
  bool has_structural_loop = false;
  bool preserved_exact_call_fallthrough = false;
};

const char *toString(EdgeRestatementKind kind);
const char *toString(EdgeResolutionStatus status);
const char *toString(BinaryRegionClosureKind kind);

}  // namespace omill

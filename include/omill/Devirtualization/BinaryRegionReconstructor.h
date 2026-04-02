#pragma once

#include <map>
#include <optional>
#include <string>

#include "omill/Analysis/BinaryRegion.h"
#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/ProtectorModel.h"

namespace omill {

struct BinaryRegionReconstructionPolicy {
  unsigned max_steps = 32;
  unsigned max_blocks = 32;
};

struct DescentReturnAddressState {
  uint64_t call_site_pc = 0;
  std::optional<uint64_t> original_return_pc;
  std::optional<uint64_t> effective_return_pc;
  std::optional<unsigned> return_slot_id;
  std::optional<unsigned> return_stack_cell_id;
  std::optional<unsigned> return_owner_id;
  VirtualStackOwnerKind return_owner_kind = VirtualStackOwnerKind::kUnknown;
  std::optional<int64_t> return_owner_delta;
  VirtualReturnAddressControlKind control_kind =
      VirtualReturnAddressControlKind::kUnknown;
  bool suppresses_normal_fallthrough = false;
};

struct RecursiveDescentFrame {
  uint64_t pc = 0;
  std::optional<DescentReturnAddressState> return_address_state;
};

struct BinaryRegionReconstructionRequest {
  uint64_t root_target_pc = 0;
  std::optional<ContinuationProof> proof;
  std::map<uint64_t, std::vector<LearnedOutgoingEdge>> learned_edges_by_source;
  std::optional<DescentReturnAddressState> initial_return_address_state;
  BinaryRegionReconstructionPolicy policy;
};

class BinaryRegionReconstructor {
 public:
  BinaryRegionSnapshot reconstruct(const BinaryRegionReconstructionRequest &request,
                                   const FrontierCallbacks &callbacks) const;
};

}  // namespace omill

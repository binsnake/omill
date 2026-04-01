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

struct BinaryRegionReconstructionRequest {
  uint64_t root_target_pc = 0;
  std::optional<ContinuationProof> proof;
  std::map<uint64_t, std::vector<LearnedOutgoingEdge>> learned_edges_by_source;
  BinaryRegionReconstructionPolicy policy;
};

class BinaryRegionReconstructor {
 public:
  BinaryRegionSnapshot reconstruct(const BinaryRegionReconstructionRequest &request,
                                   const FrontierCallbacks &callbacks) const;
};

}  // namespace omill

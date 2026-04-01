#pragma once

#include <optional>
#include <utility>

#include "omill/Analysis/BinaryRegion.h"
#include "omill/Devirtualization/BinaryRegionReconstructor.h"
#include "omill/Devirtualization/ProtectorModel.h"

namespace omill {

enum class ContinuationResolverKind {
  kExecutable,
  kBoundary,
};

enum class ContinuationResolutionDisposition {
  kImportableTrustedEntry,
  kImportableClosedSliceRoot,
  kBoundaryModeledChild,
  kRetryableOpenRegion,
  kDeferredQuarantinedSelectorArm,
  kRejectedRuntimeLeakingChild,
  kRejectedUnsupported,
};

struct ContinuationResolutionRequest {
  ContinuationResolverKind kind = ContinuationResolverKind::kExecutable;
  uint64_t target_pc = 0;
  std::optional<ContinuationProof> proof;
  std::map<uint64_t, std::vector<LearnedOutgoingEdge>> learned_edges_by_source;
};

struct ContinuationResolutionResult {
  ContinuationResolverKind kind = ContinuationResolverKind::kExecutable;
  ContinuationResolutionDisposition disposition =
      ContinuationResolutionDisposition::kRejectedUnsupported;
  BinaryRegionSnapshot region_snapshot;
  ContinuationProof updated_proof;
  std::string rationale;
};

enum class BoundaryResolutionDisposition {
  kModeledReentryBoundary,
  kModeledTerminalBoundary,
  kRetryableBoundaryRecovery,
  kHardRejectedUnsupportedBoundary,
};

struct BoundaryResolutionRequest {
  uint64_t target_pc = 0;
  std::optional<BoundaryFact> boundary;
  std::optional<ContinuationProof> proof;
};

struct BoundaryResolutionResult {
  ContinuationResolverKind kind = ContinuationResolverKind::kBoundary;
  BoundaryResolutionDisposition disposition =
      BoundaryResolutionDisposition::kHardRejectedUnsupportedBoundary;
  std::optional<BoundaryFact> boundary;
  std::optional<ContinuationProof> updated_proof;
  std::string rationale;
};

class ContinuationResolver {
 public:
  virtual ~ContinuationResolver() = default;

  virtual ContinuationResolutionResult resolve(
      const ContinuationResolutionRequest &request,
      const FrontierCallbacks &callbacks) const = 0;
};

class ExecutableContinuationResolver : public ContinuationResolver {
 public:
  explicit ExecutableContinuationResolver(
      BinaryRegionReconstructor reconstructor = {})
      : reconstructor_(std::move(reconstructor)) {}

  ContinuationResolutionResult resolve(
      const ContinuationResolutionRequest &request,
      const FrontierCallbacks &callbacks) const override;

 private:
  BinaryRegionReconstructor reconstructor_;
};

class BoundaryContinuationResolver {
 public:
  BoundaryResolutionResult resolve(
      const BoundaryResolutionRequest &request) const;
};

const char *toString(ContinuationResolverKind kind);
const char *toString(ContinuationResolutionDisposition disposition);
const char *toString(BoundaryResolutionDisposition disposition);

}  // namespace omill

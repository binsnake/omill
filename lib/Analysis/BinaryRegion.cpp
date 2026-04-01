#include "omill/Analysis/BinaryRegion.h"

namespace omill {

const char *toString(EdgeRestatementKind kind) {
  switch (kind) {
    case EdgeRestatementKind::kUnknown:
      return "unknown";
    case EdgeRestatementKind::kBinaryDirect:
      return "binary_direct";
    case EdgeRestatementKind::kProofSupplied:
      return "proof_supplied";
    case EdgeRestatementKind::kBoundaryModeled:
      return "boundary_modeled";
    case EdgeRestatementKind::kUnresolvedIndirect:
      return "unresolved_indirect";
  }
  return "unknown";
}

const char *toString(EdgeResolutionStatus status) {
  switch (status) {
    case EdgeResolutionStatus::kUnknown:
      return "unknown";
    case EdgeResolutionStatus::kResolved:
      return "resolved";
    case EdgeResolutionStatus::kBoundary:
      return "boundary";
    case EdgeResolutionStatus::kTerminal:
      return "terminal";
    case EdgeResolutionStatus::kUnresolved:
      return "unresolved";
  }
  return "unknown";
}

const char *toString(BinaryRegionClosureKind kind) {
  switch (kind) {
    case BinaryRegionClosureKind::kClosed:
      return "closed";
    case BinaryRegionClosureKind::kPartial:
      return "partial";
    case BinaryRegionClosureKind::kOpen:
      return "open";
  }
  return "open";
}

}  // namespace omill

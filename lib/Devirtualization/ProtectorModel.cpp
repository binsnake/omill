#include "omill/Devirtualization/ProtectorModel.h"

namespace omill {

const char *toString(ContinuationProvenance provenance) {
  switch (provenance) {
    case ContinuationProvenance::kUnknown:
      return "unknown";
    case ContinuationProvenance::kExactFallthrough:
      return "exact_fallthrough";
    case ContinuationProvenance::kInvalidatedExecutableEntry:
      return "invalidated_executable_entry";
    case ContinuationProvenance::kExecutablePlaceholder:
      return "executable_placeholder";
    case ContinuationProvenance::kNativeBoundary:
      return "native_boundary";
    case ContinuationProvenance::kVmEnterBoundary:
      return "vm_enter_boundary";
    case ContinuationProvenance::kSelectorDerived:
      return "selector_derived";
    case ContinuationProvenance::kTerminalBoundary:
      return "terminal_boundary";
  }
  return "unknown";
}

const char *toString(ContinuationConfidence confidence) {
  switch (confidence) {
    case ContinuationConfidence::kTrusted:
      return "trusted";
    case ContinuationConfidence::kWeak:
      return "weak";
    case ContinuationConfidence::kDeadArmSuspect:
      return "dead_arm_suspect";
  }
  return "weak";
}

const char *toString(ContinuationLiveness liveness) {
  switch (liveness) {
    case ContinuationLiveness::kLive:
      return "live";
    case ContinuationLiveness::kUnknown:
      return "unknown";
    case ContinuationLiveness::kQuarantined:
      return "quarantined";
  }
  return "unknown";
}

const char *toString(FrontierSchedulingClass scheduling_class) {
  switch (scheduling_class) {
    case FrontierSchedulingClass::kTrustedLive:
      return "trusted_live";
    case FrontierSchedulingClass::kWeakExecutable:
      return "weak_executable";
    case FrontierSchedulingClass::kQuarantinedSelectorArm:
      return "quarantined_selector_arm";
    case FrontierSchedulingClass::kTerminalModeled:
      return "terminal_modeled";
    case FrontierSchedulingClass::kNativeOrVmEnterBoundary:
      return "native_or_vm_enter_boundary";
  }
  return "weak_executable";
}

const char *toString(ContinuationResolutionKind resolution_kind) {
  switch (resolution_kind) {
    case ContinuationResolutionKind::kUnknown:
      return "unknown";
    case ContinuationResolutionKind::kTrustedEntry:
      return "trusted_entry";
    case ContinuationResolutionKind::kExactFallthrough:
      return "exact_fallthrough";
    case ContinuationResolutionKind::kInvalidatedExecutableEntry:
      return "invalidated_executable_entry";
    case ContinuationResolutionKind::kBoundaryModeled:
      return "boundary_modeled";
    case ContinuationResolutionKind::kCanonicalOwnerRedirect:
      return "canonical_owner_redirect";
    case ContinuationResolutionKind::kQuarantinedSelectorArm:
      return "quarantined_selector_arm";
    case ContinuationResolutionKind::kTerminalModeled:
      return "terminal_modeled";
  }
  return "unknown";
}

const char *toString(ContinuationImportDisposition import_disposition) {
  switch (import_disposition) {
    case ContinuationImportDisposition::kUnknown:
      return "unknown";
    case ContinuationImportDisposition::kImportable:
      return "importable";
    case ContinuationImportDisposition::kRetryable:
      return "retryable";
    case ContinuationImportDisposition::kDeferred:
      return "deferred";
    case ContinuationImportDisposition::kRejected:
      return "rejected";
  }
  return "unknown";
}

const char *toString(ChildImportClass import_class) {
  switch (import_class) {
    case ChildImportClass::kTrustedTerminalEntry:
      return "trusted_terminal_entry";
    case ChildImportClass::kClosedSliceRoot:
      return "closed_slice_root";
    case ChildImportClass::kBoundaryModeledChild:
      return "boundary_modeled_child";
    case ChildImportClass::kRuntimeLeakingChild:
      return "runtime_leaking_child";
    case ChildImportClass::kTerminalOnlyUnknown:
      return "terminal_only_unknown";
    case ChildImportClass::kUnsupported:
      return "unsupported";
  }
  return "unsupported";
}

const char *toString(ProtectorValidationIssueClass issue_class) {
  switch (issue_class) {
    case ProtectorValidationIssueClass::kExecutablePlaceholder:
      return "executable_placeholder";
    case ProtectorValidationIssueClass::kQuarantinedSelectorArm:
      return "quarantined_selector_arm";
    case ProtectorValidationIssueClass::kNativeOrVmEnterBoundary:
      return "native_or_vm_enter_boundary";
    case ProtectorValidationIssueClass::kTerminalEdge:
      return "terminal_edge";
    case ProtectorValidationIssueClass::kRemillRuntimeLeak:
      return "remill_runtime_leak";
    case ProtectorValidationIssueClass::kTrustedTargetMismatch:
      return "trusted_target_mismatch";
  }
  return "executable_placeholder";
}

}  // namespace omill

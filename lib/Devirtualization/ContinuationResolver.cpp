#include "omill/Devirtualization/ContinuationResolver.h"

#include <llvm/ADT/StringExtras.h>

namespace omill {

namespace {

ContinuationProof makeUpdatedProof(const ContinuationResolutionRequest &request) {
  ContinuationProof proof = request.proof.value_or(ContinuationProof{});
  if (!proof.raw_target_pc)
    proof.raw_target_pc = request.target_pc;
  return proof;
}

ContinuationProof makeBoundaryUpdatedProof(
    const BoundaryResolutionRequest &request) {
  ContinuationProof proof = request.proof.value_or(ContinuationProof{});
  if (!proof.raw_target_pc)
    proof.raw_target_pc = request.target_pc;
  return proof;
}

}  // namespace

ContinuationResolutionResult ExecutableContinuationResolver::resolve(
    const ContinuationResolutionRequest &request,
    const FrontierCallbacks &callbacks) const {
  ContinuationResolutionResult result;
  result.kind = ContinuationResolverKind::kExecutable;
  result.updated_proof = makeUpdatedProof(request);

  BinaryRegionReconstructionRequest reconstruction_request;
  reconstruction_request.root_target_pc = request.target_pc;
  reconstruction_request.proof = request.proof;
  reconstruction_request.learned_edges_by_source = request.learned_edges_by_source;
  result.region_snapshot =
      reconstructor_.reconstruct(reconstruction_request, callbacks);
  result.updated_proof.binary_region_snapshot_key =
      result.region_snapshot.snapshot_key;
  result.updated_proof.resolution_detail =
      "region=" + std::string(toString(result.region_snapshot.closure_kind)) +
      ",blocks=" +
      std::to_string(result.region_snapshot.blocks_by_pc.size());

  if (request.proof &&
      request.proof->liveness == ContinuationLiveness::kQuarantined) {
    result.disposition =
        ContinuationResolutionDisposition::kDeferredQuarantinedSelectorArm;
    result.updated_proof.import_disposition =
        ContinuationImportDisposition::kDeferred;
    result.rationale = "quarantined_selector_arm";
    return result;
  }

  if (request.proof &&
      request.proof->resolution_kind ==
          ContinuationResolutionKind::kBoundaryModeled) {
    result.disposition =
        ContinuationResolutionDisposition::kBoundaryModeledChild;
    result.updated_proof.import_disposition =
        ContinuationImportDisposition::kImportable;
    result.updated_proof.selected_root_import_class =
        ChildImportClass::kBoundaryModeledChild;
    result.rationale = "boundary_modeled";
    return result;
  }

  const bool importable_from_exact_proof =
      request.proof &&
      (request.proof->resolution_kind ==
           ContinuationResolutionKind::kExactFallthrough ||
       request.proof->resolution_kind ==
           ContinuationResolutionKind::kTrustedEntry ||
       request.proof->resolution_kind ==
           ContinuationResolutionKind::kCanonicalOwnerRedirect) &&
      result.region_snapshot.entry_pc != 0 &&
      result.region_snapshot.preserved_exact_call_fallthrough;

  if (importable_from_exact_proof) {
    result.disposition =
        ContinuationResolutionDisposition::kImportableTrustedEntry;
    result.updated_proof.import_disposition =
        ContinuationImportDisposition::kImportable;
    result.updated_proof.selected_root_import_class =
        ChildImportClass::kTrustedTerminalEntry;
    result.rationale = "trusted_exact_fallthrough_region";
    return result;
  }

  const bool importable_from_binary_exact_fallthrough =
      request.proof &&
      request.proof->resolution_kind ==
          ContinuationResolutionKind::kTerminalModeled &&
      request.proof->import_disposition ==
          ContinuationImportDisposition::kRetryable &&
      request.proof->liveness != ContinuationLiveness::kQuarantined &&
      result.region_snapshot.entry_pc != 0 &&
      result.region_snapshot.preserved_exact_call_fallthrough;

  if (importable_from_binary_exact_fallthrough) {
    result.disposition =
        ContinuationResolutionDisposition::kImportableTrustedEntry;
    result.updated_proof.resolution_kind =
        ContinuationResolutionKind::kExactFallthrough;
    result.updated_proof.import_disposition =
        ContinuationImportDisposition::kImportable;
    result.updated_proof.selected_root_import_class =
        ChildImportClass::kTrustedTerminalEntry;
    result.updated_proof.confidence = ContinuationConfidence::kTrusted;
    result.updated_proof.liveness = ContinuationLiveness::kLive;
    result.updated_proof.scheduling_class =
        FrontierSchedulingClass::kTrustedLive;
    result.updated_proof.is_exact_fallthrough = true;
    result.rationale = "binary_exact_fallthrough_region";
    return result;
  }

  if (result.region_snapshot.closure_kind == BinaryRegionClosureKind::kClosed &&
      request.proof &&
      request.proof->confidence == ContinuationConfidence::kTrusted) {
    result.disposition =
        ContinuationResolutionDisposition::kImportableClosedSliceRoot;
    result.updated_proof.import_disposition =
        ContinuationImportDisposition::kImportable;
    result.updated_proof.selected_root_import_class =
        ChildImportClass::kClosedSliceRoot;
    result.rationale = "closed_binary_region";
    return result;
  }

  if (request.proof &&
      request.proof->resolution_kind ==
          ContinuationResolutionKind::kInvalidatedExecutableEntry) {
    result.disposition = result.region_snapshot.closure_kind ==
                                 BinaryRegionClosureKind::kClosed
                             ? ContinuationResolutionDisposition::
                                   kRetryableOpenRegion
                             : ContinuationResolutionDisposition::
                                   kRejectedUnsupported;
    result.updated_proof.import_disposition =
        result.disposition ==
                ContinuationResolutionDisposition::kRetryableOpenRegion
            ? ContinuationImportDisposition::kRetryable
            : ContinuationImportDisposition::kRejected;
    result.rationale = "invalidated_executable_region";
    return result;
  }

  if (result.region_snapshot.closure_kind == BinaryRegionClosureKind::kOpen ||
      result.region_snapshot.closure_kind == BinaryRegionClosureKind::kPartial) {
    result.disposition = ContinuationResolutionDisposition::kRetryableOpenRegion;
    result.updated_proof.import_disposition =
        ContinuationImportDisposition::kRetryable;
    result.rationale = "open_binary_region";
    return result;
  }

  result.disposition = ContinuationResolutionDisposition::kRejectedUnsupported;
  result.updated_proof.import_disposition =
      ContinuationImportDisposition::kRejected;
  result.rationale = "unsupported_region";
  return result;
}

BoundaryResolutionResult BoundaryContinuationResolver::resolve(
    const BoundaryResolutionRequest &request) const {
  BoundaryResolutionResult result;
  result.kind = ContinuationResolverKind::kBoundary;
  result.boundary = request.boundary;
  result.updated_proof = makeBoundaryUpdatedProof(request);

  if (!request.boundary) {
    result.disposition =
        BoundaryResolutionDisposition::kHardRejectedUnsupportedBoundary;
    result.updated_proof->import_disposition =
        ContinuationImportDisposition::kRejected;
    result.rationale = "missing_boundary_fact";
    return result;
  }

  const auto &boundary = *request.boundary;
  const bool has_reentry_evidence =
      boundary.reenters_vm || boundary.is_vm_enter ||
      boundary.is_nested_vm_enter || boundary.continuation_pc.has_value() ||
      boundary.continuation_slot_id.has_value() ||
      boundary.continuation_stack_cell_id.has_value();
  if (has_reentry_evidence) {
    result.disposition = BoundaryResolutionDisposition::kModeledReentryBoundary;
    result.updated_proof->resolution_kind =
        ContinuationResolutionKind::kBoundaryModeled;
    result.updated_proof->import_disposition =
        ContinuationImportDisposition::kRejected;
    result.updated_proof->selected_root_import_class =
        ChildImportClass::kBoundaryModeledChild;
    result.updated_proof->provenance =
        boundary.is_vm_enter || boundary.is_nested_vm_enter
            ? ContinuationProvenance::kVmEnterBoundary
            : ContinuationProvenance::kNativeBoundary;
    result.updated_proof->rationale = "modeled_reentry_boundary";
    result.rationale = boundary.reenters_vm
                           ? "boundary_reenters_vm"
                           : (boundary.continuation_stack_cell_id
                                  ? "boundary_continuation_stack_cell"
                                  : (boundary.continuation_slot_id
                                         ? "boundary_continuation_slot"
                                         : "boundary_continuation_pc"));
    return result;
  }

  const bool is_modeled_terminal =
      boundary.kind == BoundaryKind::kTerminalBoundary ||
      boundary.exit_disposition == BoundaryDisposition::kVmExitTerminal ||
      boundary.is_partial_exit || boundary.is_full_exit;
  if (is_modeled_terminal) {
    result.disposition = BoundaryResolutionDisposition::kModeledTerminalBoundary;
    result.updated_proof->resolution_kind =
        ContinuationResolutionKind::kTerminalModeled;
    result.updated_proof->import_disposition =
        ContinuationImportDisposition::kRejected;
    result.updated_proof->provenance =
        ContinuationProvenance::kTerminalBoundary;
    result.updated_proof->rationale = "modeled_terminal_boundary";
    result.rationale = "boundary_terminal_modeled";
    return result;
  }

  if (boundary.native_target_pc || boundary.boundary_pc) {
    result.disposition = BoundaryResolutionDisposition::kRetryableBoundaryRecovery;
    result.updated_proof->import_disposition =
        ContinuationImportDisposition::kRetryable;
    result.updated_proof->provenance = ContinuationProvenance::kNativeBoundary;
    result.updated_proof->rationale = "retryable_boundary_recovery";
    result.rationale = "retryable_boundary_recovery";
    return result;
  }

  result.disposition =
      BoundaryResolutionDisposition::kHardRejectedUnsupportedBoundary;
  result.updated_proof->import_disposition =
      ContinuationImportDisposition::kRejected;
  result.updated_proof->rationale = "unsupported_boundary";
  result.rationale = "unsupported_boundary";
  return result;
}

const char *toString(ContinuationResolverKind kind) {
  switch (kind) {
    case ContinuationResolverKind::kExecutable:
      return "executable";
    case ContinuationResolverKind::kBoundary:
      return "boundary";
  }
  return "executable";
}

const char *toString(ContinuationResolutionDisposition disposition) {
  switch (disposition) {
    case ContinuationResolutionDisposition::kImportableTrustedEntry:
      return "importable_trusted_entry";
    case ContinuationResolutionDisposition::kImportableClosedSliceRoot:
      return "importable_closed_slice_root";
    case ContinuationResolutionDisposition::kBoundaryModeledChild:
      return "boundary_modeled_child";
    case ContinuationResolutionDisposition::kRetryableOpenRegion:
      return "retryable_open_region";
    case ContinuationResolutionDisposition::kDeferredQuarantinedSelectorArm:
      return "deferred_quarantined_selector_arm";
    case ContinuationResolutionDisposition::kRejectedRuntimeLeakingChild:
      return "rejected_runtime_leaking_child";
    case ContinuationResolutionDisposition::kRejectedUnsupported:
      return "rejected_unsupported";
  }
  return "rejected_unsupported";
}

const char *toString(BoundaryResolutionDisposition disposition) {
  switch (disposition) {
    case BoundaryResolutionDisposition::kModeledReentryBoundary:
      return "modeled_reentry_boundary";
    case BoundaryResolutionDisposition::kModeledTerminalBoundary:
      return "modeled_terminal_boundary";
    case BoundaryResolutionDisposition::kRetryableBoundaryRecovery:
      return "retryable_boundary_recovery";
    case BoundaryResolutionDisposition::kHardRejectedUnsupportedBoundary:
      return "hard_rejected_unsupported_boundary";
  }
  return "hard_rejected_unsupported_boundary";
}

}  // namespace omill

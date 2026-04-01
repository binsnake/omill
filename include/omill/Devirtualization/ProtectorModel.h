#pragma once

#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"

namespace llvm {
class Module;
}

namespace omill {

enum class ContinuationProvenance {
  kUnknown,
  kExactFallthrough,
  kInvalidatedExecutableEntry,
  kExecutablePlaceholder,
  kNativeBoundary,
  kVmEnterBoundary,
  kSelectorDerived,
  kTerminalBoundary,
};

enum class ContinuationConfidence {
  kTrusted,
  kWeak,
  kDeadArmSuspect,
};

enum class ContinuationLiveness {
  kLive,
  kUnknown,
  kQuarantined,
};

enum class FrontierSchedulingClass {
  kTrustedLive,
  kWeakExecutable,
  kQuarantinedSelectorArm,
  kTerminalModeled,
  kNativeOrVmEnterBoundary,
};

enum class ContinuationResolutionKind {
  kUnknown,
  kTrustedEntry,
  kExactFallthrough,
  kInvalidatedExecutableEntry,
  kBoundaryModeled,
  kCanonicalOwnerRedirect,
  kQuarantinedSelectorArm,
  kTerminalModeled,
};

enum class ContinuationImportDisposition {
  kUnknown,
  kImportable,
  kRetryable,
  kDeferred,
  kRejected,
};

enum class ChildImportClass {
  kTrustedTerminalEntry,
  kClosedSliceRoot,
  kBoundaryModeledChild,
  kRuntimeLeakingChild,
  kTerminalOnlyUnknown,
  kUnsupported,
};

struct ContinuationProof {
  std::string edge_identity;
  uint64_t raw_target_pc = 0;
  std::optional<uint64_t> effective_target_pc;
  std::optional<uint64_t> canonical_owner_pc;
  std::string source_handler_name;
  ContinuationProvenance provenance = ContinuationProvenance::kUnknown;
  ContinuationConfidence confidence = ContinuationConfidence::kWeak;
  ContinuationLiveness liveness = ContinuationLiveness::kUnknown;
  FrontierSchedulingClass scheduling_class =
      FrontierSchedulingClass::kWeakExecutable;
  ContinuationResolutionKind resolution_kind =
      ContinuationResolutionKind::kUnknown;
  ContinuationImportDisposition import_disposition =
      ContinuationImportDisposition::kUnknown;
  bool is_trusted_entry = false;
  bool is_exact_fallthrough = false;
  bool is_invalidated_entry = false;
  std::optional<uint64_t> invalidated_entry_source_pc;
  std::optional<uint64_t> invalidated_entry_failed_pc;
  std::optional<uint64_t> selected_root_pc;
  std::optional<ChildImportClass> selected_root_import_class;
  std::optional<std::string> binary_region_snapshot_key;
  std::string resolution_detail;
  std::string rationale;
};

struct ContinuationCandidate {
  std::string edge_identity;
  std::string source_handler_name;
  std::optional<uint64_t> raw_target_pc;
  std::optional<uint64_t> effective_target_pc;
  std::optional<uint64_t> canonical_owner_pc;
  ContinuationProvenance provenance = ContinuationProvenance::kUnknown;
  ContinuationConfidence confidence = ContinuationConfidence::kWeak;
  ContinuationLiveness liveness = ContinuationLiveness::kUnknown;
  FrontierSchedulingClass scheduling_class =
      FrontierSchedulingClass::kWeakExecutable;
  std::optional<ExecutableTargetFact> executable_target;
  std::optional<BoundaryFact> boundary;
  std::optional<ContinuationProof> proof;
  std::string rationale;
};

struct SelectorOutcome {
  std::string edge_identity;
  std::optional<uint64_t> target_pc;
  ContinuationConfidence confidence = ContinuationConfidence::kWeak;
  ContinuationLiveness liveness = ContinuationLiveness::kUnknown;
  std::string rationale;
};

struct DispatcherFamily {
  std::string id;
  std::string anchor_handler_name;
  std::vector<std::string> handler_names;
  std::vector<std::string> continuation_edge_identities;
};

struct HandlerRegion {
  std::string id;
  std::optional<uint64_t> root_va;
  std::vector<std::string> handler_names;
  std::vector<std::string> entry_handler_names;
  std::vector<std::string> frontier_edge_identities;
  std::vector<uint64_t> child_entry_pcs;
};

struct ProtectorModel {
  std::vector<ContinuationCandidate> continuation_candidates;
  std::map<std::string, SelectorOutcome> selector_outcomes_by_edge;
  std::vector<DispatcherFamily> dispatcher_families;
  std::vector<HandlerRegion> handler_regions;
};

enum class ProtectorValidationIssueClass {
  kExecutablePlaceholder,
  kQuarantinedSelectorArm,
  kNativeOrVmEnterBoundary,
  kTerminalEdge,
  kRemillRuntimeLeak,
  kTrustedTargetMismatch,
};

struct ProtectorValidationIssue {
  ProtectorValidationIssueClass issue_class =
      ProtectorValidationIssueClass::kExecutablePlaceholder;
  std::string root_name;
  std::string caller_name;
  std::string callee_name;
  std::string edge_identity;
  std::string message;
};

struct ProtectorValidationReport {
  ProtectorModel model;
  std::vector<ProtectorValidationIssue> issues;
  std::map<std::string, unsigned> counts_by_class;
};

const char *toString(ContinuationProvenance provenance);
const char *toString(ContinuationConfidence confidence);
const char *toString(ContinuationLiveness liveness);
const char *toString(FrontierSchedulingClass scheduling_class);
const char *toString(ContinuationResolutionKind resolution_kind);
const char *toString(ContinuationImportDisposition import_disposition);
const char *toString(ChildImportClass import_class);
const char *toString(ProtectorValidationIssueClass issue_class);

}  // namespace omill

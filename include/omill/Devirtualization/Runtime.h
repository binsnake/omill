#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <tuple>
#include <vector>

#include <llvm/ADT/StringRef.h>
#include <llvm/ADT/StableHashing.h>

#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/ProtectorModel.h"
#include "omill/Devirtualization/ContinuationResolver.h"

namespace llvm {
class Function;
class Module;
}

namespace omill {

class BlockLifter;
class IterativeLiftingSession;

enum class ImportEligibility {
  kImportable,
  kRetryable,
  kRejected,
};

enum class ChildArtifactLeakKind {
  kNone,
  kRemillJump,
  kRemillFunctionCall,
  kRemillMemoryIntrinsic,
  kExternalCall,
};

enum class RecoveryRejectionReason {
  kNone,
  kChildLiftFailed,
  kImportFailed,
  kTypeMismatch,
  kParseFailed,
  kMissingRoot,
  kDisallowedFunction,
  kDeclarationRejected,
  kGlobalRejected,
  kRuntimeLeak,
  kNotSelfContained,
  kUnsupported,
};

struct RuntimePreciseLogEvent {
  std::string component;
  std::string stage;
  std::string message;
  std::optional<uint64_t> target_pc;
  std::optional<unsigned> round;
  std::optional<std::string> detail;
};

enum class RuntimeArtifactStage {
  kFrontierRound,
  kOutputRecoveryRound,
  kOutputRecoveryImportRound,
  kFinalization,
};

enum class FinalStateRecoveryActionKind {
  kRetryExecutableChildImport,
  kRetryTerminalExecutableChild,
  kRetryNativeBoundaryRecovery,
  kKeepModeledPlaceholder,
  kHardReject,
};

enum class FinalStateRecoveryDisposition {
  kPlanned,
  kSkipped,
  kRetriedNoChange,
  kImported,
  kKeptPlaceholder,
  kHardRejected,
};

enum class BoundaryTailRecoveryActionKind {
  kLiftBoundaryContinuation,
  kMaterializeTerminalBoundary,
  kReplayBoundaryAndReclassify,
  kKeepModeledBoundary,
  kHardRejectBoundary,
};

enum class BoundaryTailRecoveryDisposition {
  kPlanned,
  kSkipped,
  kContinuationLifted,
  kMaterializedTerminalBoundary,
  kReclassified,
  kKeptModeledBoundary,
  kHardRejected,
};

enum class FinalTailNodeKind {
  kExecutablePlaceholder,
  kModeledReentryBoundary,
  kTerminalModeledBoundary,
  kTerminalModeledChild,
  kHardRejectedBoundary,
  kHardRejectedExecutable,
  kRetryableBoundary,
};

struct FinalTailGraphNode {
  uint64_t target_pc = 0;
  std::string symbol_name;
  FinalTailNodeKind kind = FinalTailNodeKind::kExecutablePlaceholder;
  std::string detail;
  std::optional<uint64_t> continuation_pc;
};

struct FinalTailGraphEdge {
  std::optional<uint64_t> source_pc;
  std::string source_name;
  uint64_t target_pc = 0;
};

struct FinalTailGraph {
  std::vector<FinalTailGraphNode> nodes;
  std::vector<FinalTailGraphEdge> edges;
};

struct RejectedImportArtifact {
  uint64_t target_pc = 0;
  RecoveryRejectionReason reason = RecoveryRejectionReason::kUnsupported;
  std::string detail;
};

struct ImportDecisionArtifact {
  std::string label;
  uint64_t target_pc = 0;
  ImportEligibility eligibility = ImportEligibility::kRejected;
  RecoveryRejectionReason rejection_reason =
      RecoveryRejectionReason::kUnsupported;
  std::optional<uint64_t> selected_root_pc;
  std::optional<ChildImportClass> import_class;
  std::string proof_summary;
  std::string resolution_summary;
  std::string detail;
  bool imported = false;
};

struct CleanupActionArtifact {
  std::string label;
  bool changed = false;
  std::string detail;
};

struct FinalStateRecoveryAction {
  FinalStateRecoveryActionKind kind =
      FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
  uint64_t target_pc = 0;
  RuntimeArtifactStage source_stage = RuntimeArtifactStage::kFinalization;
  std::string source_label;
  std::string final_state_class;
  std::string reason;
  unsigned retry_budget = 0;
  std::string planned_resolver_path;
  std::string expected_outcome;
};

struct ExecutedRecoveryActionArtifact {
  FinalStateRecoveryActionKind kind =
      FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
  uint64_t target_pc = 0;
  bool attempted = false;
  FinalStateRecoveryDisposition disposition =
      FinalStateRecoveryDisposition::kSkipped;
  std::string detail;
  bool module_changed = false;
};

struct BoundaryTailRecoveryAction {
  BoundaryTailRecoveryActionKind kind =
      BoundaryTailRecoveryActionKind::kKeepModeledBoundary;
  uint64_t target_pc = 0;
  std::optional<uint64_t> continuation_pc;
  std::string source_label;
  std::string reason;
  std::string expected_outcome;
};

struct BoundaryTailRecoveryActionResult {
  BoundaryTailRecoveryActionKind kind =
      BoundaryTailRecoveryActionKind::kKeepModeledBoundary;
  uint64_t target_pc = 0;
  std::optional<uint64_t> continuation_pc;
  bool attempted = false;
  BoundaryTailRecoveryDisposition disposition =
      BoundaryTailRecoveryDisposition::kSkipped;
  std::string detail;
  bool module_changed = false;
};

struct FinalStateRecoveryPlan {
  std::vector<FinalStateRecoveryAction> actions;
};

struct RecoveryQualitySummary {
  bool structurally_closed = false;
  bool functionally_recovered = false;
  bool dispatcher_heavy = false;
  bool dispatcher_shell = false;
  std::vector<uint64_t> modeled_intra_owner_continuations;
  std::vector<uint64_t> lifted_intra_owner_continuations;
  std::vector<uint64_t> modeled_pc_relative_return_thunks;
  std::vector<uint64_t> modeled_controlled_returns;
  std::vector<uint64_t> controlled_return_unresolved;
  std::vector<uint64_t> lifted_controlled_return_continuations;
  std::vector<uint64_t> terminal_modeled_targets;
  std::vector<uint64_t> terminal_modeled_children;
  std::vector<uint64_t> terminal_modeled_boundaries;
  std::vector<uint64_t> modeled_reentry_boundaries;
  std::vector<uint64_t> lifted_boundary_continuations;
  std::vector<std::string> lowering_helper_callees;
  std::vector<std::string> accepted_external_leaf_calls;
  std::vector<uint64_t> hard_rejected_targets;
};

struct RoundArtifactBundle {
  RuntimeArtifactStage stage = RuntimeArtifactStage::kFrontierRound;
  std::string label;
  std::optional<unsigned> round;
  llvm::stable_hash module_fingerprint = 0;
  bool changed = false;
  std::vector<std::string> output_root_names;
  std::vector<uint64_t> executable_placeholder_targets;
  std::vector<uint64_t> native_boundary_targets;
  std::vector<std::string> remill_runtime_callees;
  std::vector<std::string> external_callees;
  std::vector<std::string> lowering_helper_callees;
  std::vector<uint64_t> imported_targets;
  std::vector<RejectedImportArtifact> rejected_imports;
  std::vector<ImportDecisionArtifact> import_decisions;
  std::vector<CleanupActionArtifact> cleanup_actions;
  std::vector<FinalStateRecoveryAction> planned_recovery_actions;
  std::vector<ExecutedRecoveryActionArtifact> executed_recovery_actions;
  std::vector<BoundaryTailRecoveryAction> boundary_recovery_actions;
  std::vector<BoundaryTailRecoveryActionResult> boundary_recovery_results;
  RecoveryQualitySummary recovery_quality;
  std::optional<FinalTailGraph> final_tail_graph;
  std::vector<std::string> notes;
};

struct ChildLiftArtifact {
  uint64_t target_pc = 0;
  std::string ir_text;
  std::string model_text;
  std::optional<uint64_t> selected_root_pc;
  std::string selected_root_name;
  std::string selected_root_kind;
  bool selected_root_was_retargeted = false;
  std::string selected_root_selection_detail;
  bool selected_root_is_trusted_entry = false;
  bool selected_root_is_terminal_only = false;
  bool selected_root_is_terminal_modeled = false;
  bool selected_root_is_self_loop_only = false;
  bool selected_root_has_structural_loop = false;
  bool has_jump_tail = false;
  bool has_local_controlled_return = false;
  bool has_runtime_leak = false;
  bool has_unresolved_dispatch_intrinsics = false;
  bool has_remill_jump = false;
  bool has_remill_function_call = false;
  bool has_pc_relative_return_thunk = false;
  std::vector<uint64_t> modeled_executable_targets;
  std::vector<uint64_t> modeled_boundary_targets;
  std::vector<uint64_t> localized_continuation_targets;
  std::vector<uint64_t> frontier_target_pcs;
  std::optional<uint64_t> jump_tail_continuation_pc;
  std::optional<uint64_t> local_controlled_return_pc;
  std::vector<std::string> closed_slice_function_names;
  std::vector<std::string> reachable_declaration_callees;
  std::vector<std::string> lowering_helper_callees;
  ChildImportClass import_safety = ChildImportClass::kUnsupported;
  RecoveryRejectionReason rejection_reason =
      RecoveryRejectionReason::kUnsupported;
  std::string rejection_detail;
};

struct ChildArtifactPreparationSummary {
  bool parsed = false;
  bool changed = false;
  bool ran_late_closure_canonicalization = false;
  bool ran_post_patch_cleanup = false;
  bool ran_late_cleanup = false;
  std::string detail;
};

struct PreparedChildArtifact {
  ChildLiftArtifact artifact;
  ChildArtifactPreparationSummary summary;
};

struct PreparedBoundaryArtifact {
  ChildLiftArtifact artifact;
  ChildArtifactPreparationSummary summary;
  ChildArtifactLeakKind leak_kind = ChildArtifactLeakKind::kNone;
};

struct BoundaryReplaySummary {
  uint64_t target_pc = 0;
  bool replayed = false;
  std::optional<BoundaryResolutionResult> resolution;
  ChildArtifactLeakKind leak_kind = ChildArtifactLeakKind::kNone;
  std::string detail;
};

struct BoundaryReplayPlan {
  uint64_t target_pc = 0;
  bool enable_gsd = false;
};

struct ChildImportPlan {
  uint64_t target_pc = 0;
  ImportEligibility eligibility = ImportEligibility::kRejected;
  RecoveryRejectionReason rejection_reason =
      RecoveryRejectionReason::kUnsupported;
  std::string rejection_detail;
  llvm::Function *imported_root = nullptr;
  std::optional<uint64_t> selected_root_pc;
  std::optional<ChildImportClass> import_class;
  std::optional<ContinuationProof> proof;
  std::vector<std::string> allowed_declaration_callees;
  std::vector<std::string> lowering_helper_callees;
};

struct ChildArtifactCacheKey {
  uint64_t target_pc = 0;
  bool no_abi = false;
  bool enable_gsd = false;
  bool enable_recovery_mode = false;
  bool dump_virtual_model = false;
  unsigned policy_fingerprint = 2;

  auto tie() const {
    return std::tie(target_pc, no_abi, enable_gsd, enable_recovery_mode,
                    dump_virtual_model, policy_fingerprint);
  }

  bool operator<(const ChildArtifactCacheKey &other) const {
    return tie() < other.tie();
  }
};

struct ChildArtifactCacheEntry {
  ChildLiftArtifact raw_artifact;
  ChildLiftArtifact artifact;
  std::optional<PreparedChildArtifact> prepared_artifact;
  ChildImportPlan last_plan;
  std::optional<ContinuationResolutionResult> resolver_result;
  std::optional<BinaryRegionSnapshot> region_snapshot;
  std::optional<BoundaryResolutionResult> boundary_resolution;
  ChildArtifactLeakKind leak_kind = ChildArtifactLeakKind::kNone;
  bool imported = false;
  bool skipped_child_lift = false;
  std::string proof_summary;
  std::string diagnostics;
};

struct OutputRecoverySummary {
  bool changed = false;
  unsigned noabi_imported_children = 0;
  unsigned abi_imported_vm_enter_children = 0;
  unsigned patched_declared_targets = 0;
  unsigned patched_code_targets = 0;
  unsigned patched_calli_targets = 0;
  unsigned patched_dispatch_targets = 0;
  std::vector<std::string> notes;
  std::vector<RoundArtifactBundle> artifact_bundles;
};

struct OutputRecoveryOptions {
  bool raw_binary = false;
  bool no_abi = false;
  bool use_block_lifting = false;
  bool enable_devirtualization = false;
  bool enable_precise_logs = false;
  bool allow_noabi_postmain_rounds = false;
  bool allow_abi_postmain_rounds = false;
  bool enable_nested_vm_enter_child_import = false;
  unsigned max_vm_enter_child_imports = 1;
  unsigned late_noabi_closure_rounds = 4;
  unsigned max_noabi_executable_child_import_rounds = 4;
  unsigned late_abi_closure_rounds = 4;
};

struct OutputRecoveryCallbacks {
  std::function<void(const RuntimePreciseLogEvent &)> precise_log;
  std::function<void(llvm::StringRef)> run_late_closure_canonicalization;
  std::function<void(llvm::StringRef)> run_post_patch_cleanup;
  std::function<void()> run_final_output_cleanup;
  std::function<void()> annotate_vm_unresolved_continuations;
  std::function<bool(unsigned)> before_noabi_frontier_round;
  std::function<bool(unsigned, const FrontierRoundSummary &)>
      after_noabi_frontier_round;
  std::function<void()> prune_to_defined_output_root_closure;
  std::function<void()> rerun_late_output_root_target_pipeline;
  std::function<void()> sanitize_remaining_poison_native_helper_args;
  std::function<void()> erase_noop_self_recursive_native_calls;
  std::function<bool(FrontierDiscoveryPhase, llvm::StringRef)>
      advance_session_owned_frontier_work;
  std::function<std::optional<ChildLiftArtifact>(uint64_t, bool, bool, bool,
                                                 bool)>
      lift_child_target;
  std::function<ChildImportPlan(uint64_t, const ChildLiftArtifact &,
                                const ChildImportPlan &, llvm::StringRef)>
      import_executable_child;
  std::function<ChildImportPlan(uint64_t, const ChildLiftArtifact &,
                                const ChildImportPlan &, llvm::Function &)>
      import_vm_enter_child;
  std::function<void(uint64_t)> note_imported_target;
  std::function<std::vector<uint64_t>()>
      collect_executable_placeholder_declaration_targets;
  std::function<std::vector<uint64_t>()>
      collect_declared_structural_targets_with_defined_implementations;
  std::function<std::vector<uint64_t>()>
      collect_output_root_constant_code_call_targets;
  std::function<std::vector<uint64_t>()>
      collect_output_root_constant_calli_targets;
  std::function<std::vector<uint64_t>()>
      collect_output_root_constant_dispatch_targets;
  std::function<void(const std::vector<uint64_t> &, llvm::StringRef,
                     llvm::StringRef)>
      patch_constant_inttoptr_calls_to_native;
  std::function<unsigned(const std::vector<uint64_t> &, llvm::StringRef,
                         llvm::StringRef)>
      patch_declared_lifted_or_block_calls_to_defined_targets;
  std::function<unsigned(const std::vector<uint64_t> &, llvm::StringRef,
                         llvm::StringRef)>
      patch_constant_calli_targets_to_direct_calls;
  std::function<unsigned(const std::vector<uint64_t> &, llvm::StringRef,
                         llvm::StringRef)>
      patch_constant_dispatch_targets_to_direct_calls;
  std::function<void(llvm::StringRef, bool)> note_abi_post_cleanup_step;
};

struct FinalizationSummary {
  bool has_protector_report = false;
  ProtectorValidationReport protector_report;
  std::optional<FinalStateRecoveryPlan> final_state_recovery_plan;
  std::optional<RecoveryQualitySummary> recovery_quality;
  std::optional<FinalTailGraph> final_tail_graph;
  std::vector<RoundArtifactBundle> artifact_bundles;
};

struct FinalStateRecoveryRequest {
  bool no_abi = false;
  bool enabled = false;
  bool enable_gsd = false;
};

class DevirtualizationRuntime {
 public:
  explicit DevirtualizationRuntime(DevirtualizationOrchestrator &orchestrator)
      : orchestrator_(orchestrator) {}

  FrontierRoundSummary runFrontierRound(
      llvm::Module &M, BlockLifter &block_lifter,
      IterativeLiftingSession &iterative_session,
      const FrontierCallbacks &callbacks, FrontierDiscoveryPhase phase) const;

  FrontierIterationSummary runFrontierIterations(
      llvm::Module &M, BlockLifter &block_lifter,
      IterativeLiftingSession &iterative_session,
      const FrontierCallbacks &frontier_callbacks, FrontierDiscoveryPhase phase,
      unsigned max_rounds, const FrontierIterationCallbacks &iteration_callbacks,
      const VmEnterChildImportCallbacks *vm_enter_import_callbacks =
          nullptr) const;

  FrontierIterationSummary runPrimaryDevirtualization(
      llvm::Module &M, BlockLifter &block_lifter,
      IterativeLiftingSession &iterative_session,
      const FrontierCallbacks &frontier_callbacks, FrontierDiscoveryPhase phase,
      unsigned max_rounds, const FrontierIterationCallbacks &iteration_callbacks,
      const VmEnterChildImportCallbacks *vm_enter_import_callbacks =
          nullptr) const;

  OutputRecoverySummary runOutputRecovery(
      llvm::Module &M, BlockLifter *block_lifter,
      IterativeLiftingSession *iterative_session,
      const FrontierCallbacks *frontier_callbacks,
      const OutputRecoveryOptions &options,
      const OutputRecoveryCallbacks &callbacks) const;

  ProtectorValidationReport buildValidationReport(const llvm::Module &M) const;

  RecoveryQualitySummary classifyRecoveryQuality(const llvm::Module &M) const;
  FinalTailGraph buildFinalTailGraph(const llvm::Module &M) const;
  bool refineFinalTailGraphWithBoundaryReplay(
      llvm::Module &M, FinalTailGraph &graph,
      const OutputRecoveryCallbacks &callbacks, bool enable_gsd) const;
  bool projectFinalTailGraphIntoAbiModule(llvm::Module &M,
                                          const FinalTailGraph &graph) const;

  FinalizationSummary finalizeOutput(const llvm::Module &M,
                                     bool devirtualization_enabled) const;

  std::optional<FinalStateRecoveryPlan> planFinalStateRecovery(
      const llvm::Module &M, const FinalStateRecoveryRequest &request) const;

  std::optional<RoundArtifactBundle> runFinalStateRecovery(
      llvm::Module &M, const FinalStateRecoveryRequest &request,
      const OutputRecoveryCallbacks &callbacks) const;
  std::optional<RoundArtifactBundle> runBoundaryTailRecovery(
      llvm::Module &M, const FinalStateRecoveryRequest &request,
      const OutputRecoveryCallbacks &callbacks) const;

  const std::vector<RoundArtifactBundle> &roundArtifactBundles() const {
    return round_artifact_bundles_;
  }
  void clearRoundArtifactBundles() const {
    round_artifact_bundles_.clear();
    vm_enter_child_import_plan_cache_.clear();
  }

 private:
  DevirtualizationOrchestrator &orchestrator_;
  mutable std::optional<llvm::stable_hash> child_cache_module_fingerprint_;
  mutable std::map<ChildArtifactCacheKey, ChildArtifactCacheEntry>
      child_artifact_cache_;
  mutable std::map<uint64_t, ChildImportPlan> vm_enter_child_import_plan_cache_;
  mutable std::map<uint64_t, BoundaryResolutionResult> boundary_resolution_cache_;
  mutable std::vector<RoundArtifactBundle> round_artifact_bundles_;
};

bool isLoweringHelperCalleeName(llvm::StringRef name);

const char *toString(FinalStateRecoveryActionKind kind);
const char *toString(FinalStateRecoveryDisposition disposition);
const char *toString(BoundaryTailRecoveryActionKind kind);
const char *toString(BoundaryTailRecoveryDisposition disposition);
const char *toString(FinalTailNodeKind kind);

}  // namespace omill

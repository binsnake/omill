#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>

#include <llvm/ADT/StableHashing.h>

#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Analysis/VirtualModel/Types.h"
#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Devirtualization/ProtectorModel.h"
#include "omill/Omill.h"
#include "omill/Remill/Normalization.h"

namespace llvm {
class Module;
class Function;
}

namespace omill {

class BlockLifter;

enum class DevirtualizationOutputMode {
  kABI,
  kNoABI,
};

enum class DevirtualizationConfidence {
  kLow,
  kMedium,
  kHigh,
};

enum class DevirtualizationEpoch {
  kInitialLiftNormalization,
  kDetectionSeedExtraction,
  kFrontierScheduling,
  kIncrementalBlockLift,
  kNormalizationCacheAdmission,
  kCfgMaterialization,
  kContinuationClosure,
  kAbiOrNoAbiFinalization,
  kFinalInvariantVerification,
};

enum class UnresolvedExitKind {
  kDispatchJump,
  kDispatchCall,
  kProtectedBoundary,
  kUnknownContinuation,
};

enum class ExitCompleteness {
  kComplete,
  kIncomplete,
  kInvalidated,
};

enum class LiftUnitCacheStatus {
  kFresh,
  kReused,
  kInvalidated,
};

enum class VipTrackingStatus {
  kUnknown,
  kResolved,
  kSymbolic,
};

enum class FrontierDiscoveryPhase {
  kUnresolvedOnly,
  kVmUnresolvedContinuations,
  kOutputRootClosure,
  kCombined,
};

enum class FrontierWorkKind {
  kLiftableBlock,
  kIntraOwnerContinuation,
  kBoundaryContinuation,
  kNativeCallBoundary,
  kTerminalBoundary,
  kVmEnterBoundary,
  kUnknownExecutableTarget,
};

enum class FrontierWorkStatus {
  kPending,
  kLifted,
  kClassifiedTerminal,
  kClassifiedNativeExit,
  kClassifiedVmEnter,
  kFailedDecode,
  kFailedLift,
  kSkippedMaterialized,
  kInvalidated,
};

enum class SessionRegionKind {
  kPrimaryRoot,
  kNestedVmEnter,
};

enum class SessionRegionStatus {
  kPending,
  kImported,
  kBlocked,
};

struct DevirtualizationRequest {
  std::vector<uint64_t> root_vas;
  DevirtualizationOutputMode output_mode = DevirtualizationOutputMode::kABI;
  bool deobfuscate = false;
  bool verify_rewrites = false;
  bool force_devirtualize = false;
  bool auto_detect = true;
};

struct DevirtualizationCompatInputs {
  bool requested_block_lift = false;
  bool requested_generic_static = false;
  bool requested_vm_entry_mode = false;
  bool env_generic_static = false;
  bool env_verify_generic_static = false;
  bool env_force_generic_static = false;
  bool no_abi = false;
  bool requested_root_is_export = false;
  bool export_root_has_hidden_entry_seed_exprs = false;
  uint64_t requested_root_rva = 0;
  uint64_t largest_executable_section_size = 0;
  uint64_t executable_section_count = 0;
};

enum class DevirtualizationCompatReason {
  kNone,
  kCompatibilityFlag,
  kFastPlainExportRootFallback,
  kStableLargeExportRootFallback,
  kNoVmLikeCandidates,
  kNoRootLocalDevirtShape,
  kLegacyVmPathSuppressed,
  kPreAbiNoAbiCleanup,
};

enum class DevirtualizationExportRootFallbackMode {
  kNone,
  kFastPlain,
  kStableLarge,
};

struct DevirtualizationDetectionResult {
  bool should_devirtualize = false;
  bool forced = false;
  unsigned unresolved_dispatches = 0;
  unsigned protected_boundaries = 0;
  unsigned vm_entry_boundaries = 0;
  DevirtualizationConfidence confidence = DevirtualizationConfidence::kLow;
  std::vector<std::string> reasons;
  std::vector<uint64_t> seed_roots;
  std::vector<uint64_t> frontier_pcs;
};

struct DevirtualizationEpochSummary {
  DevirtualizationEpoch epoch = DevirtualizationEpoch::kInitialLiftNormalization;
  bool changed = false;
  bool clean = true;
  bool normalization_verifier_clean = true;
  std::string note;
  unsigned units_lifted = 0;
  unsigned units_reused = 0;
  unsigned unresolved_exits_complete = 0;
  unsigned unresolved_exits_incomplete = 0;
  unsigned unresolved_exits_invalidated = 0;
  unsigned normalization_failures = 0;
  unsigned dispatches_materialized = 0;
  unsigned leaked_runtime_artifacts = 0;
  std::vector<std::string> normalization_diagnostics;
  std::vector<std::string> invariant_violations;
};

struct DevirtualizationPolicy {
  bool auto_detect = true;
  bool force_block_lift = true;
  bool force_generic_static = true;
  bool disable_legacy_vm_path = true;
  bool emit_epoch_summaries = true;
  bool enforce_final_invariants = false;
};

struct ExitEvidence {
  std::vector<uint64_t> resolved_targets;
  unsigned predecessor_count = 0;
  std::optional<DevirtualizationEpoch> last_epoch_touched;
  std::string invalidation_reason;
};

struct UnresolvedExitSite {
  UnresolvedExitKind kind = UnresolvedExitKind::kUnknownContinuation;
  ExitCompleteness completeness = ExitCompleteness::kIncomplete;
  std::string owner_function;
  unsigned site_index = 0;
  std::optional<uint64_t> site_pc;
  std::optional<uint64_t> target_pc;
  std::optional<uint64_t> vip_pc;
  std::optional<uint64_t> continuation_vip_pc;
  std::optional<unsigned> continuation_slot_id;
  std::optional<unsigned> continuation_stack_cell_id;
  bool vip_symbolic = false;
  VirtualExitDisposition exit_disposition = VirtualExitDisposition::kUnknown;
  ExitEvidence evidence;
};

struct FrontierWorkItem {
  std::string owner_function;
  unsigned site_index = 0;
  std::optional<uint64_t> site_pc;
  std::optional<uint64_t> target_pc;
  VirtualRootFrontierKind root_frontier_kind =
      VirtualRootFrontierKind::kDispatch;
  std::optional<uint64_t> vip_pc;
  bool vip_symbolic = false;
  std::optional<BoundaryFact> boundary;
  std::optional<ExecutableTargetFact> executable_target;
  ContinuationConfidence continuation_confidence =
      ContinuationConfidence::kWeak;
  ContinuationLiveness continuation_liveness =
      ContinuationLiveness::kUnknown;
  FrontierSchedulingClass scheduling_class =
      FrontierSchedulingClass::kWeakExecutable;
  std::string continuation_rationale;
  FrontierWorkKind kind = FrontierWorkKind::kUnknownExecutableTarget;
  FrontierWorkStatus status = FrontierWorkStatus::kPending;
  unsigned retry_count = 0;
  std::string failure_reason;
  std::string identity;
  bool from_boundary_continuation = false;
};

struct SessionHandlerNode {
  std::string function_name;
  std::optional<uint64_t> entry_va;
  llvm::stable_hash fingerprint = 0;
  bool is_defined = false;
  bool is_output_root = false;
  bool is_closed_root_slice_root = false;
  bool is_specialized = false;
  bool is_dirty = false;
  bool is_preferred_seed = false;
  bool is_initial_seed = false;
  bool is_code_bearing = false;
  std::optional<VirtualHandlerSummary> local_summary;
  std::vector<VirtualArgumentFact> incoming_argument_facts;
  std::vector<VirtualIncomingSlotPhi> incoming_slot_phis;
  std::vector<VirtualSlotFact> incoming_facts;
  std::vector<VirtualSlotFact> outgoing_facts;
  std::vector<VirtualIncomingStackPhi> incoming_stack_phis;
  std::vector<VirtualStackFact> incoming_stack_facts;
  std::vector<VirtualStackFact> outgoing_stack_facts;
  bool stack_memory_budget_exceeded = false;
};

struct SessionEdgeFact {
  std::string identity;
  std::string owner_function;
  unsigned site_index = 0;
  std::optional<uint64_t> site_pc;
  std::optional<uint64_t> target_pc;
  VirtualRootFrontierKind root_frontier_kind =
      VirtualRootFrontierKind::kDispatch;
  std::optional<uint64_t> vip_pc;
  bool vip_symbolic = false;
  std::optional<BoundaryFact> boundary;
  std::optional<ExecutableTargetFact> executable_target;
  std::optional<ContinuationProof> continuation_proof;
  ContinuationConfidence continuation_confidence =
      ContinuationConfidence::kWeak;
  ContinuationLiveness continuation_liveness =
      ContinuationLiveness::kUnknown;
  FrontierSchedulingClass scheduling_class =
      FrontierSchedulingClass::kWeakExecutable;
  std::string continuation_rationale;
  FrontierWorkKind kind = FrontierWorkKind::kUnknownExecutableTarget;
  FrontierWorkStatus status = FrontierWorkStatus::kPending;
  unsigned retry_count = 0;
  std::string failure_reason;
  bool is_dirty = true;
  bool from_unresolved_exit = false;
  bool from_output_root_closure = false;
  bool from_vm_continuation = false;
  bool from_boundary_continuation = false;
};

struct SessionBoundaryFact {
  uint64_t target_pc = 0;
  FrontierWorkKind kind = FrontierWorkKind::kUnknownExecutableTarget;
  std::optional<BoundaryFact> boundary;
  std::optional<std::string> declaration_name;
  bool is_dirty = false;
};

struct SessionRootSlice {
  uint64_t root_va = 0;
  std::string root_function;
  std::vector<std::string> reachable_handler_names;
  std::vector<std::string> frontier_edge_identities;
  bool is_closed = false;
  bool is_dirty = false;
};

struct SessionRegionNode {
  uint64_t entry_pc = 0;
  SessionRegionKind kind = SessionRegionKind::kPrimaryRoot;
  SessionRegionStatus status = SessionRegionStatus::kPending;
  std::optional<uint64_t> parent_entry_pc;
  std::optional<uint64_t> parent_target_pc;
  std::optional<std::string> imported_root_function;
  std::vector<std::string> frontier_edge_identities;
  bool is_dirty = false;
  std::string failure_reason;
};

struct SessionGraphState {
  std::map<std::string, SessionHandlerNode> handler_nodes;
  std::map<std::string, SessionEdgeFact> edge_facts_by_identity;
  std::map<uint64_t, SessionBoundaryFact> boundary_facts_by_target;
  std::map<uint64_t, SessionRootSlice> root_slices_by_va;
  std::map<uint64_t, SessionRegionNode> region_nodes_by_entry_pc;
  std::vector<VirtualStateSlotInfo> canonical_slots;
  std::vector<VirtualStackCellInfo> canonical_stack_cells;
  std::set<std::string> dirty_function_names;
  std::set<std::string> dirty_edge_identities;
  std::set<uint64_t> dirty_root_vas;
};

struct FrontierCallbacks {
  std::function<bool(uint64_t)> is_code_address;
  std::function<bool(uint64_t)> has_defined_target;
  std::function<uint64_t(uint64_t)> normalize_target_pc;
  std::function<bool(uint64_t)> is_executable_target;
  std::function<bool(uint64_t)> is_protected_boundary;
  std::function<bool(uint64_t)> is_exact_call_fallthrough_target;
  std::function<bool(uint64_t)> can_decode_target;
  std::function<bool(uint64_t, uint8_t *, size_t)> read_target_bytes;
  struct DecodedTargetSummary {
    uint64_t pc = 0;
    uint64_t next_pc = 0;
    std::optional<uint64_t> branch_taken_pc;
    std::optional<uint64_t> branch_not_taken_pc;
    bool is_control_flow = false;
    bool is_conditional = false;
    bool is_call = false;
    bool is_return = false;
    bool is_indirect = false;
    bool is_terminal = false;
  };
  std::function<std::optional<DecodedTargetSummary>(uint64_t)>
      decode_target_summary;
};

struct FrontierAdvanceSummary {
  unsigned discovered = 0;
  unsigned pending = 0;
  unsigned lifted = 0;
  unsigned classified_native_exit = 0;
  unsigned classified_terminal = 0;
  unsigned classified_vm_enter = 0;
  unsigned failed_decode = 0;
  unsigned failed_lift = 0;
  unsigned skipped_materialized = 0;
  bool changed = false;
  std::vector<std::string> notes;
};

struct FrontierRoundSummary {
  FrontierAdvanceSummary discover;
  FrontierAdvanceSummary advance;
  bool changed = false;
  bool crashed = false;
};

struct VmEnterChildImportCallbacks {
  bool enabled = false;
  unsigned max_imports = 1;
  std::function<bool(uint64_t, llvm::Function &placeholder,
                     std::string &failure_reason,
                     llvm::Function *&imported_root)>
      try_import_target;
  std::function<void(uint64_t)> on_imported_target;
};

struct VmEnterChildImportSummary {
  unsigned attempted = 0;
  unsigned imported = 0;
  bool changed = false;
  std::vector<std::string> notes;
};

struct FrontierIterationCallbacks {
  std::function<bool(unsigned round)> before_frontier_round;
  std::function<bool(unsigned round, const FrontierRoundSummary &round_summary,
                     const VmEnterChildImportSummary &import_summary)>
      after_frontier_round;
};

struct FrontierIterationSummary {
  unsigned rounds_run = 0;
  unsigned vm_enter_children_imported = 0;
  bool changed = false;
  bool crashed = false;
  std::vector<FrontierRoundSummary> round_summaries;
  std::vector<VmEnterChildImportSummary> import_summaries;
};

struct NormalizedLiftUnitCacheKey {
  uint64_t va = 0;
  bool block_lift = true;
  TargetArch target_arch = TargetArch::kX86_64;

  auto tie() const { return std::tie(va, block_lift, target_arch); }
  bool operator<(const NormalizedLiftUnitCacheKey &other) const {
    return tie() < other.tie();
  }
};

struct NormalizedLiftUnitCacheEntry {
  NormalizedLiftUnitCacheKey key;
  std::string function_name;
  LiftUnitCacheStatus status = LiftUnitCacheStatus::kFresh;
  VipTrackingStatus vip_status = VipTrackingStatus::kUnknown;
  std::optional<uint64_t> vip_pc;
  std::string vip_context_fingerprint;
  bool normalization_gate_passed = false;
  unsigned unresolved_exit_count = 0;
  unsigned live_memory_intrinsics = 0;
  unsigned live_runtime_intrinsics = 0;
  unsigned legacy_dispatch_intrinsics = 0;
  std::vector<std::string> dirty_dependencies;
};

struct DevirtualizationRoundTelemetry {
  unsigned units_lifted = 0;
  unsigned units_reused = 0;
  unsigned unresolved_exits_complete = 0;
  unsigned unresolved_exits_incomplete = 0;
  unsigned unresolved_exits_invalidated = 0;
  unsigned normalization_failures = 0;
  unsigned dispatches_materialized = 0;
  unsigned leaked_runtime_artifacts = 0;
  unsigned dirty_handler_nodes = 0;
  unsigned dirty_edge_facts = 0;
  unsigned dirty_boundary_facts = 0;
  unsigned dirty_root_slices = 0;
  unsigned dirty_regions = 0;
  unsigned rebuilt_boundary_facts = 0;
  unsigned rebuilt_root_slices = 0;
  unsigned rebuilt_regions = 0;
};

struct DevirtualizationSession {
  std::shared_ptr<IterativeLiftingSession> iterative_session;
  SessionGraphState graph;
  std::vector<uint64_t> root_slice;
  std::vector<uint64_t> discovered_continuations;
  std::vector<std::string> discovered_continuation_identities;
  std::vector<uint64_t> late_frontier;
  std::vector<std::string> late_frontier_identities;
  std::vector<uint64_t> discovered_root_pcs;
  std::vector<uint64_t> discovered_frontier_pcs;
  std::vector<std::string> discovered_frontier_identities;
  std::vector<FrontierWorkItem> discovered_frontier_work_items;
  std::vector<FrontierWorkItem> late_frontier_work_items;
  std::map<std::string, FrontierWorkItem> frontier_work_by_identity;
  std::set<uint64_t> attempted_vm_enter_child_import_pcs;
  std::map<uint64_t, std::string> imported_vm_enter_child_roots;
  std::vector<std::string> dirty_functions;
  std::vector<std::string> newly_lifted_functions;
  std::vector<UnresolvedExitSite> unresolved_exits;
  std::map<NormalizedLiftUnitCacheKey, NormalizedLiftUnitCacheEntry>
      normalized_unit_cache;
  ProtectorModel protector_model;
  DevirtualizationRoundTelemetry latest_round;
  std::vector<DevirtualizationEpochSummary> epochs;
};

struct DevirtualizationExecutionPlan {
  bool enable_devirtualization = false;
  bool use_block_lift = false;
  bool use_generic_static_devirtualization = false;
  bool disable_legacy_vm_path = false;
  bool verify_rewrites = false;
  DevirtualizationDetectionResult detection;
};

struct DevirtualizationDriverCompatPlan {
  DevirtualizationExecutionPlan execution;
  bool use_block_lift = false;
  bool generic_static_requested = false;
  bool use_generic_static = false;
  bool verify_generic_static = false;
  bool enable_legacy_vm_mode = false;
  bool suppress_legacy_vm_mode = false;
  DevirtualizationCompatReason legacy_vm_mode_reason =
      DevirtualizationCompatReason::kNone;
  DevirtualizationExportRootFallbackMode export_root_fallback_mode =
      DevirtualizationExportRootFallbackMode::kNone;
  DevirtualizationCompatReason generic_static_reason =
      DevirtualizationCompatReason::kNone;
  bool auto_skip_always_inline = false;
  DevirtualizationCompatReason always_inline_reason =
      DevirtualizationCompatReason::kNone;
  bool root_local_generic_static_devirtualization_shape = false;
  bool use_pre_abi_noabi_cleanup = false;
  DevirtualizationCompatReason pre_abi_cleanup_reason =
      DevirtualizationCompatReason::kNone;
  bool no_abi_mode = false;
};

class DevirtualizationOrchestrator {
 public:
  explicit DevirtualizationOrchestrator(
      DevirtualizationPolicy policy = {},
      std::shared_ptr<IterativeLiftingSession> session = {});

  const DevirtualizationPolicy &policy() const { return policy_; }
  DevirtualizationSession &session() { return session_; }
  const DevirtualizationSession &session() const { return session_; }

  DevirtualizationDetectionResult detect(
      const llvm::Module &M, const DevirtualizationRequest &request,
      const DevirtualizationCompatInputs &compat_inputs = {}) const;
  DevirtualizationExecutionPlan buildExecutionPlan(
      const llvm::Module &M, const DevirtualizationRequest &request,
      const DevirtualizationCompatInputs &compat_inputs = {});
  DevirtualizationDriverCompatPlan buildDriverCompatPlan(
      const llvm::Module &M, const DevirtualizationRequest &request,
      const DevirtualizationCompatInputs &compat_inputs = {});
  void refreshSessionState(const llvm::Module &M);
  void applyExecutionPlan(const DevirtualizationExecutionPlan &plan,
                          PipelineOptions &opts) const;
  void applyDriverCompatPlan(const DevirtualizationDriverCompatPlan &plan,
                             PipelineOptions &opts) const;
  FrontierAdvanceSummary discoverFrontierWork(
      const llvm::Module &M, const FrontierCallbacks &callbacks,
      FrontierDiscoveryPhase phase = FrontierDiscoveryPhase::kCombined);
  bool enqueueBoundaryContinuationWork(
      const llvm::Module &M, const BoundaryFact &boundary,
      llvm::StringRef source_name = {},
      std::optional<uint64_t> source_pc = std::nullopt);
  bool requeueBoundaryEdgesForTarget(const llvm::Module &M, uint64_t target_pc,
                                     llvm::StringRef reason = {});
  FrontierAdvanceSummary advanceFrontierWork(
      llvm::Module &M, BlockLifter &block_lifter,
      IterativeLiftingSession &iterative_session,
      const FrontierCallbacks &callbacks);
  FrontierRoundSummary runFrontierRound(
      llvm::Module &M, BlockLifter &block_lifter,
      IterativeLiftingSession &iterative_session,
      const FrontierCallbacks &callbacks,
      FrontierDiscoveryPhase phase = FrontierDiscoveryPhase::kCombined);
  FrontierIterationSummary runFrontierIterations(
      llvm::Module &M, BlockLifter &block_lifter,
      IterativeLiftingSession &iterative_session,
      const FrontierCallbacks &frontier_callbacks, FrontierDiscoveryPhase phase,
      unsigned max_rounds, const FrontierIterationCallbacks &iteration_callbacks,
      const VmEnterChildImportCallbacks *vm_enter_import_callbacks = nullptr);
  VmEnterChildImportSummary importNestedVmEnterChildren(
      llvm::Module &M, const VmEnterChildImportCallbacks &callbacks);
  bool hasUnstableFrontierState() const;
  bool hasBlockingUnstableFrontierState(const llvm::Module &M) const;
  std::string summarizeFrontierAdvance(
      const FrontierAdvanceSummary &summary) const;
  ProtectorModel buildProtectorModel() const;
  ProtectorValidationReport buildProtectorValidationReport(
      const llvm::Module &M) const;

  std::vector<std::string> collectInvariantViolations(
      const llvm::Module &M, DevirtualizationOutputMode mode) const;
  DevirtualizationEpochSummary summarizeEpoch(
      DevirtualizationEpoch epoch, const llvm::Module &M,
      DevirtualizationOutputMode mode, bool changed,
      std::string note = {}) const;
  void recordEpoch(DevirtualizationEpoch epoch, const llvm::Module &M,
                   DevirtualizationOutputMode mode, bool changed,
                   std::string note = {});

 private:
  DevirtualizationPolicy policy_;
  DevirtualizationSession session_;
};

const char *toString(DevirtualizationConfidence confidence);
const char *toString(DevirtualizationEpoch epoch);
const char *toString(DevirtualizationCompatReason reason);
const char *toString(DevirtualizationExportRootFallbackMode mode);
const char *toString(UnresolvedExitKind kind);
const char *toString(ExitCompleteness completeness);
const char *toString(LiftUnitCacheStatus status);
const char *toString(VipTrackingStatus status);
const char *toString(FrontierDiscoveryPhase phase);
const char *toString(FrontierWorkKind kind);
const char *toString(FrontierWorkStatus status);

void publishSessionGraphProjection(const llvm::Module &M,
                                   const SessionGraphState &state);
const SessionGraphState *findSessionGraphProjection(const llvm::Module &M);
SessionGraphState *findMutableSessionGraphProjection(llvm::Module &M);

}  // namespace omill

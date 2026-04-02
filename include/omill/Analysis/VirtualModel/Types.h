#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace omill {

enum class VirtualBoundaryKind {
  kUnknown,
  kProtectedBoundary,
  kProtectedEntryStub,
};

struct VirtualBoundaryInfo {
  std::string name;
  VirtualBoundaryKind kind = VirtualBoundaryKind::kUnknown;
  std::optional<uint64_t> entry_va;
  std::optional<uint64_t> target_va;
};

struct VirtualStateSlotSummary {
  std::string base_name;
  int64_t offset = 0;
  unsigned width = 0;
  unsigned loads = 0;
  unsigned stores = 0;
  bool from_argument = false;
  bool from_alloca = false;
  std::optional<unsigned> canonical_id;
};

struct VirtualStateSlotInfo {
  unsigned id = 0;
  std::string base_name;
  int64_t offset = 0;
  unsigned width = 0;
  bool from_argument = false;
  bool from_alloca = false;
  std::vector<std::string> handler_names;
};

enum class VirtualExprKind {
  kUnknown,
  kConstant,
  kArgument,
  kStateSlot,
  kStackCell,
  kMemoryRead,
  kZExt,
  kSExt,
  kTrunc,
  kAdd,
  kSub,
  kMul,
  kXor,
  kAnd,
  kOr,
  kShl,
  kLShr,
  kAShr,
  kEq,
  kNe,
  kUlt,
  kUle,
  kUgt,
  kUge,
  kSlt,
  kSle,
  kSgt,
  kSge,
  kSelect,
  kPhi,
};

enum class VirtualSuccessorKind {
  kUnknown,
  kLiftedHandler,
  kLiftedBlock,
  kTraceBlock,
  kProtectedBoundary,
};

enum class VirtualDispatchResolutionSource {
  kUnknown,
  kDirect,
  kOutgoingFacts,
  kRegionOutgoingFacts,
  kIncomingFacts,
  kIncomingPhiFacts,
  kRegionIncomingFacts,
  kRegionIncomingPhiFacts,
  kHelperArgumentSpecialization,
  kPreludeLocalization,
};

enum class VirtualInstructionPointerSourceKind {
  kUnknown,
  kNamedSlot,
  kStackCell,
  kBytecodeRead,
  kDispatchOperand,
};

enum class VirtualExitDisposition {
  kUnknown,
  kStayInVm,
  kVmExitTerminal,
  kVmExitNativeCallReenter,
  kVmExitNativeExecUnknownReturn,
  kVmEnter,
  kNestedVmEnter,
};

enum class VirtualExitStackDeltaKind {
  kUnknown,
  kUnchanged,
  kPlusPointer,
  kPlusDoublePointer,
  kOther,
};

enum class VirtualReturnAddressControlKind {
  kUnknown,
  kPreserved,
  kStateSlotControlled,
  kStackCellControlled,
  kRedirectedConstant,
  kRedirectedSymbolic,
  kClobbered,
};

enum class VirtualStackOwnerKind {
  kUnknown,
  kNativeStackPointer,
  kFramePointerLike,
  kVmStackRootSlot,
  kArgumentRoot,
  kAllocaRoot,
  kDerivedOwner,
};

enum class VirtualStackOwnerTransferKind {
  kUnknown,
  kCopy,
  kAddConst,
  kSubConst,
  kPushStyleAdjust,
  kPopStyleAdjust,
  kSyntheticEntryTransform,
};

struct VirtualValueExpr {
  VirtualExprKind kind = VirtualExprKind::kUnknown;
  unsigned bit_width = 0;
  bool complete = false;
  std::optional<uint64_t> constant;
  std::optional<unsigned> argument_index;
  std::optional<unsigned> slot_id;
  std::optional<std::string> state_base_name;
  std::optional<int64_t> state_offset;
  std::optional<unsigned> stack_cell_id;
  std::optional<int64_t> stack_offset;
  std::vector<VirtualValueExpr> operands;
};

struct VirtualInstructionPointerSummary {
  std::optional<unsigned> slot_id;
  std::optional<unsigned> stack_cell_id;
  VirtualValueExpr expr_before_dispatch;
  VirtualValueExpr expr_after_dispatch;
  std::optional<uint64_t> resolved_pc;
  VirtualInstructionPointerSourceKind source_kind =
      VirtualInstructionPointerSourceKind::kUnknown;
  bool symbolic = false;
};

struct VirtualReturnAddressControlSummary {
  VirtualReturnAddressControlKind kind =
      VirtualReturnAddressControlKind::kUnknown;
  std::optional<uint64_t> original_return_pc;
  std::optional<unsigned> return_slot_id;
  std::optional<unsigned> return_stack_cell_id;
  std::optional<unsigned> return_owner_id;
  VirtualStackOwnerKind return_owner_kind = VirtualStackOwnerKind::kUnknown;
  std::optional<int64_t> return_owner_delta;
  VirtualValueExpr effective_return_expr;
  std::optional<uint64_t> resolved_effective_return_pc;
  bool was_overwritten = false;
  bool suppresses_normal_fallthrough = false;
};

struct VirtualExitSummary {
  VirtualExitDisposition disposition = VirtualExitDisposition::kUnknown;
  std::optional<uint64_t> native_target_pc;
  VirtualInstructionPointerSummary continuation_vip;
  std::optional<uint64_t> continuation_pc;
  VirtualReturnAddressControlSummary return_address_control;
  VirtualExitStackDeltaKind stack_delta_kind =
      VirtualExitStackDeltaKind::kUnknown;
  std::optional<int64_t> stack_delta_bytes;
  bool is_full_exit = false;
  bool is_partial_exit = false;
  bool reenters_vm = false;
  bool corroborated_by_trace = false;
};

struct VirtualDispatchSuccessorSummary {
  VirtualSuccessorKind kind = VirtualSuccessorKind::kUnknown;
  VirtualDispatchResolutionSource resolution_source =
      VirtualDispatchResolutionSource::kUnknown;
  uint64_t target_pc = 0;
  std::optional<uint64_t> canonical_boundary_target_va;
  std::optional<std::string> target_function_name;
  std::optional<std::string> boundary_name;
};

struct VirtualDispatchSummary {
  bool is_jump = false;
  VirtualValueExpr target;
  VirtualValueExpr specialized_target;
  VirtualDispatchResolutionSource specialized_target_source =
      VirtualDispatchResolutionSource::kUnknown;
  VirtualInstructionPointerSummary vip;
  VirtualExitSummary exit;
  std::vector<VirtualDispatchSuccessorSummary> successors;
  std::string unresolved_reason;
};

struct VirtualStateTransferSummary {
  VirtualStateSlotSummary target_slot;
  VirtualValueExpr value;
};

struct VirtualSlotFact {
  unsigned slot_id = 0;
  VirtualValueExpr value;
};

struct VirtualArgumentFact {
  unsigned argument_index = 0;
  VirtualValueExpr value;
};

struct VirtualStackCellSummary {
  std::optional<unsigned> owner_slot_id;
  VirtualStackOwnerKind owner_kind = VirtualStackOwnerKind::kUnknown;
  std::optional<unsigned> derived_from_owner_slot_id;
  std::optional<int64_t> owner_constant_delta;
  std::string base_name;
  int64_t base_offset = 0;
  unsigned base_width = 0;
  int64_t offset = 0;
  unsigned width = 0;
  unsigned loads = 0;
  unsigned stores = 0;
  bool base_from_argument = false;
  bool base_from_alloca = false;
  std::optional<unsigned> canonical_id;
  std::optional<unsigned> canonical_base_slot_id;
};

struct VirtualStackCellInfo {
  unsigned id = 0;
  unsigned base_slot_id = 0;
  unsigned owner_slot_id = 0;
  VirtualStackOwnerKind owner_kind = VirtualStackOwnerKind::kUnknown;
  std::optional<unsigned> derived_from_owner_slot_id;
  std::optional<int64_t> owner_constant_delta;
  std::string base_name;
  int64_t base_offset = 0;
  unsigned base_width = 0;
  int64_t cell_offset = 0;
  unsigned width = 0;
  bool base_from_argument = false;
  bool base_from_alloca = false;
  std::vector<std::string> handler_names;
};

struct VirtualStackOwnerSummary {
  std::optional<unsigned> owner_slot_id;
  std::string base_name;
  int64_t base_offset = 0;
  unsigned base_width = 0;
  VirtualStackOwnerKind kind = VirtualStackOwnerKind::kUnknown;
  std::optional<unsigned> derived_from_owner_slot_id;
  std::optional<int64_t> constant_delta;
  bool is_active_stack_owner = false;
};

struct VirtualStackTransferSummary {
  VirtualStackCellSummary target_cell;
  VirtualValueExpr value;
};

struct VirtualStackOwnerTransferSummary {
  std::optional<unsigned> source_owner_id;
  std::optional<unsigned> target_owner_id;
  VirtualStackOwnerTransferKind kind = VirtualStackOwnerTransferKind::kUnknown;
  std::optional<int64_t> constant_delta;
};

struct VirtualStackFact {
  unsigned cell_id = 0;
  VirtualValueExpr value;
};

enum class VirtualIncomingContextSourceKind {
  kDirectCallsite,
  kEntryPrelude,
  kLocalizedCallee,
};

struct VirtualIncomingContextArm {
  std::string edge_identity;
  VirtualIncomingContextSourceKind source_kind =
      VirtualIncomingContextSourceKind::kDirectCallsite;
  std::string source_handler_name;
  unsigned source_site_index = 0;
  VirtualValueExpr value;
};

struct VirtualIncomingSlotPhi {
  unsigned slot_id = 0;
  VirtualValueExpr merged_value;
  std::vector<VirtualIncomingContextArm> arms;
};

struct VirtualIncomingStackPhi {
  unsigned cell_id = 0;
  VirtualValueExpr merged_value;
  std::vector<VirtualIncomingContextArm> arms;
};

struct VirtualCallSiteSummary {
  bool is_call = false;
  VirtualValueExpr target;
  VirtualValueExpr specialized_target;
  VirtualDispatchResolutionSource specialized_target_source =
      VirtualDispatchResolutionSource::kUnknown;
  std::optional<uint64_t> resolved_target_pc;
  std::optional<uint64_t> recovered_entry_pc;
  std::optional<uint64_t> continuation_pc;
  std::optional<unsigned> continuation_slot_id;
  std::optional<unsigned> continuation_stack_cell_id;
  std::optional<unsigned> continuation_owner_id;
  VirtualStackOwnerKind continuation_owner_kind =
      VirtualStackOwnerKind::kUnknown;
  VirtualReturnAddressControlSummary return_address_control;
  VirtualInstructionPointerSummary vip;
  VirtualExitSummary exit;
  bool is_executable_in_image = false;
  bool is_decodable_entry = false;
  std::optional<std::string> target_function_name;
  std::optional<std::string> recovered_target_function_name;
  std::vector<VirtualSlotFact> return_slot_facts;
  std::vector<VirtualStackFact> return_stack_facts;
  std::string unresolved_reason;
};

struct VirtualHandlerSummary {
  std::string function_name;
  std::optional<uint64_t> entry_va;
  bool is_output_root = false;
  bool is_closed_root_slice_root = false;
  bool is_specialized = false;
  bool is_dirty_seed = false;
  std::optional<uint64_t> specialization_root_va;
  unsigned dispatch_call_count = 0;
  unsigned dispatch_jump_count = 0;
  unsigned protected_boundary_call_count = 0;
  bool is_candidate = false;
  VirtualInstructionPointerSummary canonical_vip;
  std::vector<std::string> called_boundaries;
  std::vector<std::string> direct_callees;
  std::vector<VirtualStateSlotSummary> state_slots;
  std::vector<VirtualStackOwnerSummary> stack_owners;
  std::vector<VirtualStackCellSummary> stack_cells;
  std::vector<VirtualDispatchSummary> dispatches;
  std::vector<VirtualCallSiteSummary> callsites;
  std::vector<VirtualStateTransferSummary> state_transfers;
  std::vector<VirtualStackOwnerTransferSummary> stack_owner_transfers;
  std::vector<VirtualStackTransferSummary> stack_transfers;
  std::vector<unsigned> live_in_slot_ids;
  std::vector<unsigned> written_slot_ids;
  std::vector<unsigned> live_in_stack_cell_ids;
  std::vector<unsigned> written_stack_cell_ids;
  std::vector<VirtualSlotFact> specialization_facts;
  std::vector<VirtualStackFact> specialization_stack_facts;
  std::vector<VirtualArgumentFact> incoming_argument_facts;
  std::vector<VirtualIncomingSlotPhi> incoming_slot_phis;
  std::vector<VirtualSlotFact> incoming_facts;
  std::vector<VirtualSlotFact> outgoing_facts;
  std::vector<VirtualIncomingStackPhi> incoming_stack_phis;
  std::vector<VirtualStackFact> incoming_stack_facts;
  std::vector<VirtualStackFact> outgoing_stack_facts;
  bool has_unsupported_stack_memory = false;
  bool stack_memory_budget_exceeded = false;
};

struct VirtualRegionSummary {
  struct Edge {
    std::string source_handler_name;
    std::string target_handler_name;
  };

  unsigned id = 0;
  std::vector<std::string> boundary_names;
  std::vector<std::string> handler_names;
  std::vector<std::string> entry_handler_names;
  std::vector<std::string> exit_handler_names;
  std::vector<Edge> internal_edges;
  std::vector<unsigned> live_in_slot_ids;
  std::vector<unsigned> written_slot_ids;
  std::vector<unsigned> live_in_stack_cell_ids;
  std::vector<unsigned> written_stack_cell_ids;
  std::vector<VirtualIncomingSlotPhi> incoming_slot_phis;
  std::vector<VirtualSlotFact> incoming_facts;
  std::vector<VirtualSlotFact> outgoing_facts;
  std::vector<VirtualIncomingStackPhi> incoming_stack_phis;
  std::vector<VirtualStackFact> incoming_stack_facts;
  std::vector<VirtualStackFact> outgoing_stack_facts;
};

enum class VirtualRootFrontierKind {
  kDispatch,
  kCall,
};

struct VirtualRootSliceSummary {
  struct FrontierEdge {
    VirtualRootFrontierKind kind = VirtualRootFrontierKind::kDispatch;
    std::string source_handler_name;
    unsigned dispatch_index = 0;
    unsigned callsite_index = 0;
    std::string reason;
    std::optional<uint64_t> target_pc;
    std::optional<uint64_t> canonical_target_va;
    std::optional<std::string> boundary_name;
    std::optional<uint64_t> vip_pc;
    VirtualExitDisposition exit_disposition =
        VirtualExitDisposition::kUnknown;
  };

  uint64_t root_va = 0;
  std::vector<std::string> reachable_handler_names;
  std::vector<FrontierEdge> frontier_edges;
  bool is_closed = false;
  unsigned specialization_count = 0;
};

inline std::optional<uint64_t> effectiveContinuationPc(
    const VirtualCallSiteSummary &callsite) {
  if (callsite.return_address_control.suppresses_normal_fallthrough) {
    return callsite.return_address_control.resolved_effective_return_pc;
  }
  return callsite.continuation_pc;
}

std::string renderVirtualValueExpr(const VirtualValueExpr &expr);
std::string renderVirtualStackOwnerKind(VirtualStackOwnerKind kind);
std::string renderVirtualReturnAddressControlKind(
    VirtualReturnAddressControlKind kind);
std::string renderVirtualReturnAddressControlSummary(
    const VirtualReturnAddressControlSummary &summary);
std::string renderVirtualIncomingContextSourceKind(
    VirtualIncomingContextSourceKind kind);
std::string renderVirtualIncomingSlotPhi(const VirtualIncomingSlotPhi &phi);
std::string renderVirtualIncomingStackPhi(const VirtualIncomingStackPhi &phi);

}  // namespace omill

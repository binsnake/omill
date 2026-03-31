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
  kRegionIncomingFacts,
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

struct VirtualExitSummary {
  VirtualExitDisposition disposition = VirtualExitDisposition::kUnknown;
  std::optional<uint64_t> native_target_pc;
  VirtualInstructionPointerSummary continuation_vip;
  std::optional<uint64_t> continuation_pc;
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
  std::string base_name;
  int64_t base_offset = 0;
  unsigned base_width = 0;
  int64_t cell_offset = 0;
  unsigned width = 0;
  bool base_from_argument = false;
  bool base_from_alloca = false;
  std::vector<std::string> handler_names;
};

struct VirtualStackTransferSummary {
  VirtualStackCellSummary target_cell;
  VirtualValueExpr value;
};

struct VirtualStackFact {
  unsigned cell_id = 0;
  VirtualValueExpr value;
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
  std::vector<VirtualStackCellSummary> stack_cells;
  std::vector<VirtualDispatchSummary> dispatches;
  std::vector<VirtualCallSiteSummary> callsites;
  std::vector<VirtualStateTransferSummary> state_transfers;
  std::vector<VirtualStackTransferSummary> stack_transfers;
  std::vector<unsigned> live_in_slot_ids;
  std::vector<unsigned> written_slot_ids;
  std::vector<unsigned> live_in_stack_cell_ids;
  std::vector<unsigned> written_stack_cell_ids;
  std::vector<VirtualSlotFact> specialization_facts;
  std::vector<VirtualStackFact> specialization_stack_facts;
  std::vector<VirtualArgumentFact> incoming_argument_facts;
  std::vector<VirtualSlotFact> incoming_facts;
  std::vector<VirtualSlotFact> outgoing_facts;
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
  std::vector<VirtualSlotFact> incoming_facts;
  std::vector<VirtualSlotFact> outgoing_facts;
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

std::string renderVirtualValueExpr(const VirtualValueExpr &expr);

}  // namespace omill

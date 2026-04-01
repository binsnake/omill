#pragma once

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VirtualModel/Analysis.h"
#include "omill/Arch/ArchABI.h"

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StableHashing.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Instructions.h>

#include <chrono>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>

namespace llvm {
class BasicBlock;
class DataLayout;
class CallBase;
class Function;
class Module;
class Value;
}

namespace omill::virtual_model::detail {

inline constexpr unsigned kMaxCallsiteLocalizationDepth = 4;

struct CachedHandlerSummaryEntry {
  llvm::stable_hash fingerprint = 0;
  VirtualHandlerSummary summary;
};

struct SlotKey {
  std::string base_name;
  int64_t offset = 0;
  unsigned width = 0;
  bool from_argument = false;
  bool from_alloca = false;

  auto tie() const {
    return std::tie(base_name, offset, width, from_argument, from_alloca);
  }

  bool operator<(const SlotKey &other) const { return tie() < other.tie(); }
};

struct StackCellKey {
  SlotKey base_slot;
  int64_t cell_offset = 0;
  unsigned width = 0;

  auto tie() const { return std::tie(base_slot, cell_offset, width); }

  bool operator<(const StackCellKey &other) const {
    return tie() < other.tie();
  }
};

struct CanonicalStackFactKey {
  unsigned base_slot_id = 0;
  int64_t cell_offset = 0;
  unsigned width = 0;

  auto tie() const { return std::tie(base_slot_id, cell_offset, width); }

  bool operator<(const CanonicalStackFactKey &other) const {
    return tie() < other.tie();
  }
};

struct TrackedStackQuery {
  CanonicalStackFactKey key;
  llvm::SmallVector<CanonicalStackFactKey, 8> variants;
};

struct TrackedStackLookupResult {
  CanonicalStackFactKey key;
  VirtualValueExpr value;
  bool matched_variant = false;
};

struct TrackedFactState {
  std::map<unsigned, VirtualValueExpr> slot_facts;
  std::map<CanonicalStackFactKey, VirtualValueExpr> stack_facts;
  std::map<unsigned, int64_t> stack_base_deltas;
  std::map<unsigned, VirtualValueExpr> materialized_stack_facts;
};

struct CallsiteLocalizedOutgoingFacts {
  std::map<unsigned, VirtualValueExpr> outgoing_slots;
  std::map<unsigned, VirtualValueExpr> outgoing_stack;
  std::map<StackCellKey, VirtualValueExpr> structural_outgoing_stack;
  TrackedFactState tracked_state;
  std::set<unsigned> written_slot_ids;
  std::set<unsigned> written_stack_cell_ids;
  std::set<StackCellKey> written_structural_stack_keys;
  std::set<CanonicalStackFactKey> written_stack_keys;
};

struct CachedOutgoingFactsKey {
  std::string function_name;
  llvm::stable_hash handler_fingerprint = 0;
  llvm::stable_hash incoming_fingerprint = 0;
  llvm::stable_hash incoming_stack_fingerprint = 0;
  llvm::stable_hash incoming_argument_fingerprint = 0;
  llvm::stable_hash callee_outgoing_fingerprint = 0;

  auto tie() const {
    return std::tie(function_name, handler_fingerprint, incoming_fingerprint,
                    incoming_stack_fingerprint, incoming_argument_fingerprint,
                    callee_outgoing_fingerprint);
  }

  bool operator<(const CachedOutgoingFactsKey &other) const {
    return tie() < other.tie();
  }
};

struct CachedOutgoingFactsEntry {
  std::map<unsigned, VirtualValueExpr> outgoing_slots;
  std::map<unsigned, VirtualValueExpr> outgoing_stack;
  bool stack_memory_budget_exceeded = false;
};

struct CachedStableSlotFactEntry {
  VirtualStateSlotSummary slot;
  VirtualValueExpr value;
};

struct CachedStableStackFactEntry {
  VirtualStackCellSummary cell;
  VirtualValueExpr value;
};

struct CachedStableArgumentFactEntry {
  unsigned argument_index = 0;
  VirtualValueExpr value;
};

struct IncomingContextState {
  std::string edge_identity;
  std::vector<VirtualSlotFact> slot_facts;
  std::vector<VirtualStackFact> stack_facts;
};

struct CachedPropagationEntry {
  llvm::stable_hash fingerprint = 0;
  std::vector<CachedStableArgumentFactEntry> incoming_arguments;
  std::vector<VirtualIncomingSlotPhi> incoming_slot_phis;
  std::vector<CachedStableSlotFactEntry> incoming_slots;
  std::vector<CachedStableSlotFactEntry> outgoing_slots;
  std::vector<VirtualIncomingStackPhi> incoming_stack_phis;
  std::vector<CachedStableStackFactEntry> incoming_stack;
  std::vector<CachedStableStackFactEntry> outgoing_stack;
  bool stack_memory_budget_exceeded = false;
};

struct CachedRootSlicesEntry {
  llvm::stable_hash fingerprint = 0;
  std::vector<VirtualRootSliceSummary> root_slices;
};

struct CachedDirectCalleeEntry {
  llvm::stable_hash fingerprint = 0;
  llvm::SmallVector<std::string, 8> callees;
};

using BooleanSlotExprKey = std::tuple<std::string, int64_t, bool, bool>;
using EquivalentStackCellGroupKey =
    std::tuple<std::string, int64_t, unsigned, bool, bool, int64_t, unsigned>;

struct MaterializedStackCellKey {
  unsigned base_slot_id = 0;
  int64_t cell_offset = 0;
  unsigned width = 0;

  auto tie() const { return std::tie(base_slot_id, cell_offset, width); }

  bool operator<(const MaterializedStackCellKey &other) const {
    return tie() < other.tie();
  }
};

struct StackModelContext {
  std::map<SlotKey, unsigned> slot_ids;
  std::map<unsigned, const VirtualStateSlotInfo *> slot_info;
  std::map<StackCellKey, unsigned> stack_cell_ids;
  std::map<unsigned, const VirtualStackCellInfo *> stack_cell_info;
  std::map<EquivalentStackCellGroupKey, llvm::SmallVector<unsigned, 4>>
      equivalent_stack_cell_groups;
  std::map<MaterializedStackCellKey, unsigned> materialized_stack_cell_ids;
};

class StackModelBuilder {
 public:
  explicit StackModelBuilder(VirtualMachineModel &model);

  void internSlot(VirtualStateSlotSummary &slot, llvm::StringRef handler_name);
  void internStackCell(VirtualStackCellSummary &cell,
                       llvm::StringRef handler_name);
  void internExprReferencedSlots(const VirtualValueExpr &expr,
                                 llvm::StringRef handler_name);

  const std::map<SlotKey, unsigned> &slotIds() const { return slot_ids_; }
  const std::map<StackCellKey, unsigned> &stackCellIds() const {
    return stack_cell_ids_;
  }

 private:
  VirtualMachineModel &model_;
  std::map<SlotKey, unsigned> slot_ids_;
  std::map<StackCellKey, unsigned> stack_cell_ids_;
  unsigned next_slot_id_ = 0;
  unsigned next_stack_cell_id_ = 0;
};

struct EntryPreludeCallInfo {
  uint64_t call_pc = 0;
  uint64_t target_pc = 0;
  uint64_t continuation_pc = 0;
};

struct ResolvedCallSiteInfo {
  VirtualValueExpr target_expr;
  VirtualDispatchResolutionSource target_source =
      VirtualDispatchResolutionSource::kUnknown;
  std::optional<uint64_t> target_pc;
  std::optional<uint64_t> continuation_pc;
  std::optional<unsigned> continuation_slot_id;
  std::optional<unsigned> continuation_stack_cell_id;
};

struct LocalCallSiteState {
  std::map<unsigned, VirtualValueExpr> slot_facts;
  std::map<unsigned, VirtualValueExpr> stack_facts;
};

struct CachedModuleHandlerSummaryState {
  llvm::stable_hash module_fingerprint = 0;
  uint64_t module_instance_serial = 0;
  std::map<std::string, CachedHandlerSummaryEntry> summaries;
  CachedRootSlicesEntry root_slices;
  std::map<std::string, CachedDirectCalleeEntry> direct_callees;
  std::map<CachedOutgoingFactsKey, std::optional<CallsiteLocalizedOutgoingFacts>>
      localized_top_level_replays;
  std::map<std::string, std::optional<CallsiteLocalizedOutgoingFacts>>
      localized_callsite_replays;
  std::map<std::string, std::map<unsigned, VirtualValueExpr>>
      specialized_call_arg_replays;
  std::map<std::string, LocalCallSiteState> precall_state_entries;
  std::map<CachedOutgoingFactsKey, CachedOutgoingFactsEntry> outgoing_facts;
  std::map<std::string, CachedPropagationEntry> propagation_entries;
};

struct LocalizedReplayCacheState {
  std::map<CachedOutgoingFactsKey, std::optional<CallsiteLocalizedOutgoingFacts>>
      top_level_entries;
  std::map<std::string, std::optional<CallsiteLocalizedOutgoingFacts>>
      callsite_entries;
  std::map<std::string, std::map<unsigned, VirtualValueExpr>>
      specialized_call_arg_entries;
  std::map<std::string, LocalCallSiteState> precall_state_entries;
  std::map<CachedOutgoingFactsKey, std::optional<CallsiteLocalizedOutgoingFacts>>
      *persistent_top_level_entries = nullptr;
  std::map<std::string, std::optional<CallsiteLocalizedOutgoingFacts>>
      *persistent_callsite_entries = nullptr;
  std::map<std::string, std::map<unsigned, VirtualValueExpr>>
      *persistent_specialized_call_arg_entries = nullptr;
  std::map<std::string, LocalCallSiteState> *persistent_precall_state_entries =
      nullptr;
  const std::map<unsigned, const VirtualStateSlotInfo *> *slot_info = nullptr;
  const std::map<unsigned, const VirtualStackCellInfo *> *stack_cell_info =
      nullptr;
  const std::map<EquivalentStackCellGroupKey, llvm::SmallVector<unsigned, 4>>
      *equivalent_stack_cell_groups = nullptr;
  unsigned top_level_hits = 0;
  unsigned top_level_misses = 0;
  unsigned callsite_hits = 0;
  unsigned callsite_misses = 0;
  unsigned specialized_call_arg_hits = 0;
  unsigned specialized_call_arg_misses = 0;
  unsigned precall_state_hits = 0;
  unsigned precall_state_misses = 0;
  uint64_t top_level_localized_compute_ms = 0;
  uint64_t localized_single_block_compute_ms = 0;
  uint64_t direct_callee_effects_ms = 0;
  uint64_t callsite_localized_compute_ms = 0;
  uint64_t specialized_call_arg_build_ms = 0;
  uint64_t precall_state_build_ms = 0;
  uint64_t direct_callee_key_build_ms = 0;
  uint64_t callsite_key_build_ms = 0;
};

}  // namespace omill::virtual_model::detail

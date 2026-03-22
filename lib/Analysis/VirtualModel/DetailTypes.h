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

struct CallsiteLocalizedOutgoingFacts {
  std::map<unsigned, VirtualValueExpr> outgoing_slots;
  std::map<unsigned, VirtualValueExpr> outgoing_stack;
  std::map<StackCellKey, VirtualValueExpr> structural_outgoing_stack;
  std::set<unsigned> written_slot_ids;
  std::set<unsigned> written_stack_cell_ids;
  std::set<StackCellKey> written_structural_stack_keys;
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

struct CachedPropagationEntry {
  llvm::stable_hash fingerprint = 0;
  std::vector<CachedStableArgumentFactEntry> incoming_arguments;
  std::vector<CachedStableSlotFactEntry> incoming_slots;
  std::vector<CachedStableSlotFactEntry> outgoing_slots;
  std::vector<CachedStableStackFactEntry> incoming_stack;
  std::vector<CachedStableStackFactEntry> outgoing_stack;
  bool stack_memory_budget_exceeded = false;
};

struct CachedDirectCalleeEntry {
  llvm::stable_hash fingerprint = 0;
  llvm::SmallVector<std::string, 8> callees;
};

using BooleanSlotExprKey = std::tuple<std::string, int64_t, bool, bool>;

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
};

struct LocalCallSiteState {
  std::map<unsigned, VirtualValueExpr> slot_facts;
  std::map<unsigned, VirtualValueExpr> stack_facts;
};

struct CachedModuleHandlerSummaryState {
  std::map<std::string, CachedHandlerSummaryEntry> summaries;
  std::map<std::string, CachedDirectCalleeEntry> direct_callees;
  std::map<std::string, std::optional<CallsiteLocalizedOutgoingFacts>>
      localized_top_level_replays;
  std::map<std::string, CachedOutgoingFactsEntry> outgoing_facts;
  std::map<std::string, CachedPropagationEntry> propagation_entries;
};

struct LocalizedReplayCacheState {
  std::map<std::string, std::optional<CallsiteLocalizedOutgoingFacts>>
      top_level_entries;
  unsigned top_level_hits = 0;
  unsigned top_level_misses = 0;
};

}  // namespace omill::virtual_model::detail

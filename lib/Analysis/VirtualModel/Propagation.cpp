#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/Twine.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <chrono>
#include <string>

namespace omill::virtual_model::detail {

static void collectExprSlotIds(const VirtualValueExpr &expr,
                               std::set<unsigned> &ids) {
  if (expr.slot_id.has_value())
    ids.insert(*expr.slot_id);
  for (const auto &operand : expr.operands)
    collectExprSlotIds(operand, ids);
}

static void collectExprStackCellIds(const VirtualValueExpr &expr,
                                    std::set<unsigned> &ids) {
  if (expr.stack_cell_id.has_value())
    ids.insert(*expr.stack_cell_id);
  for (const auto &operand : expr.operands)
    collectExprStackCellIds(operand, ids);
}

static std::set<unsigned> collectReferencedSlotIds(
    llvm::ArrayRef<VirtualValueExpr> exprs) {
  std::set<unsigned> ids;
  for (const auto &expr : exprs)
    collectExprSlotIds(expr, ids);
  return ids;
}

static std::set<unsigned> collectReferencedStackCellIds(
    llvm::ArrayRef<VirtualValueExpr> exprs) {
  std::set<unsigned> ids;
  for (const auto &expr : exprs)
    collectExprStackCellIds(expr, ids);
  return ids;
}

void canonicalizeVirtualState(VirtualMachineModel &model) {
  auto &slots = model.mutableSlots();
  auto &stack_cells = model.mutableStackCells();
  auto &handlers = model.mutableHandlers();
  std::map<SlotKey, unsigned> slot_ids;
  std::map<StackCellKey, unsigned> stack_cell_ids;
  unsigned next_id = 0;
  unsigned next_stack_cell_id = 0;

  auto intern_slot = [&](VirtualStateSlotSummary &slot,
                         llvm::StringRef handler_name) {
    auto key = slotKeyForSummary(slot);
    auto it = slot_ids.find(key);
    if (it == slot_ids.end()) {
      unsigned id = next_id++;
      slot_ids.emplace(key, id);
      slots.push_back(VirtualStateSlotInfo{id, slot.base_name, slot.offset,
                                           slot.width, slot.from_argument,
                                           slot.from_alloca, {}});
      it = slot_ids.find(key);
    }
    slot.canonical_id = it->second;
    auto &info = slots[it->second];
    if (std::find(info.handler_names.begin(), info.handler_names.end(),
                  handler_name.str()) == info.handler_names.end()) {
      info.handler_names.push_back(handler_name.str());
    }
  };

  auto intern_stack_cell = [&](VirtualStackCellSummary &cell,
                               llvm::StringRef handler_name) {
    VirtualStateSlotSummary base_slot;
    base_slot.base_name = cell.base_name;
    base_slot.offset = cell.base_offset;
    base_slot.width = cell.base_width;
    base_slot.from_argument = cell.base_from_argument;
    base_slot.from_alloca = cell.base_from_alloca;
    intern_slot(base_slot, handler_name);
    cell.canonical_base_slot_id = base_slot.canonical_id;

    auto intern_cell_info = [&](VirtualStackCellSummary &summary) {
      auto key = stackCellKeyForSummary(summary);
      auto it = stack_cell_ids.find(key);
      if (it == stack_cell_ids.end()) {
        unsigned id = next_stack_cell_id++;
        stack_cell_ids.emplace(key, id);
        stack_cells.push_back(VirtualStackCellInfo{
            id,
            *summary.canonical_base_slot_id,
            summary.base_name,
            summary.base_offset,
            summary.base_width,
            summary.offset,
            summary.width,
            summary.base_from_argument,
            summary.base_from_alloca,
            {},
        });
        it = stack_cell_ids.find(key);
      }
      auto &info = stack_cells[it->second];
      if (std::find(info.handler_names.begin(), info.handler_names.end(),
                    handler_name.str()) == info.handler_names.end()) {
        info.handler_names.push_back(handler_name.str());
      }
      return it;
    };

    if (cell.offset != 0) {
      VirtualStackCellSummary zero_cell = cell;
      zero_cell.offset = 0;
      zero_cell.canonical_id.reset();
      zero_cell.canonical_base_slot_id = cell.canonical_base_slot_id;
      intern_cell_info(zero_cell);
    }

    auto it = intern_cell_info(cell);
    cell.canonical_id = it->second;
  };

  auto intern_expr_slots = [&](const VirtualValueExpr &expr,
                               llvm::StringRef handler_name) {
    std::vector<VirtualStateSlotSummary> referenced_slots;
    collectExprReferencedStateSlots(expr, referenced_slots);
    for (auto &slot : referenced_slots)
      intern_slot(slot, handler_name);
  };

  for (auto &summary : handlers) {
    for (auto &slot : summary.state_slots)
      intern_slot(slot, summary.function_name);
    for (auto &transfer : summary.state_transfers)
      intern_slot(transfer.target_slot, summary.function_name);
    for (auto &cell : summary.stack_cells)
      intern_stack_cell(cell, summary.function_name);
    for (auto &transfer : summary.stack_transfers)
      intern_stack_cell(transfer.target_cell, summary.function_name);
    for (const auto &dispatch : summary.dispatches)
      intern_expr_slots(dispatch.target, summary.function_name);
    for (const auto &callsite : summary.callsites)
      intern_expr_slots(callsite.target, summary.function_name);
    for (const auto &transfer : summary.state_transfers)
      intern_expr_slots(transfer.value, summary.function_name);
    for (const auto &transfer : summary.stack_transfers)
      intern_expr_slots(transfer.value, summary.function_name);
    for (const auto &fact : summary.specialization_facts)
      intern_expr_slots(fact.value, summary.function_name);
    for (const auto &fact : summary.specialization_stack_facts)
      intern_expr_slots(fact.value, summary.function_name);
    for (const auto &fact : summary.incoming_argument_facts)
      intern_expr_slots(fact.value, summary.function_name);
  }

  for (auto &summary : handlers) {
    for (auto &dispatch : summary.dispatches)
      annotateExprSlots(dispatch.target, slot_ids);
    for (auto &dispatch : summary.dispatches)
      annotateExprStackCells(dispatch.target, stack_cell_ids, slot_ids);
    for (auto &callsite : summary.callsites)
      annotateExprSlots(callsite.target, slot_ids);
    for (auto &callsite : summary.callsites)
      annotateExprStackCells(callsite.target, stack_cell_ids, slot_ids);
    for (auto &transfer : summary.state_transfers)
      annotateExprSlots(transfer.value, slot_ids);
    for (auto &transfer : summary.state_transfers)
      annotateExprStackCells(transfer.value, stack_cell_ids, slot_ids);
    for (auto &transfer : summary.stack_transfers)
      annotateExprSlots(transfer.value, slot_ids);
    for (auto &transfer : summary.stack_transfers)
      annotateExprStackCells(transfer.value, stack_cell_ids, slot_ids);

    std::set<unsigned> live_in_ids;
    std::set<unsigned> written_ids;
    std::set<unsigned> live_in_stack_ids;
    std::set<unsigned> written_stack_ids;
    for (const auto &slot : summary.state_slots) {
      if (!slot.canonical_id.has_value())
        continue;
      if (slot.loads != 0)
        live_in_ids.insert(*slot.canonical_id);
      if (slot.stores != 0)
        written_ids.insert(*slot.canonical_id);
    }
    for (const auto &cell : summary.stack_cells) {
      if (!cell.canonical_id.has_value())
        continue;
      if (cell.loads != 0)
        live_in_stack_ids.insert(*cell.canonical_id);
      if (cell.stores != 0)
        written_stack_ids.insert(*cell.canonical_id);
      if (cell.canonical_base_slot_id.has_value())
        live_in_ids.insert(*cell.canonical_base_slot_id);
    }
    for (const auto &dispatch : summary.dispatches)
      collectExprSlotIds(dispatch.target, live_in_ids);
    for (const auto &dispatch : summary.dispatches)
      collectExprStackCellIds(dispatch.target, live_in_stack_ids);
    for (const auto &callsite : summary.callsites)
      collectExprSlotIds(callsite.target, live_in_ids);
    for (const auto &callsite : summary.callsites)
      collectExprStackCellIds(callsite.target, live_in_stack_ids);
    for (const auto &transfer : summary.state_transfers) {
      if (transfer.target_slot.canonical_id.has_value())
        written_ids.insert(*transfer.target_slot.canonical_id);
      collectExprSlotIds(transfer.value, live_in_ids);
      collectExprStackCellIds(transfer.value, live_in_stack_ids);
    }
    for (const auto &transfer : summary.stack_transfers) {
      if (transfer.target_cell.canonical_id.has_value())
        written_stack_ids.insert(*transfer.target_cell.canonical_id);
      if (transfer.target_cell.canonical_base_slot_id.has_value())
        live_in_ids.insert(*transfer.target_cell.canonical_base_slot_id);
      collectExprSlotIds(transfer.value, live_in_ids);
      collectExprStackCellIds(transfer.value, live_in_stack_ids);
    }
    summary.live_in_slot_ids.assign(live_in_ids.begin(), live_in_ids.end());
    summary.written_slot_ids.assign(written_ids.begin(), written_ids.end());
    summary.live_in_stack_cell_ids.assign(live_in_stack_ids.begin(),
                                          live_in_stack_ids.end());
    summary.written_stack_cell_ids.assign(written_stack_ids.begin(),
                                          written_stack_ids.end());
  }
}

static bool slotFactMapEquals(const std::map<unsigned, VirtualValueExpr> &lhs,
                              const std::map<unsigned, VirtualValueExpr> &rhs) {
  if (lhs.size() != rhs.size())
    return false;
  auto lit = lhs.begin();
  auto rit = rhs.begin();
  for (; lit != lhs.end(); ++lit, ++rit) {
    if (lit->first != rit->first || !exprEquals(lit->second, rit->second))
      return false;
  }
  return true;
}

static bool stackFactMapEquals(const std::map<unsigned, VirtualValueExpr> &lhs,
                               const std::map<unsigned, VirtualValueExpr> &rhs) {
  return slotFactMapEquals(lhs, rhs);
}

struct OutgoingFactsCacheState {
  std::map<std::string, CachedOutgoingFactsEntry> entries;
  unsigned hits = 0;
  unsigned misses = 0;
};

static void appendExprMapCacheKey(
    llvm::raw_ostream &os, const std::map<unsigned, VirtualValueExpr> &facts,
    llvm::StringRef label) {
  os << label << "{";
  for (const auto &[id, value] : facts)
    os << id << "=" << renderVirtualValueExpr(value) << ";";
  os << "}";
}

void propagateVirtualStateFacts(llvm::Module &M, VirtualMachineModel &model,
                                const BinaryMemoryMap &binary_memory,
                                CachedModuleHandlerSummaryState *module_cache) {
  constexpr unsigned kMaxTrackedStackCells = 32;
  vmModelStageDebugLog("propagate: setup-begin");
  auto factSubsetChanged = [](const std::map<unsigned, VirtualValueExpr> &before,
                              const std::map<unsigned, VirtualValueExpr> &after,
                              const llvm::SmallDenseSet<unsigned, 16> &ids) {
    for (unsigned id : ids) {
      auto before_it = before.find(id);
      auto after_it = after.find(id);
      if (before_it == before.end() && after_it == after.end())
        continue;
      if (before_it == before.end() || after_it == after.end() ||
          !exprEquals(before_it->second, after_it->second)) {
        return true;
      }
    }
    return false;
  };

  auto &handlers = model.mutableHandlers();
  const auto slot_ids = buildSlotIdMap(model);
  const auto slot_info = buildSlotInfoMap(model);
  const auto stack_cell_ids = buildStackCellIdMap(model);
  const auto stack_cell_info = buildStackCellInfoMap(model);
  vmModelStageDebugLog("propagate: maps-built handlers=" +
                       llvm::Twine(handlers.size()).str() + " slots=" +
                       llvm::Twine(slot_ids.size()).str() + " stack_cells=" +
                       llvm::Twine(stack_cell_ids.size()).str());
  std::map<std::string, size_t> handler_index;
  for (size_t i = 0; i < handlers.size(); ++i)
    handler_index.emplace(handlers[i].function_name, i);
  std::vector<llvm::SmallVector<size_t, 4>> reverse_caller_indices(
      handlers.size());
  llvm::SmallVector<size_t, 16> handlers_with_direct_callees;
  std::vector<std::optional<EntryPreludeCallInfo>> prelude_infos(
      handlers.size());
  std::vector<llvm::SmallVector<size_t, 2>> reverse_prelude_indices(
      handlers.size());
  llvm::SmallVector<size_t, 16> handlers_with_prelude;
  std::vector<uint8_t> has_prelude(handlers.size(), 0);
  std::vector<uint8_t> has_direct_callees(handlers.size(), 0);
  for (size_t i = 0; i < handlers.size(); ++i) {
    for (const auto &callee_name : handlers[i].direct_callees) {
      auto callee_it = handler_index.find(callee_name);
      if (callee_it == handler_index.end())
        continue;
      reverse_caller_indices[callee_it->second].push_back(i);
    }
    if (!handlers[i].direct_callees.empty()) {
      handlers_with_direct_callees.push_back(i);
      has_direct_callees[i] = 1;
    }
    if (handlers[i].entry_va.has_value()) {
      auto prelude =
          detectEntryPreludeDirectCall(binary_memory, *handlers[i].entry_va);
      if (prelude.has_value()) {
        prelude_infos[i] = prelude;
        handlers_with_prelude.push_back(i);
        has_prelude[i] = 1;
        if (const auto *target_summary =
                lookupHandlerByEntryVA(model, prelude->target_pc)) {
          auto target_it = handler_index.find(target_summary->function_name);
          if (target_it != handler_index.end())
            reverse_prelude_indices[target_it->second].push_back(i);
        }
      }
    }
  }
  vmModelStageDebugLog("propagate: reverse-edges-built direct_callee_handlers=" +
                       llvm::Twine(handlers_with_direct_callees.size()).str() +
                       " prelude_handlers=" +
                       llvm::Twine(handlers_with_prelude.size()).str());

  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_argument_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_stack_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_stack_maps(
      handlers.size());
  std::vector<std::set<unsigned>> dynamic_live_in_slot_ids(handlers.size());
  std::vector<std::set<unsigned>> dynamic_live_in_stack_cell_ids(
      handlers.size());
  std::vector<std::set<unsigned>> forced_incoming_slots(handlers.size());
  std::vector<std::set<unsigned>> forced_incoming_stack_cells(handlers.size());
  LocalizedReplayCacheState localized_replay_cache;
  OutgoingFactsCacheState outgoing_facts_cache;
  auto *persistent_top_level_replay_cache =
      module_cache ? &module_cache->localized_top_level_replays : nullptr;
  auto *persistent_outgoing_facts_cache =
      module_cache ? &module_cache->outgoing_facts : nullptr;
  auto *persistent_propagation_entries =
      module_cache ? &module_cache->propagation_entries : nullptr;
  auto build_handler_outgoing_cache_key =
      [&](size_t handler_index_value, const llvm::Function *handler_fn,
          bool include_callees) {
        std::string key_storage;
        llvm::raw_string_ostream os(key_storage);
        os << handlers[handler_index_value].function_name << "|fp="
           << (handler_fn ? summaryRelevantFunctionFingerprint(*handler_fn) : 0)
           << "|";
        appendExprMapCacheKey(os, incoming_maps[handler_index_value], "in");
        appendExprMapCacheKey(os, incoming_stack_maps[handler_index_value],
                              "stack");
        appendExprMapCacheKey(os, incoming_argument_maps[handler_index_value],
                              "args");
        if (include_callees) {
          os << "callees{";
          for (const auto &callee_name :
               handlers[handler_index_value].direct_callees) {
            auto callee_it = handler_index.find(callee_name);
            if (callee_it == handler_index.end())
              continue;
            os << callee_name << ":";
            appendExprMapCacheKey(os, outgoing_maps[callee_it->second], "out");
            appendExprMapCacheKey(os, outgoing_stack_maps[callee_it->second],
                                  "ostack");
          }
          os << "}";
        }
        os.flush();
        return key_storage;
      };
  std::vector<llvm::stable_hash> handler_fingerprints(handlers.size(), 0);
  std::vector<uint8_t> restored_propagation_state(handlers.size(), 0);

  for (size_t i = 0; i < handlers.size(); ++i) {
    auto *handler_fn = M.getFunction(handlers[i].function_name);
    if (handler_fn)
      handler_fingerprints[i] = summaryRelevantFunctionFingerprint(*handler_fn);
    if (persistent_propagation_entries) {
      auto cache_it =
          persistent_propagation_entries->find(handlers[i].function_name);
      if (cache_it != persistent_propagation_entries->end() &&
          cache_it->second.fingerprint == handler_fingerprints[i]) {
        incoming_argument_maps[i] = restoreStableArgumentFactMap(
            cache_it->second.incoming_arguments, slot_ids, stack_cell_ids);
        incoming_maps[i] = restoreStableSlotFactMap(
            cache_it->second.incoming_slots, slot_ids, stack_cell_ids);
        outgoing_maps[i] = restoreStableSlotFactMap(
            cache_it->second.outgoing_slots, slot_ids, stack_cell_ids);
        incoming_stack_maps[i] = restoreStableStackFactMap(
            cache_it->second.incoming_stack, slot_ids, stack_cell_ids);
        outgoing_stack_maps[i] = restoreStableStackFactMap(
            cache_it->second.outgoing_stack, slot_ids, stack_cell_ids);
        handlers[i].stack_memory_budget_exceeded =
            cache_it->second.stack_memory_budget_exceeded;
        restored_propagation_state[i] = 1;
      }
    }
    for (const auto &fact : handlers[i].specialization_facts) {
      incoming_maps[i][fact.slot_id] = fact.value;
      forced_incoming_slots[i].insert(fact.slot_id);
    }
    for (const auto &fact : handlers[i].specialization_stack_facts) {
      incoming_stack_maps[i][fact.cell_id] = fact.value;
      forced_incoming_stack_cells[i].insert(fact.cell_id);
    }
    if (handlers[i].entry_va.has_value()) {
      incoming_argument_maps[i][1] =
          constantExpr(*handlers[i].entry_va, /*bits=*/64);
    }
  }
  vmModelStageDebugLog("propagate: initial-facts-seeded restored=" +
                       llvm::Twine(std::count(restored_propagation_state.begin(),
                                              restored_propagation_state.end(),
                                              static_cast<uint8_t>(1)))
                           .str());

  llvm::SmallVector<size_t, 32> dirty_handlers;
  llvm::SmallVector<size_t, 32> dirty_call_source_handlers;
  llvm::SmallVector<size_t, 16> dirty_prelude_handlers;
  std::vector<uint8_t> initial_dirty_flags(handlers.size(), 0);
  std::vector<uint8_t> initial_dirty_call_flags(handlers.size(), 0);
  std::vector<uint8_t> initial_dirty_prelude_flags(handlers.size(), 0);
  auto seed_dirty = [&](size_t index) {
    if (index >= handlers.size() || initial_dirty_flags[index])
      return;
    initial_dirty_flags[index] = 1;
    dirty_handlers.push_back(index);
  };
  auto seed_dirty_call_source = [&](size_t index) {
    if (index >= handlers.size() || initial_dirty_call_flags[index] ||
        !has_direct_callees[index]) {
      return;
    }
    initial_dirty_call_flags[index] = 1;
    dirty_call_source_handlers.push_back(index);
  };
  auto seed_dirty_prelude = [&](size_t index) {
    if (index >= handlers.size() || initial_dirty_prelude_flags[index] ||
        !has_prelude[index]) {
      return;
    }
    initial_dirty_prelude_flags[index] = 1;
    dirty_prelude_handlers.push_back(index);
  };
  for (size_t i = 0; i < handlers.size(); ++i) {
    if (restored_propagation_state[i])
      continue;
    seed_dirty(i);
    seed_dirty_call_source(i);
    seed_dirty_prelude(i);
    for (size_t caller_index : reverse_caller_indices[i])
      seed_dirty(caller_index);
    for (size_t prelude_index : reverse_prelude_indices[i])
      seed_dirty_prelude(prelude_index);
  }
  if (dirty_handlers.empty() && !handlers.empty()) {
    for (size_t i = 0; i < handlers.size(); ++i) {
      seed_dirty(i);
      seed_dirty_call_source(i);
      seed_dirty_prelude(i);
    }
  }
  vmModelStageDebugLog("propagate: initial-dirty dirty_handlers=" +
                       llvm::Twine(dirty_handlers.size()).str() +
                       " dirty_call_sources=" +
                       llvm::Twine(dirty_call_source_handlers.size()).str() +
                       " dirty_preludes=" +
                       llvm::Twine(dirty_prelude_handlers.size()).str());
  unsigned iterations = 0;
  while ((!dirty_handlers.empty() || !dirty_call_source_handlers.empty() ||
          !dirty_prelude_handlers.empty()) &&
         iterations++ < 16) {
    const auto iteration_begin = std::chrono::steady_clock::now();
    bool changed = false;
    unsigned localized_attempts = 0;
    unsigned localized_successes = 0;
    unsigned summary_recomputes = 0;
    llvm::SmallVector<size_t, 32> next_dirty_handlers;
    llvm::SmallVector<size_t, 32> next_dirty_call_sources;
    llvm::SmallVector<size_t, 16> next_dirty_preludes;
    std::vector<uint8_t> next_dirty_flags(handlers.size(), 0);
    std::vector<uint8_t> next_dirty_call_flags(handlers.size(), 0);
    std::vector<uint8_t> next_dirty_prelude_flags(handlers.size(), 0);
    auto enqueue_dirty = [&](size_t index) {
      if (index >= handlers.size() || next_dirty_flags[index])
        return;
      next_dirty_flags[index] = 1;
      next_dirty_handlers.push_back(index);
    };
    auto enqueue_dirty_call_source = [&](size_t index) {
      if (index >= handlers.size() || next_dirty_call_flags[index] ||
          !has_direct_callees[index]) {
        return;
      }
      next_dirty_call_flags[index] = 1;
      next_dirty_call_sources.push_back(index);
    };
    auto enqueue_dirty_prelude = [&](size_t index) {
      if (index >= handlers.size() || next_dirty_prelude_flags[index] ||
          !has_prelude[index]) {
        return;
      }
      next_dirty_prelude_flags[index] = 1;
      next_dirty_preludes.push_back(index);
    };
    auto note_incoming_change = [&](size_t target_index, bool arg_change) {
      enqueue_dirty(target_index);
      if (arg_change)
        enqueue_dirty_call_source(target_index);
      enqueue_dirty_prelude(target_index);
    };
    llvm::SmallVector<size_t, 16> active_call_sources(
        dirty_call_source_handlers.begin(), dirty_call_source_handlers.end());
    std::vector<uint8_t> active_call_source_flags(handlers.size(), 0);
    for (size_t i : active_call_sources)
      active_call_source_flags[i] = 1;
    llvm::SmallVector<size_t, 16> active_prelude_handlers(
        dirty_prelude_handlers.begin(), dirty_prelude_handlers.end());
    std::vector<uint8_t> active_prelude_flags(handlers.size(), 0);
    for (size_t i : active_prelude_handlers)
      active_prelude_flags[i] = 1;
    vmModelStageDebugLog("propagate: iteration=" +
                         llvm::Twine(iterations).str() + " phase=begin");

    for (size_t i : dirty_handlers) {
      vmModelStageDebugLog("propagate: iteration=" +
                           llvm::Twine(iterations).str() +
                           " phase=outgoing handler=" +
                           handlers[i].function_name);
      std::map<unsigned, VirtualValueExpr> outgoing_map;
      std::map<unsigned, VirtualValueExpr> outgoing_stack_map;
      bool used_localized = false;
      bool have_cached_outgoing = false;
      bool budget_exceeded = false;
      if (auto *caller_fn = M.getFunction(handlers[i].function_name)) {
        vmModelStageDebugLog("propagate: iteration=" +
                             llvm::Twine(iterations).str() +
                             " phase=outgoing handler=" +
                             handlers[i].function_name + " step=have-function");
        if (!handlers[i].direct_callees.empty() &&
            canComputeLocalizedSingleBlockOutgoingFacts(*caller_fn,
                                                       handlers[i])) {
          vmModelStageDebugLog("propagate: iteration=" +
                               llvm::Twine(iterations).str() +
                               " phase=outgoing handler=" +
                               handlers[i].function_name +
                               " step=localized-eligible callees=" +
                               llvm::Twine(handlers[i].direct_callees.size())
                                   .str());
          ++localized_attempts;
          auto cache_key = build_handler_outgoing_cache_key(
              i, caller_fn, /*include_callees=*/true);
          vmModelStageDebugLog("propagate: iteration=" +
                               llvm::Twine(iterations).str() +
                               " phase=outgoing handler=" +
                               handlers[i].function_name +
                               " step=localized-cache-lookup");
          auto cache_it =
              localized_replay_cache.top_level_entries.find(cache_key);
          std::optional<CallsiteLocalizedOutgoingFacts> localized;
          if (cache_it != localized_replay_cache.top_level_entries.end()) {
            ++localized_replay_cache.top_level_hits;
            localized = cache_it->second;
          } else if (persistent_top_level_replay_cache) {
            auto persistent_it =
                persistent_top_level_replay_cache->find(cache_key);
            if (persistent_it != persistent_top_level_replay_cache->end()) {
              ++localized_replay_cache.top_level_hits;
              localized = persistent_it->second;
              localized_replay_cache.top_level_entries.emplace(cache_key,
                                                               localized);
            }
          }
          if (!localized.has_value() &&
              localized_replay_cache.top_level_entries.find(cache_key) ==
                  localized_replay_cache.top_level_entries.end()) {
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=localized-compute-begin");
            ++localized_replay_cache.top_level_misses;
            llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
            visiting.insert(caller_fn);
            localized = computeLocalizedSingleBlockOutgoingFacts(
                *caller_fn, model, handlers[i], slot_ids, stack_cell_ids,
                incoming_maps[i], incoming_stack_maps[i],
                incoming_argument_maps[i], handler_index, outgoing_maps,
                outgoing_stack_maps, binary_memory, /*depth=*/0, visiting,
                nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                &localized_replay_cache);
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=localized-compute-done success=" +
                                 llvm::Twine(localized.has_value()).str());
            localized_replay_cache.top_level_entries.emplace(
                std::move(cache_key), localized);
            if (persistent_top_level_replay_cache) {
              persistent_top_level_replay_cache->insert_or_assign(
                  cache_key, localized);
            }
          }
          if (localized) {
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=localized-apply");
            ++localized_successes;
            llvm::SmallDenseSet<unsigned, 16> written_slots(
                localized->written_slot_ids.begin(),
                localized->written_slot_ids.end());
            for (const auto &[slot_id, value] : localized->outgoing_slots) {
              if (!written_slots.empty() && !written_slots.count(slot_id))
                continue;
              outgoing_map.emplace(slot_id, value);
            }
            llvm::SmallDenseSet<unsigned, 16> written_stack_cells(
                localized->written_stack_cell_ids.begin(),
                localized->written_stack_cell_ids.end());
            for (const auto &[cell_id, value] : localized->outgoing_stack) {
              if (!written_stack_cells.empty() &&
                  !written_stack_cells.count(cell_id)) {
                continue;
              }
              outgoing_stack_map.emplace(cell_id, value);
            }
            used_localized = true;
          }
        }
        if (!used_localized) {
          vmModelStageDebugLog("propagate: iteration=" +
                               llvm::Twine(iterations).str() +
                               " phase=outgoing handler=" +
                               handlers[i].function_name +
                               " step=summary-path");
          auto cache_key = build_handler_outgoing_cache_key(
              i, caller_fn, /*include_callees=*/true);
          auto cache_it = outgoing_facts_cache.entries.find(cache_key);
          if (cache_it != outgoing_facts_cache.entries.end()) {
            ++outgoing_facts_cache.hits;
            outgoing_map = cache_it->second.outgoing_slots;
            outgoing_stack_map = cache_it->second.outgoing_stack;
            budget_exceeded = cache_it->second.stack_memory_budget_exceeded;
            have_cached_outgoing = true;
          } else if (persistent_outgoing_facts_cache) {
            auto persistent_it =
                persistent_outgoing_facts_cache->find(cache_key);
            if (persistent_it != persistent_outgoing_facts_cache->end()) {
              ++outgoing_facts_cache.hits;
              outgoing_map = persistent_it->second.outgoing_slots;
              outgoing_stack_map = persistent_it->second.outgoing_stack;
              budget_exceeded =
                  persistent_it->second.stack_memory_budget_exceeded;
              outgoing_facts_cache.entries.emplace(cache_key,
                                                  persistent_it->second);
              have_cached_outgoing = true;
            }
          }
          if (!have_cached_outgoing) {
            ++outgoing_facts_cache.misses;
            ++summary_recomputes;
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=compute-outgoing-begin");
            auto new_outgoing =
                computeOutgoingFacts(handlers[i], incoming_maps[i],
                                     incoming_stack_maps[i],
                                     incoming_argument_maps[i]);
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=compute-outgoing-done count=" +
                                 llvm::Twine(new_outgoing.size()).str());
            auto new_outgoing_stack = computeOutgoingStackFacts(
                handlers[i], incoming_maps[i], incoming_stack_maps[i],
                incoming_argument_maps[i]);
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=compute-outgoing-stack-done count=" +
                                 llvm::Twine(new_outgoing_stack.size()).str());
            for (const auto &fact : new_outgoing)
              outgoing_map[fact.slot_id] = fact.value;
            for (const auto &fact : new_outgoing_stack)
              outgoing_stack_map[fact.cell_id] = fact.value;
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=direct-callee-effects-begin");
            applyDirectCalleeEffects(*caller_fn, model, handler_index,
                                     outgoing_maps, outgoing_stack_maps,
                                     incoming_argument_maps[i], outgoing_map,
                                     outgoing_stack_map, binary_memory);
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=direct-callee-effects-done");
            outgoing_stack_map =
                rebaseOutgoingStackFacts(model, outgoing_map, outgoing_stack_map);
            vmModelStageDebugLog("propagate: iteration=" +
                                 llvm::Twine(iterations).str() +
                                 " phase=outgoing handler=" +
                                 handlers[i].function_name +
                                 " step=rebase-outgoing-stack-done count=" +
                                 llvm::Twine(outgoing_stack_map.size()).str());
            budget_exceeded = outgoing_stack_map.size() > kMaxTrackedStackCells;
            if (budget_exceeded) {
              while (outgoing_stack_map.size() > kMaxTrackedStackCells)
                outgoing_stack_map.erase(std::prev(outgoing_stack_map.end()));
            }
            CachedOutgoingFactsEntry cache_entry;
            cache_entry.outgoing_slots = outgoing_map;
            cache_entry.outgoing_stack = outgoing_stack_map;
            cache_entry.stack_memory_budget_exceeded = budget_exceeded;
            outgoing_facts_cache.entries.emplace(cache_key, cache_entry);
            if (persistent_outgoing_facts_cache) {
              persistent_outgoing_facts_cache->insert_or_assign(cache_key,
                                                                cache_entry);
            }
          }
        }
      } else {
        ++summary_recomputes;
        auto new_outgoing =
            computeOutgoingFacts(handlers[i], incoming_maps[i],
                                 incoming_stack_maps[i],
                                 incoming_argument_maps[i]);
        auto new_outgoing_stack = computeOutgoingStackFacts(
            handlers[i], incoming_maps[i], incoming_stack_maps[i],
            incoming_argument_maps[i]);
        for (const auto &fact : new_outgoing)
          outgoing_map[fact.slot_id] = fact.value;
        for (const auto &fact : new_outgoing_stack)
          outgoing_stack_map[fact.cell_id] = fact.value;
      }
      if (!have_cached_outgoing) {
        outgoing_stack_map =
            rebaseOutgoingStackFacts(model, outgoing_map, outgoing_stack_map);
        budget_exceeded = outgoing_stack_map.size() > kMaxTrackedStackCells;
        if (budget_exceeded) {
          while (outgoing_stack_map.size() > kMaxTrackedStackCells)
            outgoing_stack_map.erase(std::prev(outgoing_stack_map.end()));
        }
      }
      if (handlers[i].stack_memory_budget_exceeded != budget_exceeded) {
        handlers[i].stack_memory_budget_exceeded = budget_exceeded;
        changed = true;
      }
      const auto &previous_outgoing_map = outgoing_maps[i];
      const auto &previous_outgoing_stack_map = outgoing_stack_maps[i];
      bool slot_outgoing_changed =
          !slotFactMapEquals(outgoing_map, previous_outgoing_map);
      bool stack_outgoing_changed =
          !stackFactMapEquals(outgoing_stack_map, previous_outgoing_stack_map);
      bool outgoing_changed = slot_outgoing_changed || stack_outgoing_changed;
      llvm::SmallVector<VirtualValueExpr, 8> dynamic_control_exprs;
      dynamic_control_exprs.reserve(handlers[i].dispatches.size() +
                                    handlers[i].callsites.size());
      for (const auto &dispatch : handlers[i].dispatches) {
        auto specialized = specializeExpr(dispatch.target, outgoing_map,
                                          &outgoing_stack_map,
                                          &incoming_argument_maps[i]);
        dynamic_control_exprs.push_back(std::move(specialized));
      }
      for (const auto &callsite : handlers[i].callsites) {
        auto specialized = specializeExpr(callsite.target, outgoing_map,
                                          &outgoing_stack_map,
                                          &incoming_argument_maps[i]);
        dynamic_control_exprs.push_back(std::move(specialized));
      }
      auto referenced_slot_ids = collectReferencedSlotIds(dynamic_control_exprs);
      auto referenced_stack_cell_ids =
          collectReferencedStackCellIds(dynamic_control_exprs);
      bool dynamic_live_in_changed =
          dynamic_live_in_slot_ids[i] != referenced_slot_ids ||
          dynamic_live_in_stack_cell_ids[i] != referenced_stack_cell_ids;
      if (dynamic_live_in_changed) {
        dynamic_live_in_slot_ids[i] = std::move(referenced_slot_ids);
        dynamic_live_in_stack_cell_ids[i] =
            std::move(referenced_stack_cell_ids);
        for (size_t caller_index : reverse_caller_indices[i]) {
          if (active_call_source_flags[caller_index])
            continue;
          active_call_source_flags[caller_index] = 1;
          active_call_sources.push_back(caller_index);
        }
      }
      bool caller_visible_change = false;
      if (outgoing_changed) {
        llvm::SmallDenseSet<unsigned, 16> caller_visible_written_slots(
            handlers[i].written_slot_ids.begin(),
            handlers[i].written_slot_ids.end());
        auto previous_visible_stack_ids =
            rebaseWrittenStackCellIds(model, previous_outgoing_map,
                                      handlers[i].written_stack_cell_ids);
        auto new_visible_stack_ids =
            rebaseWrittenStackCellIds(model, outgoing_map,
                                      handlers[i].written_stack_cell_ids);
        llvm::SmallDenseSet<unsigned, 16> caller_visible_written_stack_cells(
            previous_visible_stack_ids.begin(), previous_visible_stack_ids.end());
        caller_visible_written_stack_cells.insert(new_visible_stack_ids.begin(),
                                                  new_visible_stack_ids.end());
        caller_visible_change =
            factSubsetChanged(previous_outgoing_map, outgoing_map,
                              caller_visible_written_slots) ||
            factSubsetChanged(previous_outgoing_stack_map, outgoing_stack_map,
                              caller_visible_written_stack_cells);
      }
      if (slot_outgoing_changed) {
        outgoing_maps[i] = std::move(outgoing_map);
        changed = true;
      }
      if (stack_outgoing_changed) {
        outgoing_stack_maps[i] = std::move(outgoing_stack_map);
        changed = true;
      }
      if (outgoing_changed) {
        if (!active_call_source_flags[i] && has_direct_callees[i]) {
          active_call_source_flags[i] = 1;
          active_call_sources.push_back(i);
        }
        for (size_t prelude_index : reverse_prelude_indices[i]) {
          if (active_prelude_flags[prelude_index])
            continue;
          active_prelude_flags[prelude_index] = 1;
          active_prelude_handlers.push_back(prelude_index);
        }
        if (caller_visible_change) {
          for (size_t caller_index : reverse_caller_indices[i])
            enqueue_dirty(caller_index);
        }
      }
    }
    vmModelStageDebugLog("propagate: iteration=" +
                         llvm::Twine(iterations).str() +
                         " phase=outgoing-done");
    auto merge_fact = [&](std::map<unsigned, VirtualValueExpr> &dst,
                          unsigned id, const VirtualValueExpr &value,
                          size_t target_index, bool arg_change) {
      auto existing = dst.find(id);
      if (existing == dst.end()) {
        dst.emplace(id, value);
        changed = true;
        note_incoming_change(target_index, arg_change);
        return;
      }
      if (exprEquals(existing->second, value))
        return;
      auto merged = mergeIncomingExpr(existing->second, value);
      if (merged.has_value()) {
        if (!exprEquals(existing->second, *merged)) {
          existing->second = std::move(*merged);
          changed = true;
          note_incoming_change(target_index, arg_change);
        }
        return;
      }
      auto unknown = unknownExpr(existing->second.bit_width
                                     ? existing->second.bit_width
                                     : value.bit_width);
      if (!exprEquals(existing->second, unknown)) {
        existing->second = std::move(unknown);
        changed = true;
        note_incoming_change(target_index, arg_change);
      }
    };

    vmModelStageDebugLog("propagate: iteration=" +
                         llvm::Twine(iterations).str() +
                         " phase=callsite-import-begin");
    for (size_t i : active_call_sources) {
      vmModelStageDebugLog("propagate: iteration=" +
                           llvm::Twine(iterations).str() +
                           " phase=callsite-import handler=" +
                           handlers[i].function_name);
      auto *caller_fn = M.getFunction(handlers[i].function_name);
      if (!caller_fn)
        continue;
      const auto &caller_outgoing = outgoing_maps[i];
      const auto &caller_outgoing_stack = outgoing_stack_maps[i];
      const auto &caller_arguments = incoming_argument_maps[i];
      const auto &dl = M.getDataLayout();

      for (auto &BB : *caller_fn) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          auto callee_it = handler_index.find(callee->getName().str());
          if (callee_it == handler_index.end())
            continue;

          auto &callee_incoming = incoming_maps[callee_it->second];
          auto &callee_incoming_stack = incoming_stack_maps[callee_it->second];
          auto &callee_incoming_args = incoming_argument_maps[callee_it->second];
          const auto &callee_summary = handlers[callee_it->second];
          std::set<unsigned> allowed(callee_summary.live_in_slot_ids.begin(),
                                     callee_summary.live_in_slot_ids.end());
          allowed.insert(dynamic_live_in_slot_ids[callee_it->second].begin(),
                         dynamic_live_in_slot_ids[callee_it->second].end());
          std::set<unsigned> allowed_stack(
              callee_summary.live_in_stack_cell_ids.begin(),
              callee_summary.live_in_stack_cell_ids.end());
          allowed_stack.insert(
              dynamic_live_in_stack_cell_ids[callee_it->second].begin(),
              dynamic_live_in_stack_cell_ids[callee_it->second].end());

          for (const auto &[slot_id, value] : caller_outgoing) {
            if (!allowed.empty() && !allowed.count(slot_id))
              continue;
            if (forced_incoming_slots[callee_it->second].count(slot_id))
              continue;
            if (!isGloballyMergeableStateFactExpr(
                    value, /*allow_arguments=*/false))
              continue;
            merge_fact(callee_incoming, slot_id, value, callee_it->second,
                       /*arg_change=*/false);
          }
          for (const auto &[cell_id, value] : caller_outgoing_stack) {
            if (!allowed_stack.empty() && !allowed_stack.count(cell_id))
              continue;
            if (forced_incoming_stack_cells[callee_it->second].count(cell_id))
              continue;
            if (!isGloballyMergeableStateFactExpr(
                    value, /*allow_arguments=*/false))
              continue;
            merge_fact(callee_incoming_stack, cell_id, value,
                       callee_it->second, /*arg_change=*/false);
          }

          for (unsigned callee_slot_id : callee_summary.live_in_slot_ids) {
            if (forced_incoming_slots[callee_it->second].count(callee_slot_id))
              continue;
            auto info_it = slot_info.find(callee_slot_id);
            if (info_it == slot_info.end())
              continue;
            auto mapped_slot_id = lookupMappedCallerSlotId(
                *call, *info_it->second, slot_ids, dl);
            if (!mapped_slot_id)
              continue;
            auto value_it = caller_outgoing.find(*mapped_slot_id);
            if (value_it == caller_outgoing.end())
              continue;
            if (!isSimpleRemappableFactExpr(value_it->second) ||
                containsCallerLocalAllocaStateExpr(value_it->second))
              continue;
            merge_fact(callee_incoming, callee_slot_id, value_it->second,
                       callee_it->second, /*arg_change=*/false);
          }

          for (unsigned callee_cell_id : callee_summary.live_in_stack_cell_ids) {
            if (forced_incoming_stack_cells[callee_it->second].count(
                    callee_cell_id)) {
              continue;
            }
            auto info_it = stack_cell_info.find(callee_cell_id);
            if (info_it == stack_cell_info.end())
              continue;
            auto mapped_cell_id = lookupMappedCallerStackCellId(
                *call, *info_it->second, slot_ids, stack_cell_ids, dl);
            if (!mapped_cell_id)
              continue;
            auto value_it = caller_outgoing_stack.find(*mapped_cell_id);
            if (value_it == caller_outgoing_stack.end())
              continue;
            if (!isSimpleRemappableFactExpr(value_it->second) ||
                containsCallerLocalAllocaStateExpr(value_it->second))
              continue;
            merge_fact(callee_incoming_stack, callee_cell_id, value_it->second,
                       callee_it->second, /*arg_change=*/false);
          }

          for (unsigned arg_index = 0; arg_index < call->arg_size(); ++arg_index) {
            auto arg_expr = summarizeValueExpr(call->getArgOperand(arg_index), dl);
            annotateExprSlots(arg_expr, slot_ids);
            annotateExprStackCells(arg_expr, stack_cell_ids, slot_ids);
            auto specialized = specializeExpr(arg_expr, caller_outgoing,
                                              &caller_outgoing_stack,
                                              &caller_arguments);
            if (!isGloballyMergeableStateFactExpr(
                    specialized, /*allow_arguments=*/true))
              continue;
            merge_fact(callee_incoming_args, arg_index, specialized,
                       callee_it->second, /*arg_change=*/true);
          }

          if (auto continuation_pc = inferLiftedCallContinuationPc(*call)) {
            auto sp_offset = lookupNativeStackPointerOffset(M);
            if (sp_offset.has_value()) {
              for (const auto &[callee_cell_id, cell] : stack_cell_info) {
                if (!cell->base_from_argument || cell->base_from_alloca)
                  continue;
                auto arg_index = parseArgumentBaseName(cell->base_name);
                if (!arg_index || *arg_index != 0)
                  continue;
                if (cell->base_offset != static_cast<int64_t>(*sp_offset) ||
                    cell->cell_offset != 0) {
                  continue;
                }
                vmModelImportDebugLog("seeded-call-continuation callee=" +
                                      callee->getName().str() + " cell=" +
                                      std::to_string(callee_cell_id) +
                                      " pc=0x" +
                                      llvm::utohexstr(*continuation_pc));
                merge_fact(callee_incoming_stack, callee_cell_id,
                           constantExpr(*continuation_pc, cell->width * 8),
                           callee_it->second, /*arg_change=*/false);
              }
            }
          }
        }
      }
    }
    vmModelStageDebugLog("propagate: iteration=" +
                         llvm::Twine(iterations).str() +
                         " phase=callsite-import-done");

    vmModelStageDebugLog("propagate: iteration=" +
                         llvm::Twine(iterations).str() +
                         " phase=prelude-begin");
    for (size_t i : active_prelude_handlers) {
      vmModelStageDebugLog("propagate: iteration=" +
                           llvm::Twine(iterations).str() +
                           " phase=prelude handler=" +
                           handlers[i].function_name);
      if (!prelude_infos[i].has_value())
        continue;
      if (const auto *target_summary =
              lookupHandlerByEntryVA(model, prelude_infos[i]->target_pc)) {
        llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
        auto localized = computeEntryPreludeCallOutgoingFacts(
            M, model, *target_summary, slot_info, stack_cell_info, slot_ids,
            stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
            incoming_maps[i], incoming_stack_maps[i], incoming_argument_maps[i],
            prelude_infos[i]->continuation_pc, binary_memory, /*depth=*/1,
            visiting);
        if (localized) {
          llvm::SmallDenseSet<unsigned, 16> written_slots(
              target_summary->written_slot_ids.begin(),
              target_summary->written_slot_ids.end());
          auto written_stack_cells = rebaseWrittenStackCellIds(
              model, localized->outgoing_slots,
              target_summary->written_stack_cell_ids);

          for (const auto &[slot_id, value] : localized->outgoing_slots) {
            if (!written_slots.empty() && !written_slots.count(slot_id))
              continue;
            if (forced_incoming_slots[i].count(slot_id))
              continue;
            if (!isGloballyMergeableStateFactExpr(
                    value, /*allow_arguments=*/false)) {
              continue;
            }
            merge_fact(incoming_maps[i], slot_id, value, i,
                       /*arg_change=*/false);
          }
          for (const auto &[cell_id, value] : localized->outgoing_stack) {
            if (!written_stack_cells.empty() &&
                !written_stack_cells.count(cell_id)) {
              continue;
            }
            if (forced_incoming_stack_cells[i].count(cell_id))
              continue;
            if (!isGloballyMergeableStateFactExpr(
                    value, /*allow_arguments=*/false)) {
              continue;
            }
            merge_fact(incoming_stack_maps[i], cell_id, value, i,
                       /*arg_change=*/false);
          }
        }
      }
    }
    vmModelStageDebugLog("propagate: iteration=" +
                         llvm::Twine(iterations).str() +
                         " phase=prelude-done");

    if (!changed)
      break;
    vmModelStageDebugLog(
        "propagate: iteration=" + llvm::Twine(iterations).str() +
        " dirty_handlers=" + llvm::Twine(dirty_handlers.size()).str() +
        " dirty_call_sources=" +
        llvm::Twine(dirty_call_source_handlers.size()).str() +
        " dirty_preludes=" + llvm::Twine(dirty_prelude_handlers.size()).str() +
        " localized_attempts=" + llvm::Twine(localized_attempts).str() +
        " localized_successes=" + llvm::Twine(localized_successes).str() +
        " summary_recomputes=" + llvm::Twine(summary_recomputes).str() +
        " ms=" +
        llvm::Twine(elapsedMilliseconds(iteration_begin,
                                        std::chrono::steady_clock::now()))
            .str());
    dirty_handlers = std::move(next_dirty_handlers);
    dirty_call_source_handlers = std::move(next_dirty_call_sources);
    dirty_prelude_handlers = std::move(next_dirty_preludes);
  }

  for (size_t i = 0; i < handlers.size(); ++i) {
    handlers[i].incoming_argument_facts.clear();
    for (const auto &[arg_index, value] : incoming_argument_maps[i]) {
      handlers[i].incoming_argument_facts.push_back(
          VirtualArgumentFact{arg_index, value});
    }

    handlers[i].incoming_facts.clear();
    for (const auto &[slot_id, value] : incoming_maps[i])
      handlers[i].incoming_facts.push_back(VirtualSlotFact{slot_id, value});

    handlers[i].outgoing_facts.clear();
    for (const auto &[slot_id, value] : outgoing_maps[i])
      handlers[i].outgoing_facts.push_back(VirtualSlotFact{slot_id, value});

    handlers[i].incoming_stack_facts.clear();
    for (const auto &[cell_id, value] : incoming_stack_maps[i])
      handlers[i].incoming_stack_facts.push_back(VirtualStackFact{cell_id, value});

    handlers[i].outgoing_stack_facts.clear();
    for (const auto &[cell_id, value] : outgoing_stack_maps[i])
      handlers[i].outgoing_stack_facts.push_back(VirtualStackFact{cell_id, value});
  }
  if (persistent_propagation_entries) {
    for (size_t i = 0; i < handlers.size(); ++i) {
      CachedPropagationEntry entry;
      entry.fingerprint = handler_fingerprints[i];
      entry.incoming_arguments =
          captureStableArgumentFacts(incoming_argument_maps[i]);
      entry.incoming_slots = captureStableSlotFacts(incoming_maps[i], slot_info);
      entry.outgoing_slots = captureStableSlotFacts(outgoing_maps[i], slot_info);
      entry.incoming_stack =
          captureStableStackFacts(incoming_stack_maps[i], stack_cell_info);
      entry.outgoing_stack =
          captureStableStackFacts(outgoing_stack_maps[i], stack_cell_info);
      entry.stack_memory_budget_exceeded =
          handlers[i].stack_memory_budget_exceeded;
      persistent_propagation_entries->insert_or_assign(handlers[i].function_name,
                                                       std::move(entry));
    }
  }
  vmModelStageDebugLog("propagate: top-level-localized-replay-cache hits=" +
                       llvm::Twine(localized_replay_cache.top_level_hits).str() +
                       " misses=" +
                       llvm::Twine(localized_replay_cache.top_level_misses)
                           .str());
  vmModelStageDebugLog("propagate: outgoing-fact-cache hits=" +
                       llvm::Twine(outgoing_facts_cache.hits).str() +
                       " misses=" +
                       llvm::Twine(outgoing_facts_cache.misses).str());
  vmModelStageDebugLog("propagate: restored-state handlers=" +
                       llvm::Twine(std::count(restored_propagation_state.begin(),
                                              restored_propagation_state.end(),
                                              static_cast<uint8_t>(1)))
                           .str());
}

}  // namespace omill::virtual_model::detail

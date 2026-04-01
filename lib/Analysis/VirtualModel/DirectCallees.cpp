#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

namespace omill::virtual_model::detail {

namespace {

static bool slotSummaryMatchesInfo(const VirtualStateSlotSummary &summary,
                                   const VirtualStateSlotInfo &info) {
  return summary.base_name == info.base_name &&
         summary.offset == info.offset &&
         summary.width == info.width &&
         summary.from_argument == info.from_argument &&
         summary.from_alloca == info.from_alloca;
}

static bool stackCellSummaryMatchesInfo(const VirtualStackCellSummary &summary,
                                        const VirtualStackCellInfo &info) {
  return summary.base_name == info.base_name &&
         summary.base_offset == info.base_offset &&
         summary.base_width == info.base_width &&
         summary.base_from_argument == info.base_from_argument &&
         summary.base_from_alloca == info.base_from_alloca &&
         summary.offset == info.cell_offset && summary.width == info.width;
}

static std::optional<VirtualValueExpr> structurallySpecializeHelperExpr(
    const VirtualValueExpr &expr, llvm::ArrayRef<VirtualSlotFact> slot_facts,
    llvm::ArrayRef<VirtualStackFact> stack_facts,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info) {
  if (expr.kind == VirtualExprKind::kStateSlot) {
    if (auto summary = extractStateSlotSummaryFromExpr(expr, slot_info)) {
      for (const auto &fact : slot_facts) {
        auto it = slot_info.find(fact.slot_id);
        if (it == slot_info.end() ||
            !slotSummaryMatchesInfo(*summary, *it->second)) {
          continue;
        }
        return castExprToBitWidth(fact.value, expr.bit_width);
      }
    }
  } else if (expr.kind == VirtualExprKind::kStackCell) {
    if (auto summary = extractStackCellSummaryFromExpr(expr, exprByteWidth(expr))) {
      for (const auto &fact : stack_facts) {
        auto it = stack_cell_info.find(fact.cell_id);
        if (it == stack_cell_info.end() ||
            !stackCellSummaryMatchesInfo(*summary, *it->second)) {
          continue;
        }
        return castExprToBitWidth(fact.value, expr.bit_width);
      }
    }
  }

  bool changed = false;
  VirtualValueExpr specialized = expr;
  specialized.operands.clear();
  for (const auto &operand : expr.operands) {
    if (auto rewritten = structurallySpecializeHelperExpr(
            operand, slot_facts, stack_facts, slot_info, stack_cell_info)) {
      specialized.operands.push_back(*rewritten);
      changed = true;
    } else {
      specialized.operands.push_back(operand);
    }
  }
  if (!changed)
    return std::nullopt;
  return specialized;
}

static bool exprContainsStackCellBasedOnSlot(
    const VirtualValueExpr &expr, const VirtualStateSlotInfo &slot_info) {
  if (auto summary =
          extractStackCellSummaryFromExpr(expr, exprByteWidth(expr))) {
    if (summary->base_name == slot_info.base_name &&
        summary->base_offset == slot_info.offset &&
        summary->base_width == slot_info.width &&
        summary->base_from_argument == slot_info.from_argument &&
        summary->base_from_alloca == slot_info.from_alloca) {
      return true;
    }
  }
  for (const auto &operand : expr.operands) {
    if (exprContainsStackCellBasedOnSlot(operand, slot_info))
      return true;
  }
  return false;
}

static bool exprContainsSlotId(const VirtualValueExpr &expr, unsigned slot_id) {
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value() &&
      *expr.slot_id == slot_id) {
    return true;
  }
  for (const auto &operand : expr.operands) {
    if (exprContainsSlotId(operand, slot_id))
      return true;
  }
  return false;
}

static std::optional<int64_t> stackBaseDeltaForExpr(const VirtualValueExpr &expr,
                                                    unsigned slot_id) {
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id == slot_id)
    return 0;

  if (expr.kind == VirtualExprKind::kStackCell && expr.slot_id == slot_id &&
      expr.stack_offset.has_value()) {
    return *expr.stack_offset;
  }

  if ((expr.kind == VirtualExprKind::kAdd || expr.kind == VirtualExprKind::kSub) &&
      expr.operands.size() == 2) {
    if (auto nested = stackBaseDeltaForExpr(expr.operands[0], slot_id);
        nested && expr.operands[1].constant.has_value()) {
      int64_t delta = static_cast<int64_t>(*expr.operands[1].constant);
      if (expr.kind == VirtualExprKind::kSub)
        delta = -delta;
      return *nested + delta;
    }
    if (expr.kind == VirtualExprKind::kAdd &&
        expr.operands[0].constant.has_value()) {
      if (auto nested = stackBaseDeltaForExpr(expr.operands[1], slot_id)) {
        return *nested + static_cast<int64_t>(*expr.operands[0].constant);
      }
    }
  }

  return std::nullopt;
}

static std::optional<int64_t> findStackBaseDeltaForSlot(
    const std::map<unsigned, VirtualValueExpr> &slot_facts, unsigned slot_id) {
  std::optional<int64_t> found_delta;
  auto consider_delta = [&](const VirtualValueExpr &value) {
    auto delta = stackBaseDeltaForExpr(value, slot_id);
    if (!delta)
      return true;
    if (!found_delta) {
      found_delta = *delta;
      return true;
    }
    return *found_delta == *delta;
  };

  if (auto it = slot_facts.find(slot_id); it != slot_facts.end()) {
    if (!consider_delta(it->second))
      return std::nullopt;
  }

  for (const auto &[fact_slot_id, value] : slot_facts) {
    if (fact_slot_id == slot_id)
      continue;
    if (!consider_delta(value))
      return std::nullopt;
  }

  return found_delta;
}

static std::optional<VirtualValueExpr> resolveStructuralStackFallback(
    const VirtualValueExpr &expr,
    const std::map<StackCellKey, VirtualValueExpr> &structural_stack_facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing) {
  auto summary = extractStackCellSummaryFromExpr(expr, exprByteWidth(expr));
  if (!summary)
    return std::nullopt;

  std::optional<unsigned> base_slot_id = expr.slot_id;
  if (!base_slot_id) {
    auto slot_it = slot_ids.find(
        SlotKey{summary->base_name, summary->base_offset, summary->base_width,
                summary->base_from_argument, summary->base_from_alloca});
    if (slot_it != slot_ids.end())
      base_slot_id = slot_it->second;
  }
  if (!base_slot_id)
    return std::nullopt;

  auto delta = findStackBaseDeltaForSlot(caller_outgoing, *base_slot_id);
  llvm::SmallVector<int64_t, 5> candidate_offsets{summary->offset};
  if (delta && *delta != 0) {
    candidate_offsets.push_back(summary->offset - *delta);
    candidate_offsets.push_back(summary->offset + *delta);
    candidate_offsets.push_back(summary->offset - (2 * *delta));
    candidate_offsets.push_back(summary->offset + (2 * *delta));
  }

  for (int64_t candidate_offset : candidate_offsets) {
    StackCellKey candidate_key{
        SlotKey{summary->base_name, summary->base_offset, summary->base_width,
                summary->base_from_argument, summary->base_from_alloca},
        candidate_offset, summary->width};
    auto it = structural_stack_facts.find(candidate_key);
    if (it == structural_stack_facts.end())
      continue;
    if (exprEquals(it->second, expr))
      continue;
    return it->second;
  }

  return std::nullopt;
}

static llvm::SmallVector<unsigned, 4> collectRequiredSpecializedCallArgIndices(
    const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info) {
  llvm::SmallVector<unsigned, 4> required_arg_indices;
  for (unsigned slot_id : callee_summary.written_slot_ids) {
    auto info_it = slot_info.find(slot_id);
    if (info_it == slot_info.end())
      continue;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name))
      required_arg_indices.push_back(*arg_index);
  }
  for (unsigned cell_id : callee_summary.written_stack_cell_ids) {
    auto info_it = stack_cell_info.find(cell_id);
    if (info_it == stack_cell_info.end())
      continue;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name))
      required_arg_indices.push_back(*arg_index);
  }
  llvm::sort(required_arg_indices);
  required_arg_indices.erase(
      std::unique(required_arg_indices.begin(), required_arg_indices.end()),
      required_arg_indices.end());
  return required_arg_indices;
}

static void appendRequiredArgIndexCacheKey(llvm::raw_ostream &os,
                                           llvm::ArrayRef<unsigned> arg_indices) {
  if (arg_indices.empty())
    return;
  os << "|required_args=";
  for (unsigned arg_index : arg_indices)
    os << arg_index << ',';
}

static void collectReferencedArgumentIds(const VirtualValueExpr &expr,
                                        llvm::SmallDenseSet<unsigned, 8> &ids) {
  if (expr.kind == VirtualExprKind::kArgument && expr.argument_index.has_value())
    ids.insert(*expr.argument_index);
  for (const auto &operand : expr.operands)
    collectReferencedArgumentIds(operand, ids);
}

static llvm::SmallVector<unsigned, 4> collectLocalizedReplayArgumentIndices(
    const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info) {
  llvm::SmallDenseSet<unsigned, 8> arg_indices;
  for (const auto &fact : callee_summary.incoming_argument_facts)
    arg_indices.insert(fact.argument_index);
  for (unsigned slot_id : callee_summary.live_in_slot_ids) {
    auto info_it = slot_info.find(slot_id);
    if (info_it == slot_info.end())
      continue;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name))
      arg_indices.insert(*arg_index);
  }
  for (unsigned cell_id : callee_summary.live_in_stack_cell_ids) {
    auto info_it = stack_cell_info.find(cell_id);
    if (info_it == stack_cell_info.end())
      continue;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name))
      arg_indices.insert(*arg_index);
  }
  for (const auto &dispatch : callee_summary.dispatches)
    collectReferencedArgumentIds(dispatch.target, arg_indices);
  for (const auto &callsite : callee_summary.callsites)
    collectReferencedArgumentIds(callsite.target, arg_indices);
  for (const auto &transfer : callee_summary.state_transfers)
    collectReferencedArgumentIds(transfer.value, arg_indices);
  for (const auto &transfer : callee_summary.stack_transfers)
    collectReferencedArgumentIds(transfer.value, arg_indices);

  llvm::SmallVector<unsigned, 4> requested_arg_indices(arg_indices.begin(),
                                                       arg_indices.end());
  llvm::sort(requested_arg_indices);
  return requested_arg_indices;
}

static bool containsSortedId(llvm::ArrayRef<unsigned> ids, unsigned id) {
  return std::binary_search(ids.begin(), ids.end(), id);
}

static bool hasNonCanonicalStructuralStackTransfer(
    const VirtualHandlerSummary &summary) {
  return llvm::any_of(summary.stack_transfers,
                      [](const VirtualStackTransferSummary &transfer) {
                        return !transfer.target_cell.canonical_id.has_value();
                      });
}

static bool leafDirectCalleeMayAffectRelevantOutputs(
    llvm::CallBase &call, const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl, llvm::ArrayRef<unsigned> relevant_slot_ids,
    llvm::ArrayRef<unsigned> relevant_stack_cell_ids) {
  if (relevant_slot_ids.empty() && relevant_stack_cell_ids.empty())
    return true;
  if (hasNonCanonicalStructuralStackTransfer(callee_summary))
    return true;

  for (unsigned slot_id : callee_summary.written_slot_ids) {
    if (containsSortedId(relevant_slot_ids, slot_id))
      return true;
    auto info_it = slot_info.find(slot_id);
    if (info_it == slot_info.end())
      continue;
    auto mapped_slot_id =
        lookupMappedCallerSlotId(call, *info_it->second, slot_ids, dl);
    if (mapped_slot_id && containsSortedId(relevant_slot_ids, *mapped_slot_id))
      return true;
  }

  for (unsigned cell_id : callee_summary.written_stack_cell_ids) {
    if (containsSortedId(relevant_stack_cell_ids, cell_id))
      return true;
    auto info_it = stack_cell_info.find(cell_id);
    if (info_it == stack_cell_info.end())
      continue;
    auto mapped_cell_id = lookupMappedCallerStackCellId(
        call, *info_it->second, slot_ids, stack_cell_ids, dl);
    if (mapped_cell_id &&
        containsSortedId(relevant_stack_cell_ids, *mapped_cell_id)) {
      return true;
    }
  }

  return false;
}

static void appendRelevantSlotFactMapCacheKey(
    llvm::raw_ostream &os, const std::map<unsigned, VirtualValueExpr> &facts,
    llvm::StringRef label, const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info) {
  llvm::SmallDenseSet<unsigned, 16> relevant_ids(
      callee_summary.live_in_slot_ids.begin(),
      callee_summary.live_in_slot_ids.end());
  os << label << "{";
  for (const auto &[id, value] : facts) {
    bool include = relevant_ids.count(id) != 0;
    if (!include) {
      auto info_it = slot_info.find(id);
      include = info_it != slot_info.end() && info_it->second->from_argument;
    }
    if (!include)
      continue;
    os << id << "=" << renderVirtualValueExpr(value) << ";";
  }
  os << "}";
}

static void appendRelevantStackFactMapCacheKey(
    llvm::raw_ostream &os, const std::map<unsigned, VirtualValueExpr> &facts,
    llvm::StringRef label, const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info) {
  llvm::SmallDenseSet<unsigned, 16> relevant_ids(
      callee_summary.live_in_stack_cell_ids.begin(),
      callee_summary.live_in_stack_cell_ids.end());
  os << label << "{";
  for (const auto &[id, value] : facts) {
    bool include = relevant_ids.count(id) != 0;
    if (!include) {
      auto info_it = stack_cell_info.find(id);
      include =
          info_it != stack_cell_info.end() && info_it->second->base_from_argument;
    }
    if (!include)
      continue;
    os << id << "=" << renderVirtualValueExpr(value) << ";";
  }
  os << "}";
}

static void appendRelevantArgumentFactMapCacheKey(
    llvm::raw_ostream &os, const std::map<unsigned, VirtualValueExpr> &facts,
    llvm::StringRef label, llvm::ArrayRef<unsigned> relevant_arg_indices) {
  os << label << "{";
  for (const auto &[id, value] : facts) {
    if (!std::binary_search(relevant_arg_indices.begin(),
                            relevant_arg_indices.end(), id)) {
      continue;
    }
    os << id << "=" << renderVirtualValueExpr(value) << ";";
  }
  os << "}";
}

static void appendStructuralStackMapCacheKey(
    llvm::raw_ostream &os,
    const std::map<StackCellKey, VirtualValueExpr> &facts,
    llvm::StringRef label) {
  os << label << "{";
  for (const auto &[key, value] : facts) {
    os << key.base_slot.base_name << ":" << key.base_slot.offset << ":"
       << key.base_slot.width << ":" << key.base_slot.from_argument << ":"
       << key.base_slot.from_alloca << ":" << key.cell_offset << ":"
       << key.width << "=" << renderVirtualValueExpr(value) << ";";
  }
  os << "}";
}

static unsigned callsiteOrdinal(const llvm::CallBase &call) {
  unsigned ordinal = 0;
  for (const auto &BB : *call.getFunction()) {
    for (const auto &I : BB) {
      auto *other_call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!other_call)
        continue;
      if (other_call == &call)
        return ordinal;
      ++ordinal;
    }
  }
  return ordinal;
}

static std::string buildDirectCalleeLocalizedReplayCacheKey(
    const llvm::CallBase &call, const llvm::Function &callee_fn,
    const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    llvm::ArrayRef<unsigned> relevant_arg_indices,
    const std::map<StackCellKey, VirtualValueExpr>
        &caller_structural_outgoing_stack,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts,
    unsigned depth) {
  std::string key_storage;
  llvm::raw_string_ostream os(key_storage);
  os << "dc:" << call.getFunction()->getName() << "#"
     << callsiteOrdinal(call) << "->" << callee_fn.getName() << "|fp="
     << summaryRelevantFunctionFingerprint(callee_fn) << "|depth=" << depth
     << "|";
  appendRelevantSlotFactMapCacheKey(os, caller_outgoing, "caller_out",
                                    callee_summary, slot_info);
  appendRelevantStackFactMapCacheKey(os, caller_outgoing_stack, "caller_stack",
                                     callee_summary, stack_cell_info);
  appendRelevantArgumentFactMapCacheKey(os, caller_argument_map, "caller_args",
                                        relevant_arg_indices);
  appendStructuralStackMapCacheKey(os, caller_structural_outgoing_stack,
                                   "caller_struct");
  if (fallback_caller_stack_facts)
    appendRelevantStackFactMapCacheKey(os, *fallback_caller_stack_facts,
                                       "fallback_stack", callee_summary,
                                       stack_cell_info);
  if (fallback_caller_slot_facts)
    appendRelevantSlotFactMapCacheKey(os, *fallback_caller_slot_facts,
                                      "fallback_slot", callee_summary,
                                      slot_info);
  if (fallback_caller_structural_stack_facts) {
    appendStructuralStackMapCacheKey(os, *fallback_caller_structural_stack_facts,
                                     "fallback_struct");
  }
  os.flush();
  return key_storage;
}

}  // namespace

bool applySingleDirectCalleeEffects(
    llvm::Function &caller_fn, llvm::CallBase &call,
    const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    std::map<StackCellKey, VirtualValueExpr> &caller_structural_outgoing_stack,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const llvm::DataLayout &dl, const BinaryMemoryMap &binary_memory,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts,
    LocalizedReplayCacheState *localized_replay_cache,
    llvm::ArrayRef<unsigned> relevant_caller_slot_ids,
    llvm::ArrayRef<unsigned> relevant_caller_stack_cell_ids) {
  auto *callee = call.getCalledFunction();
  if (!callee)
    return false;

  auto callee_it = handler_index.find(callee->getName().str());
  if (callee_it == handler_index.end())
    return false;

  const auto &callee_summary = model.handlers()[callee_it->second];
  vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                       " callee=" + callee->getName().str() +
                       " step=begin");
  if (callee_summary.direct_callees.empty() && callee_summary.callsites.empty() &&
      !leafDirectCalleeMayAffectRelevantOutputs(
          call, callee_summary, slot_info, stack_cell_info, slot_ids,
          stack_cell_ids, dl, relevant_caller_slot_ids,
          relevant_caller_stack_cell_ids)) {
    vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                         " callee=" + callee->getName().str() +
                         " step=skip-irrelevant-leaf");
    return true;
  }
  const bool cacheable_localized =
      localized_replay_cache && callee_summary.direct_callees.empty() &&
      callee_summary.callsites.empty();
  auto localized_cache_arg_indices = collectLocalizedReplayArgumentIndices(
      callee_summary, slot_info, stack_cell_info);
  std::optional<CallsiteLocalizedOutgoingFacts> localized_outgoing;
  bool have_cached_localized = false;
  std::string localized_cache_key;
  if (cacheable_localized) {
    const auto key_begin = std::chrono::steady_clock::now();
    localized_cache_key = buildDirectCalleeLocalizedReplayCacheKey(
        call, *callee, callee_summary, slot_info, stack_cell_info,
        caller_outgoing, caller_outgoing_stack, caller_argument_map,
        localized_cache_arg_indices, caller_structural_outgoing_stack,
        fallback_caller_structural_stack_facts, fallback_caller_stack_facts,
        fallback_caller_slot_facts, depth);
    if (localized_replay_cache) {
      localized_replay_cache->direct_callee_key_build_ms += elapsedMilliseconds(
          key_begin, std::chrono::steady_clock::now());
    }
    auto cache_it =
        localized_replay_cache->callsite_entries.find(localized_cache_key);
    if (cache_it != localized_replay_cache->callsite_entries.end()) {
      ++localized_replay_cache->callsite_hits;
      localized_outgoing = cache_it->second;
      have_cached_localized = true;
    } else if (localized_replay_cache->persistent_callsite_entries) {
      auto persistent_it = localized_replay_cache->persistent_callsite_entries
                               ->find(localized_cache_key);
      if (persistent_it !=
          localized_replay_cache->persistent_callsite_entries->end()) {
        ++localized_replay_cache->callsite_hits;
        localized_outgoing = persistent_it->second;
        localized_replay_cache->callsite_entries.emplace(localized_cache_key,
                                                         localized_outgoing);
        have_cached_localized = true;
      }
    }
  }
  const auto native_sp_offset = nativeStackPointerOffsetForValue(&call);
  auto required_specialized_arg_indices = collectRequiredSpecializedCallArgIndices(
      callee_summary, slot_info, stack_cell_info);
  std::optional<LocalCallSiteState> precomputed_local_call_state;
  std::string precall_state_cache_key;
  auto ensure_localized_cache_key = [&]() {
    if (!localized_replay_cache || !localized_cache_key.empty())
      return;
    const auto key_begin = std::chrono::steady_clock::now();
    localized_cache_key = buildDirectCalleeLocalizedReplayCacheKey(
        call, *callee, callee_summary, slot_info, stack_cell_info,
        caller_outgoing, caller_outgoing_stack, caller_argument_map,
        localized_cache_arg_indices, caller_structural_outgoing_stack,
        fallback_caller_structural_stack_facts, fallback_caller_stack_facts,
        fallback_caller_slot_facts, depth);
    localized_replay_cache->direct_callee_key_build_ms += elapsedMilliseconds(
        key_begin, std::chrono::steady_clock::now());
  };
  auto tryLoadPrecallState = [&]() -> bool {
    if (!localized_replay_cache || !native_sp_offset.has_value())
      return false;
    ensure_localized_cache_key();
    if (localized_cache_key.empty())
      return false;
    precall_state_cache_key = "precall|" + localized_cache_key;
    auto cache_it =
        localized_replay_cache->precall_state_entries.find(precall_state_cache_key);
    if (cache_it != localized_replay_cache->precall_state_entries.end()) {
      ++localized_replay_cache->precall_state_hits;
      precomputed_local_call_state = cache_it->second;
      return true;
    }
    if (localized_replay_cache->persistent_precall_state_entries) {
      auto persistent_it =
          localized_replay_cache->persistent_precall_state_entries->find(
              precall_state_cache_key);
      if (persistent_it !=
          localized_replay_cache->persistent_precall_state_entries->end()) {
        ++localized_replay_cache->precall_state_hits;
        precomputed_local_call_state = persistent_it->second;
        localized_replay_cache->precall_state_entries.emplace(
            precall_state_cache_key, *precomputed_local_call_state);
        return true;
      }
    }
    ++localized_replay_cache->precall_state_misses;
    return false;
  };
  auto buildAndCachePrecallState = [&]() {
    if (precomputed_local_call_state)
      return;
    const auto precall_begin = std::chrono::steady_clock::now();
    precomputed_local_call_state = computeLocalFactsBeforeCall(
        call, dl, slot_ids, stack_cell_ids, caller_outgoing,
        caller_outgoing_stack, caller_argument_map);
    if (!localized_replay_cache)
      return;
    localized_replay_cache->precall_state_build_ms +=
        elapsedMilliseconds(precall_begin, std::chrono::steady_clock::now());
    ensure_localized_cache_key();
    if (localized_cache_key.empty())
      return;
    if (precall_state_cache_key.empty())
      precall_state_cache_key = "precall|" + localized_cache_key;
    localized_replay_cache->precall_state_entries.emplace(
        precall_state_cache_key, *precomputed_local_call_state);
    if (localized_replay_cache->persistent_precall_state_entries) {
      localized_replay_cache->persistent_precall_state_entries->insert_or_assign(
          precall_state_cache_key, *precomputed_local_call_state);
    }
  };
  tryLoadPrecallState();
  std::map<unsigned, VirtualValueExpr> specialized_call_args;
  bool have_cached_specialized_call_args = false;
  std::string specialized_call_args_cache_key;
  if (localized_replay_cache && !required_specialized_arg_indices.empty()) {
    ensure_localized_cache_key();
    specialized_call_args_cache_key = "args|" + localized_cache_key;
    llvm::raw_string_ostream os(specialized_call_args_cache_key);
    appendRequiredArgIndexCacheKey(os, required_specialized_arg_indices);
    os.flush();
    auto cache_it = localized_replay_cache->specialized_call_arg_entries.find(
        specialized_call_args_cache_key);
    if (cache_it != localized_replay_cache->specialized_call_arg_entries.end()) {
      ++localized_replay_cache->specialized_call_arg_hits;
      specialized_call_args = cache_it->second;
      have_cached_specialized_call_args = true;
    } else if (localized_replay_cache->persistent_specialized_call_arg_entries) {
      auto persistent_it =
          localized_replay_cache->persistent_specialized_call_arg_entries->find(
              specialized_call_args_cache_key);
      if (persistent_it !=
          localized_replay_cache->persistent_specialized_call_arg_entries
              ->end()) {
        ++localized_replay_cache->specialized_call_arg_hits;
        specialized_call_args = persistent_it->second;
        localized_replay_cache->specialized_call_arg_entries.emplace(
            specialized_call_args_cache_key, specialized_call_args);
        have_cached_specialized_call_args = true;
      }
    }
  }
  if (!have_cached_specialized_call_args &&
      !required_specialized_arg_indices.empty()) {
    if (localized_replay_cache)
      ++localized_replay_cache->specialized_call_arg_misses;
    const auto specialized_args_begin = std::chrono::steady_clock::now();
    specialized_call_args = [&]() {
      if (native_sp_offset.has_value()) {
        buildAndCachePrecallState();
        return buildSpecializedCallArgumentMap(
            call, dl, slot_ids, stack_cell_ids,
            precomputed_local_call_state->slot_facts,
            precomputed_local_call_state->stack_facts, caller_argument_map,
            required_specialized_arg_indices);
      }
      return buildSpecializedCallArgumentMap(
          call, dl, slot_ids, stack_cell_ids, caller_outgoing,
          caller_outgoing_stack, caller_argument_map,
          required_specialized_arg_indices);
    }();
    if (localized_replay_cache) {
      localized_replay_cache->specialized_call_arg_build_ms +=
          elapsedMilliseconds(specialized_args_begin,
                              std::chrono::steady_clock::now());
    }
    if (localized_replay_cache) {
      localized_replay_cache->specialized_call_arg_entries.emplace(
          specialized_call_args_cache_key, specialized_call_args);
      if (localized_replay_cache->persistent_specialized_call_arg_entries) {
        localized_replay_cache->persistent_specialized_call_arg_entries
            ->insert_or_assign(specialized_call_args_cache_key,
                               specialized_call_args);
      }
    }
  }
  llvm::SmallDenseSet<unsigned, 16> written_slots(
      callee_summary.written_slot_ids.begin(),
      callee_summary.written_slot_ids.end());
  if (!have_cached_localized) {
    ensure_localized_cache_key();
    if (native_sp_offset.has_value() && !precomputed_local_call_state) {
      buildAndCachePrecallState();
    }
    if (cacheable_localized)
      ++localized_replay_cache->callsite_misses;
    const auto localized_begin = std::chrono::steady_clock::now();
    localized_outgoing = computeCallsiteLocalizedOutgoingFacts(
        call, model, callee_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
        caller_outgoing, caller_outgoing_stack, caller_argument_map,
        binary_memory, depth + 1, visiting, &caller_structural_outgoing_stack,
        fallback_caller_stack_facts, fallback_caller_slot_facts,
        fallback_caller_structural_stack_facts, localized_replay_cache,
        precomputed_local_call_state ? &*precomputed_local_call_state : nullptr,
        localized_cache_key);
    if (localized_replay_cache) {
      localized_replay_cache->callsite_localized_compute_ms +=
          elapsedMilliseconds(localized_begin, std::chrono::steady_clock::now());
    }
    if (cacheable_localized) {
      localized_replay_cache->callsite_entries.emplace(localized_cache_key,
                                                       localized_outgoing);
      if (localized_replay_cache->persistent_callsite_entries) {
        localized_replay_cache->persistent_callsite_entries->insert_or_assign(
            localized_cache_key, localized_outgoing);
      }
    }
  }
  vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                       " callee=" + callee->getName().str() +
                       " step=localized-callsite-done success=" +
                       llvm::Twine(localized_outgoing.has_value()).str());
  if (localized_outgoing) {
    vmModelImportDebugLog("callsite-local summary call=" +
                          callee->getName().str() + " slots=" +
                          std::to_string(localized_outgoing->outgoing_slots.size()) +
                          " stack=" +
                          std::to_string(localized_outgoing->outgoing_stack.size()) +
                          " structural=" +
                          std::to_string(
                              localized_outgoing->structural_outgoing_stack.size()));
  }
  const auto &callee_outgoing_map =
      localized_outgoing ? localized_outgoing->outgoing_slots
                         : outgoing_maps[callee_it->second];
  const auto &callee_outgoing_stack_map =
      localized_outgoing ? localized_outgoing->outgoing_stack
                         : outgoing_stack_maps[callee_it->second];
  if (localized_outgoing) {
    vmModelImportDebugLog("callsite-local effects call=" +
                          callee->getName().str());
    written_slots = llvm::SmallDenseSet<unsigned, 16>(
        localized_outgoing->written_slot_ids.begin(),
        localized_outgoing->written_slot_ids.end());
  }
  llvm::SmallDenseSet<unsigned, 16> written_stack_cells;
  if (localized_outgoing) {
    written_stack_cells = llvm::SmallDenseSet<unsigned, 16>(
        localized_outgoing->written_stack_cell_ids.begin(),
        localized_outgoing->written_stack_cell_ids.end());
  } else {
    written_stack_cells = rebaseWrittenStackCellIds(
        model, callee_outgoing_map, callee_summary.written_stack_cell_ids);
  }

  auto materializeStructuralStackFact =
      [&](const StackCellKey &key, const VirtualValueExpr &value) {
        auto mapped_cell_it = stack_cell_ids.find(key);
        if (mapped_cell_it == stack_cell_ids.end())
          return;
        auto existing = caller_outgoing_stack.find(mapped_cell_it->second);
        if (existing != caller_outgoing_stack.end() &&
            exprEquals(existing->second, value)) {
          return;
        }
        vmModelImportDebugLog("stack-import after call=" +
                              callee->getName().str() + " expr=" +
                              renderVirtualValueExpr(value) + " cell=" +
                              std::to_string(mapped_cell_it->second));
        caller_outgoing_stack[mapped_cell_it->second] = value;
      };

  for (const auto &[callee_slot_id, callee_value] : callee_outgoing_map) {
    if (!written_slots.empty() && !written_slots.count(callee_slot_id))
      continue;
    auto slot_info_it = slot_info.find(callee_slot_id);
    if (slot_info_it == slot_info.end())
      continue;
    std::optional<unsigned> mapped_slot_id;
    if (auto arg_index = parseArgumentBaseName(slot_info_it->second->base_name);
        !mapped_slot_id && arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStateSlotSummary mapped_slot = *actual_slot;
          mapped_slot.offset += slot_info_it->second->offset;
          mapped_slot.width = slot_info_it->second->width;
          mapped_slot_id = lookupSlotIdForSummary(mapped_slot, slot_ids);
        }
      }
    }
    if (!mapped_slot_id) {
      mapped_slot_id =
          lookupMappedCallerSlotId(call, *slot_info_it->second, slot_ids, dl);
    }
    if (!mapped_slot_id)
      continue;
    if (!relevant_caller_slot_ids.empty() &&
        !containsSortedId(relevant_caller_slot_ids, *mapped_slot_id)) {
      continue;
    }

    auto remapped =
        remapCalleeExprToCaller(callee_value, call, slot_info, stack_cell_info,
                                slot_ids, stack_cell_ids, dl);
    vmModelImportDebugLog("slot-import before call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(callee_value) +
                          " remapped=" + renderVirtualValueExpr(remapped));
    auto effective_caller_outgoing_stack =
        rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack);
    auto effective_slot_facts = slotFactsForMap(caller_outgoing);
    auto effective_stack_facts = stackFactsForMap(effective_caller_outgoing_stack);
    auto tracked_caller_state = buildTrackedFactState(
        model, caller_outgoing, effective_caller_outgoing_stack,
        &caller_structural_outgoing_stack);
    auto specialized =
        localized_outgoing
            ? normalizeLocalizedExprForCaller(
                  callee_value, caller_fn, slot_ids, stack_cell_ids,
                  caller_outgoing, effective_caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map)
            : normalizeImportedExprForCaller(
                  callee_value, call, slot_info, stack_cell_info, slot_ids,
                  stack_cell_ids, dl, caller_outgoing,
                  effective_caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map);
    if (localized_outgoing && specialized.has_value() &&
        containsArgumentExpr(*specialized)) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing,
              effective_caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
          specialized = std::move(remapped);
      }
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         isUnknownLikeExpr(*specialized) ||
         !isBoundedLocalizedTransferExpr(*specialized)) &&
        isBoundedLocalizedTransferExpr(remapped)) {
      specialized = remapped;
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         isUnknownLikeExpr(*specialized) ||
         !isBoundedLocalizedTransferExpr(*specialized))) {
      specialized = remapped;
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         (specialized.has_value() &&
          (isUnknownLikeExpr(*specialized) ||
           !isBoundedLocalizedTransferExpr(*specialized))))) {
      if (auto imported = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing,
              effective_caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
        if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
            !isBoundedLocalizedTransferExpr(*specialized)) {
          if (!isUnknownLikeExpr(*imported) &&
              isBoundedLocalizedTransferExpr(*imported)) {
            specialized = std::move(imported);
          }
        }
      }
    }
    if (specialized.has_value() &&
        (containsStackCellExpr(*specialized) || containsStateSlotExpr(*specialized))) {
      if (auto structural = structurallySpecializeHelperExpr(
              *specialized, effective_slot_facts, effective_stack_facts,
              slot_info, stack_cell_info)) {
        specialized = std::move(structural);
      }
    }
    if (specialized.has_value()) {
      auto tracked_resolved = resolveTrackedStackExpr(
          model, tracked_caller_state, *specialized, slot_ids, stack_cell_ids);
      if (!exprEquals(tracked_resolved, *specialized))
        specialized = std::move(tracked_resolved);
    }
    if (localized_outgoing &&
        (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
         !isBoundedLocalizedTransferExpr(*specialized)) &&
        isBoundedLocalizedTransferExpr(remapped)) {
      specialized = remapped;
    }
    if (specialized.has_value() && containsStackCellExpr(*specialized)) {
      if (specialized->kind == VirtualExprKind::kStackCell) {
        if (auto structural = resolveStructuralStackFallback(
                *specialized, caller_structural_outgoing_stack, slot_ids,
                caller_outgoing)) {
          vmModelImportDebugLog("slot-import structural-fallback call=" +
                                callee->getName().str() + " expr=" +
                                renderVirtualValueExpr(*specialized) +
                                " resolved=" +
                                renderVirtualValueExpr(*structural));
          specialized = std::move(structural);
        }
      }
      auto mapped_slot_info_it = slot_info.find(*mapped_slot_id);
      if (mapped_slot_info_it != slot_info.end() &&
          (exprContainsStackCellBasedOnSlot(*specialized,
                                            *mapped_slot_info_it->second) ||
           exprContainsSlotId(remapped, *mapped_slot_id))) {
        specialized = remapped;
      }
    }
    bool acceptable =
        specialized.has_value() &&
        (localized_outgoing ? isBoundedLocalizedTransferExpr(*specialized)
                            : isBoundedStateProvenanceExpr(*specialized));
    if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
        !acceptable) {
      if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
          !acceptable) {
        std::string reason = !specialized.has_value()
                                 ? "no-specialized"
                                 : (isUnknownLikeExpr(*specialized) ? "unknown"
                                                                    : "unbounded");
        vmModelImportDebugLog("slot-import skip call=" +
                              callee->getName().str() + " reason=" + reason +
                              " expr=" + renderVirtualValueExpr(callee_value) +
                              " specialized=" +
                              (specialized.has_value()
                                   ? renderVirtualValueExpr(*specialized)
                                   : std::string("<none>")));
      }
      continue;
    }
    auto existing = caller_outgoing.find(*mapped_slot_id);
    if (existing != caller_outgoing.end() &&
        !exprEquals(existing->second, *specialized) &&
        isIdentitySlotExpr(*specialized, *mapped_slot_id)) {
      continue;
    }
    if (existing != caller_outgoing.end() &&
        !exprEquals(existing->second, *specialized) &&
        containsStackCellExpr(*specialized)) {
      if (auto existing_delta =
              stackBaseDeltaForExpr(existing->second, *mapped_slot_id);
          existing_delta) {
        vmModelImportDebugLog("slot-import keep-existing call=" +
                              callee->getName().str() + " slot=" +
                              std::to_string(*mapped_slot_id) + " existing=" +
                              renderVirtualValueExpr(existing->second) +
                              " specialized=" +
                              renderVirtualValueExpr(*specialized));
        continue;
      }
    }
    vmModelImportDebugLog("slot-import after call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(*specialized) +
                          " mapped_slot=" +
                          std::to_string(*mapped_slot_id) + "(" +
                          slot_info.at(*mapped_slot_id)->base_name + "+" +
                          std::to_string(slot_info.at(*mapped_slot_id)->offset) +
                          ")");
    unsigned mapped_bits =
        slot_info.at(*mapped_slot_id)->width
            ? (slot_info.at(*mapped_slot_id)->width * 8u)
            : 0u;
    unsigned callee_bits =
        slot_info_it->second->width ? (slot_info_it->second->width * 8u) : 0u;
    if (mapped_bits > callee_bits) {
      auto existing_wide = caller_outgoing.find(*mapped_slot_id);
      if (existing_wide == caller_outgoing.end())
        continue;
      auto merged = mergeLowBitsIntoWiderStateExpr(
          existing_wide->second, mapped_bits, *specialized, callee_bits,
          *mapped_slot_id);
      if (!merged)
        continue;
      caller_outgoing[*mapped_slot_id] = std::move(*merged);
    } else if (mapped_bits != 0 && callee_bits > mapped_bits) {
      caller_outgoing[*mapped_slot_id] =
          castExprToBitWidth(*specialized, mapped_bits);
    } else {
      caller_outgoing[*mapped_slot_id] = std::move(*specialized);
    }
    propagateAliasedStateSlotWrite(caller_outgoing, *mapped_slot_id,
                                   caller_outgoing.at(*mapped_slot_id),
                                   slot_info);
  }

  for (const auto &[callee_cell_id, callee_value] : callee_outgoing_stack_map) {
    if (!written_stack_cells.empty() &&
        !written_stack_cells.count(callee_cell_id)) {
      vmModelImportDebugLog("stack-import skip call=" + callee->getName().str() +
                            " reason=not-written cell=" +
                            std::to_string(callee_cell_id));
      continue;
    }
    auto cell_info_it = stack_cell_info.find(callee_cell_id);
    if (cell_info_it == stack_cell_info.end()) {
      vmModelImportDebugLog("stack-import skip call=" + callee->getName().str() +
                            " reason=missing-cell-info cell=" +
                            std::to_string(callee_cell_id));
      continue;
    }
    std::optional<unsigned> mapped_cell_id;
    std::optional<StackCellKey> mapped_structural_key;
    auto validate_exact_mapped_cell =
        [&](const VirtualStackCellSummary &mapped_cell) {
          if (!mapped_cell_id)
            return;
          auto mapped_info_it = stack_cell_info.find(*mapped_cell_id);
          if (mapped_info_it == stack_cell_info.end() ||
              mapped_info_it->second->base_name != mapped_cell.base_name ||
              mapped_info_it->second->base_offset != mapped_cell.base_offset ||
              mapped_info_it->second->base_width != mapped_cell.base_width ||
              mapped_info_it->second->base_from_argument !=
                  mapped_cell.base_from_argument ||
              mapped_info_it->second->base_from_alloca !=
                  mapped_cell.base_from_alloca ||
              mapped_info_it->second->cell_offset != mapped_cell.offset ||
              mapped_info_it->second->width != mapped_cell.width) {
            mapped_structural_key = stackCellKeyForSummary(mapped_cell);
            mapped_cell_id.reset();
          }
        };
    if (auto arg_index = parseArgumentBaseName(cell_info_it->second->base_name);
        !mapped_cell_id && arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStackCellSummary mapped_cell;
          mapped_cell.base_name = actual_slot->base_name;
          mapped_cell.base_offset =
              actual_slot->offset + cell_info_it->second->base_offset;
          mapped_cell.base_width = actual_slot->width;
          mapped_cell.base_from_argument = actual_slot->from_argument;
          mapped_cell.base_from_alloca = actual_slot->from_alloca;
          mapped_cell.offset = cell_info_it->second->cell_offset;
          mapped_cell.width = cell_info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
          validate_exact_mapped_cell(mapped_cell);
          if (!mapped_cell_id)
            mapped_structural_key = stackCellKeyForSummary(mapped_cell);
        } else if (auto actual_cell = extractStackCellSummaryFromExpr(
                       expr_it->second, cell_info_it->second->width)) {
          VirtualStackCellSummary mapped_cell = *actual_cell;
          mapped_cell.base_offset += cell_info_it->second->base_offset;
          mapped_cell.offset += cell_info_it->second->cell_offset;
          mapped_cell.width = cell_info_it->second->width;
          vmModelImportDebugLog(
              "stack-import map-attempt call=" + callee->getName().str() +
              " callee_cell_base=" + cell_info_it->second->base_name + "+" +
              std::to_string(cell_info_it->second->base_offset) +
              " callee_cell_off=" +
              std::to_string(cell_info_it->second->cell_offset) +
              " actual_expr=" + renderVirtualValueExpr(expr_it->second) +
              " mapped_base=" + mapped_cell.base_name + "+" +
              std::to_string(mapped_cell.base_offset) + " mapped_off=" +
              std::to_string(mapped_cell.offset));
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
          validate_exact_mapped_cell(mapped_cell);
          if (mapped_cell_id)
            vmModelImportDebugLog("stack-import map-hit call=" +
                                  callee->getName().str() + " mapped_cell_id=" +
                                  std::to_string(*mapped_cell_id));
          if (!mapped_cell_id)
            mapped_structural_key = stackCellKeyForSummary(mapped_cell);
        }
      }
    }
    if (!mapped_cell_id && !mapped_structural_key) {
      if (localized_outgoing &&
          stack_cell_info.find(callee_cell_id) != stack_cell_info.end()) {
        mapped_cell_id = callee_cell_id;
      }
    }
    if (!mapped_cell_id && !mapped_structural_key) {
      mapped_cell_id = lookupMappedCallerStackCellId(
          call, *cell_info_it->second, slot_ids, stack_cell_ids, dl);
    }
    if (!mapped_cell_id && !mapped_structural_key) {
      vmModelImportDebugLog("stack-import skip call=" + callee->getName().str() +
                            " reason=no-mapped-cell cell=" +
                            std::to_string(callee_cell_id));
      continue;
    }
    if (!localized_outgoing && mapped_cell_id &&
        !relevant_caller_stack_cell_ids.empty() &&
        !containsSortedId(relevant_caller_stack_cell_ids, *mapped_cell_id)) {
      vmModelImportDebugLog("stack-import skip call=" + callee->getName().str() +
                            " reason=irrelevant-mapped-cell cell=" +
                            std::to_string(callee_cell_id) + " mapped=" +
                            std::to_string(*mapped_cell_id));
      continue;
    }

    auto remapped =
        remapCalleeExprToCaller(callee_value, call, slot_info, stack_cell_info,
                                slot_ids, stack_cell_ids, dl);
    vmModelImportDebugLog("stack-import before call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(callee_value) +
                          " remapped=" + renderVirtualValueExpr(remapped));
    auto effective_caller_outgoing_stack =
        rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack);
    auto effective_slot_facts = slotFactsForMap(caller_outgoing);
    auto effective_stack_facts = stackFactsForMap(effective_caller_outgoing_stack);
    auto tracked_caller_state = buildTrackedFactState(
        model, caller_outgoing, effective_caller_outgoing_stack,
        &caller_structural_outgoing_stack);
    auto specialized =
        localized_outgoing
            ? normalizeLocalizedExprForCaller(
                  callee_value, caller_fn, slot_ids, stack_cell_ids,
                  caller_outgoing, effective_caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map)
            : normalizeImportedExprForCaller(
                  callee_value, call, slot_info, stack_cell_info, slot_ids,
                  stack_cell_ids, dl, caller_outgoing,
                  effective_caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map);
    if (localized_outgoing && specialized.has_value() &&
        containsArgumentExpr(*specialized)) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing,
              effective_caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
          specialized = std::move(remapped);
      }
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         isUnknownLikeExpr(*specialized) ||
         !isBoundedLocalizedTransferExpr(*specialized)) &&
        isBoundedLocalizedTransferExpr(remapped)) {
      specialized = remapped;
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         isUnknownLikeExpr(*specialized) ||
         !isBoundedLocalizedTransferExpr(*specialized))) {
      specialized = remapped;
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         (specialized.has_value() &&
          (isUnknownLikeExpr(*specialized) ||
           !isBoundedLocalizedTransferExpr(*specialized))))) {
      if (auto imported = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing,
              effective_caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
        if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
            !isBoundedLocalizedTransferExpr(*specialized)) {
          if (!isUnknownLikeExpr(*imported) &&
              isBoundedLocalizedTransferExpr(*imported)) {
            specialized = std::move(imported);
          }
        }
      }
    }
    if (specialized.has_value() &&
        (containsStackCellExpr(*specialized) || containsStateSlotExpr(*specialized))) {
      if (auto structural = structurallySpecializeHelperExpr(
              *specialized, effective_slot_facts, effective_stack_facts,
              slot_info, stack_cell_info)) {
        specialized = std::move(structural);
      }
    }
    if (specialized.has_value()) {
      auto tracked_resolved = resolveTrackedStackExpr(
          model, tracked_caller_state, *specialized, slot_ids, stack_cell_ids);
      if (!exprEquals(tracked_resolved, *specialized))
        specialized = std::move(tracked_resolved);
    }
    if (localized_outgoing &&
        (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
         !isBoundedLocalizedTransferExpr(*specialized)) &&
        isBoundedLocalizedTransferExpr(remapped)) {
      specialized = remapped;
    }
    bool acceptable =
        specialized.has_value() &&
        (localized_outgoing ? isBoundedLocalizedTransferExpr(*specialized)
                            : isBoundedStateProvenanceExpr(*specialized));
    if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
        !acceptable) {
      std::string reason = !specialized.has_value()
                               ? "no-specialized"
                               : (isUnknownLikeExpr(*specialized) ? "unknown"
                                                                  : "unbounded");
      vmModelImportDebugLog("stack-import skip call=" + callee->getName().str() +
                            " reason=" + reason + " cell=" +
                            std::to_string(callee_cell_id) + " expr=" +
                            renderVirtualValueExpr(callee_value));
      continue;
    }
    if (!mapped_cell_id && mapped_structural_key) {
      auto existing = caller_structural_outgoing_stack.find(*mapped_structural_key);
      if (existing == caller_structural_outgoing_stack.end() ||
          !exprEquals(existing->second, *specialized)) {
        vmModelImportDebugLog("structural-stack-import after call=" +
                              callee->getName().str() + " expr=" +
                              renderVirtualValueExpr(*specialized));
        materializeStructuralStackFact(*mapped_structural_key, *specialized);
        caller_structural_outgoing_stack[*mapped_structural_key] =
            std::move(*specialized);
      }
      continue;
    }
    auto existing = caller_outgoing_stack.find(*mapped_cell_id);
    if (existing != caller_outgoing_stack.end() &&
        !exprEquals(existing->second, *specialized) &&
        isIdentityStackCellExpr(*specialized, *mapped_cell_id)) {
      continue;
    }
    vmModelImportDebugLog("stack-import after call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(*specialized) +
                          " mapped_cell=" +
                          std::to_string(*mapped_cell_id) + "(" +
                          stack_cell_info.at(*mapped_cell_id)->base_name + "+" +
                          std::to_string(
                              stack_cell_info.at(*mapped_cell_id)->base_offset) +
                          "," +
                          std::to_string(
                              stack_cell_info.at(*mapped_cell_id)->cell_offset) +
                          ")");
    caller_outgoing_stack[*mapped_cell_id] = std::move(*specialized);
  }
  if (localized_outgoing) {
    std::set<StackCellKey> written_structural_stack_keys;
    written_structural_stack_keys.insert(
        localized_outgoing->written_structural_stack_keys.begin(),
        localized_outgoing->written_structural_stack_keys.end());
    for (const auto &[callee_key, callee_value] :
         localized_outgoing->structural_outgoing_stack) {
      if (!written_structural_stack_keys.empty() &&
          !written_structural_stack_keys.count(callee_key)) {
        continue;
      }
      auto mapped_key = remapCalleeStructuralStackKeyToCaller(
          callee_key, call, slot_info, stack_cell_info, slot_ids,
          stack_cell_ids, dl);
      if (!mapped_key)
        continue;
      vmModelImportDebugLog("structural-stack-key call=" +
                            callee->getName().str() + " key=" +
                            mapped_key->base_slot.base_name + ":" +
                            std::to_string(mapped_key->base_slot.offset) + ":" +
                            std::to_string(mapped_key->base_slot.width) + ":" +
                            std::to_string(mapped_key->base_slot.from_argument) +
                            ":" +
                            std::to_string(mapped_key->base_slot.from_alloca) +
                            ":" + std::to_string(mapped_key->cell_offset) + ":" +
                            std::to_string(mapped_key->width));
      auto specialized = normalizeLocalizedExprForCaller(
          callee_value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
          rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack),
          &caller_structural_outgoing_stack,
          caller_argument_map);
      auto structural_stack_map =
          rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack);
      auto structural_slot_facts = slotFactsForMap(caller_outgoing);
      auto structural_stack_facts = stackFactsForMap(structural_stack_map);
      if (specialized.has_value() &&
          (containsStackCellExpr(*specialized) || containsStateSlotExpr(*specialized))) {
        if (auto structural = structurallySpecializeHelperExpr(
                *specialized, structural_slot_facts, structural_stack_facts,
                slot_info, stack_cell_info)) {
          specialized = std::move(structural);
        }
      }
      if (specialized.has_value()) {
        auto tracked_caller_state = buildTrackedFactState(
            model, caller_outgoing,
            rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack),
            &caller_structural_outgoing_stack);
        auto tracked_resolved = resolveTrackedStackExpr(
            model, tracked_caller_state, *specialized, slot_ids,
            stack_cell_ids);
        if (!exprEquals(tracked_resolved, *specialized))
          specialized = std::move(tracked_resolved);
      }
      if (!specialized.has_value() ||
          (specialized.has_value() && containsArgumentExpr(*specialized))) {
        if (auto remapped = normalizeImportedExprForCaller(
                callee_value, call, slot_info, stack_cell_info, slot_ids,
                stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
                &caller_structural_outgoing_stack, caller_argument_map)) {
          specialized = std::move(remapped);
        }
      }
      if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
          !isBoundedLocalizedTransferExpr(*specialized)) {
        continue;
      }
      auto existing = caller_structural_outgoing_stack.find(*mapped_key);
      if (existing != caller_structural_outgoing_stack.end() &&
          exprEquals(existing->second, *specialized)) {
        continue;
      }
      vmModelImportDebugLog("structural-stack-import after call=" +
                            callee->getName().str() + " expr=" +
                            renderVirtualValueExpr(*specialized));
      materializeStructuralStackFact(*mapped_key, *specialized);
      caller_structural_outgoing_stack[*mapped_key] = std::move(*specialized);
    }
  }

  vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                       " callee=" + callee->getName().str() +
                       " step=done");
  return true;
}

void applyDirectCalleeEffectsImpl(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    std::map<StackCellKey, VirtualValueExpr> &caller_structural_outgoing_stack,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const llvm::DataLayout &dl, const BinaryMemoryMap &binary_memory,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    LocalizedReplayCacheState *localized_replay_cache,
    llvm::ArrayRef<unsigned> relevant_caller_slot_ids,
    llvm::ArrayRef<unsigned> relevant_caller_stack_cell_ids) {
  for (auto &BB : caller_fn) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;
          vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                           " inspect=" + callee->getName().str());
      if (applySingleDirectCalleeEffects(
              caller_fn, *call, model, handler_index, outgoing_maps,
              outgoing_stack_maps, caller_argument_map, caller_outgoing,
              caller_outgoing_stack, caller_structural_outgoing_stack, slot_ids,
              slot_info, stack_cell_ids, stack_cell_info, dl, binary_memory,
              depth, visiting, nullptr, nullptr, nullptr,
              localized_replay_cache, relevant_caller_slot_ids,
              relevant_caller_stack_cell_ids)) {
        continue;
      }

      if (!isCallSiteHelper(*callee))
        continue;
      vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                           " helper-callsite=" + callee->getName().str() +
                           " step=resolve-begin");

      auto local_state = computeLocalFactsBeforeCall(
          *call, dl, slot_ids, stack_cell_ids, caller_outgoing,
          caller_outgoing_stack, caller_argument_map);
      auto callsite = resolveCallSiteInfo(
          *call, dl, slot_ids, stack_cell_ids, local_state.slot_facts,
          local_state.stack_facts, caller_argument_map);
      vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                           " helper-callsite=" + callee->getName().str() +
                           " step=resolve-done target=" +
                           (callsite.target_pc.has_value()
                                ? ("0x" +
                                   llvm::utohexstr(*callsite.target_pc))
                                : std::string("<none>")));
      if (!callsite.target_pc.has_value())
        continue;

      const auto *target_summary =
          lookupHandlerByEntryVA(model, *callsite.target_pc);
      if (!target_summary)
        continue;

      auto localized_outgoing = computeResolvedCallTargetOutgoingFacts(
          *call, model, *target_summary, slot_info, stack_cell_info, slot_ids,
          stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
          caller_outgoing, caller_outgoing_stack, caller_argument_map, callsite,
          binary_memory, depth + 1, visiting);
      vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                           " helper-callsite=" + callee->getName().str() +
                           " step=localized-target-done success=" +
                           llvm::Twine(localized_outgoing.has_value()).str());
      if (!localized_outgoing)
        continue;

      vmModelImportDebugLog("call-root effects call=" + callee->getName().str() +
                            " target=0x" +
                            llvm::utohexstr(*callsite.target_pc) + " fn=" +
                            target_summary->function_name);

      llvm::SmallDenseSet<unsigned, 16> written_slots(
          target_summary->written_slot_ids.begin(),
          target_summary->written_slot_ids.end());
      llvm::SmallDenseSet<unsigned, 16> written_stack_cells;
      for (const auto &[cell_id, value] : localized_outgoing->outgoing_stack) {
        (void)value;
        written_stack_cells.insert(cell_id);
      }

      for (const auto &[slot_id, value] : localized_outgoing->outgoing_slots) {
        if (!written_slots.empty() && !written_slots.count(slot_id))
          continue;
        if (!relevant_caller_slot_ids.empty() &&
            !containsSortedId(relevant_caller_slot_ids, slot_id)) {
          continue;
        }
        auto specialized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack),
            &caller_structural_outgoing_stack,
            caller_argument_map);
        auto structural_stack_map =
            rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack);
        auto structural_slot_facts = slotFactsForMap(caller_outgoing);
        auto structural_stack_facts = stackFactsForMap(structural_stack_map);
        if (specialized.has_value() &&
            (containsStackCellExpr(*specialized) || containsStateSlotExpr(*specialized))) {
          if (auto structural = structurallySpecializeHelperExpr(
                  *specialized, structural_slot_facts, structural_stack_facts,
                  slot_info, stack_cell_info)) {
            specialized = std::move(structural);
          }
        }
        if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
            !isBoundedLocalizedTransferExpr(*specialized)) {
          continue;
        }
        auto existing = caller_outgoing.find(slot_id);
        if (existing != caller_outgoing.end() &&
            !exprEquals(existing->second, *specialized) &&
            isIdentitySlotExpr(*specialized, slot_id)) {
          continue;
        }
        vmModelImportDebugLog("call-root slot-import after call=" +
                              callee->getName().str() + " expr=" +
                              renderVirtualValueExpr(*specialized));
        caller_outgoing[slot_id] = std::move(*specialized);
      }

      for (const auto &[cell_id, value] : localized_outgoing->outgoing_stack) {
        if (!written_stack_cells.empty() && !written_stack_cells.count(cell_id))
          continue;
        if (!relevant_caller_stack_cell_ids.empty() &&
            !containsSortedId(relevant_caller_stack_cell_ids, cell_id)) {
          continue;
        }
      auto specialized = normalizeLocalizedExprForCaller(
          value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
          rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack),
          &caller_structural_outgoing_stack,
          caller_argument_map);
      auto structural_stack_map =
          rebaseOutgoingStackFacts(model, caller_outgoing, caller_outgoing_stack);
      auto structural_slot_facts = slotFactsForMap(caller_outgoing);
      auto structural_stack_facts = stackFactsForMap(structural_stack_map);
      if (specialized.has_value() &&
          (containsStackCellExpr(*specialized) || containsStateSlotExpr(*specialized))) {
        if (auto structural = structurallySpecializeHelperExpr(
                *specialized, structural_slot_facts, structural_stack_facts,
                slot_info, stack_cell_info)) {
          specialized = std::move(structural);
        }
      }
      if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
          !isBoundedLocalizedTransferExpr(*specialized)) {
        continue;
      }
        auto existing = caller_outgoing_stack.find(cell_id);
        if (existing != caller_outgoing_stack.end() &&
            !exprEquals(existing->second, *specialized) &&
            isIdentityStackCellExpr(*specialized, cell_id)) {
          continue;
        }
        vmModelImportDebugLog("call-root stack-import after call=" +
                              callee->getName().str() + " expr=" +
                              renderVirtualValueExpr(*specialized) +
                              " cell=" + std::to_string(cell_id));
        caller_outgoing_stack[cell_id] = std::move(*specialized);
      }
      for (const auto &[key, value] : localized_outgoing->structural_outgoing_stack) {
        auto specialized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, &caller_structural_outgoing_stack,
            caller_argument_map);
        if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
            !isBoundedLocalizedTransferExpr(*specialized)) {
          continue;
        }
        if (auto mapped_cell_it = stack_cell_ids.find(key);
            mapped_cell_it != stack_cell_ids.end()) {
          auto existing = caller_outgoing_stack.find(mapped_cell_it->second);
          if (existing == caller_outgoing_stack.end() ||
              !exprEquals(existing->second, *specialized)) {
            vmModelImportDebugLog("call-root stack-import after call=" +
                                  callee->getName().str() + " expr=" +
                                  renderVirtualValueExpr(*specialized) +
                                  " cell=" +
                                  std::to_string(mapped_cell_it->second));
            caller_outgoing_stack[mapped_cell_it->second] = *specialized;
          }
        }
        caller_structural_outgoing_stack[key] = std::move(*specialized);
      }
    }
  }
}

void applyDirectCalleeEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const BinaryMemoryMap &binary_memory,
    LocalizedReplayCacheState *localized_replay_cache,
    llvm::ArrayRef<unsigned> relevant_caller_slot_ids,
    llvm::ArrayRef<unsigned> relevant_caller_stack_cell_ids) {
  const auto stack_model = buildStackModelContext(model);
  const auto &slot_ids = stack_model.slot_ids;
  const auto &slot_info = stack_model.slot_info;
  const auto &stack_cell_ids = stack_model.stack_cell_ids;
  const auto &stack_cell_info = stack_model.stack_cell_info;
  const auto &dl = caller_fn.getParent()->getDataLayout();
  std::map<StackCellKey, VirtualValueExpr> caller_structural_outgoing_stack;
  llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
  visiting.insert(&caller_fn);
  applyDirectCalleeEffectsImpl(
      caller_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
      caller_argument_map, caller_outgoing, caller_outgoing_stack,
      caller_structural_outgoing_stack, slot_ids, slot_info, stack_cell_ids,
      stack_cell_info, dl, binary_memory, /*depth=*/0, visiting,
      localized_replay_cache, relevant_caller_slot_ids,
      relevant_caller_stack_cell_ids);

  for (unsigned round = 0; round < 2; ++round) {
    bool changed = false;

    for (auto &[slot_id, value] : caller_outgoing) {
      auto normalized = normalizeLocalizedExprForCaller(
          value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
          caller_outgoing_stack, &caller_structural_outgoing_stack,
          caller_argument_map);
      if (!normalized.has_value() || exprEquals(value, *normalized))
        continue;
      value = std::move(*normalized);
      changed = true;
    }

    for (auto &[cell_id, value] : caller_outgoing_stack) {
      auto normalized = normalizeLocalizedExprForCaller(
          value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
          caller_outgoing_stack, &caller_structural_outgoing_stack,
          caller_argument_map);
      if (!normalized.has_value() || exprEquals(value, *normalized))
        continue;
      value = std::move(*normalized);
      changed = true;
    }

    if (!changed)
      break;
  }
}

}  // namespace omill::virtual_model::detail

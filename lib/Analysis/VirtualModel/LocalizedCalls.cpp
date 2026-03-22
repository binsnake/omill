#include "Analysis/VirtualModel/Internal.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

namespace omill::virtual_model::detail {

static void applyLocalizedCallsiteReturnEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const VirtualHandlerSummary &caller_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);

std::optional<CallsiteLocalizedOutgoingFacts> computeCallsiteLocalizedOutgoingFacts(
    llvm::CallBase &call, const VirtualMachineModel &model,
    const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts) {
  auto *callee_fn = call.getCalledFunction();
  if (!callee_fn)
    return std::nullopt;
  auto log_localization_step = [&](llvm::StringRef step) {
    vmModelStageDebugLog("callsite-localize: caller=" +
                         call.getFunction()->getName().str() + " callee=" +
                         callee_fn->getName().str() + " step=" + step.str());
  };
  log_localization_step("begin");
  if (!canRecursivelyLocalizeCallsiteSummary(callee_summary, depth))
    return std::nullopt;
  if (!visiting.insert(callee_fn).second)
    return std::nullopt;

  std::map<unsigned, VirtualValueExpr> callee_incoming;
  std::map<unsigned, VirtualValueExpr> callee_incoming_stack;
  std::map<unsigned, VirtualValueExpr> callee_incoming_args;
  std::map<unsigned, VirtualValueExpr> callee_localized_args;
  const auto native_sp_offset = nativeStackPointerOffsetForValue(&call);
  const auto specialized_call_args = [&]() {
    if (native_sp_offset.has_value()) {
      auto local_call_state = computeLocalFactsBeforeCall(
          call, dl, slot_ids, stack_cell_ids, caller_outgoing,
          caller_outgoing_stack, caller_argument_map);
      return buildSpecializedCallArgumentMap(
          call, dl, slot_ids, stack_cell_ids, local_call_state.slot_facts,
          local_call_state.stack_facts, caller_argument_map);
    }
    return buildSpecializedCallArgumentMap(
        call, dl, slot_ids, stack_cell_ids, caller_outgoing,
        caller_outgoing_stack, caller_argument_map);
  }();
  log_localization_step("specialized-args-done");

  for (const auto &fact : callee_summary.specialization_facts)
    callee_incoming[fact.slot_id] = fact.value;
  for (const auto &fact : callee_summary.specialization_stack_facts)
    callee_incoming_stack[fact.cell_id] = fact.value;
  if (callee_summary.entry_va.has_value())
    callee_incoming_args[1] = constantExpr(*callee_summary.entry_va, 64);
  callee_localized_args = callee_incoming_args;

  if (!callee_summary.direct_callees.empty()) {
    for (const auto &[slot_id, value] : caller_outgoing) {
      auto info_it = slot_info.find(slot_id);
      if (info_it == slot_info.end() || !info_it->second->from_argument ||
          !isBoundedStateProvenanceExpr(value)) {
        continue;
      }
      mergeFactIntoMap(callee_incoming, slot_id, value);
    }
    for (const auto &[cell_id, value] : caller_outgoing_stack) {
      auto info_it = stack_cell_info.find(cell_id);
      if (info_it == stack_cell_info.end() ||
          !info_it->second->base_from_argument ||
          !isBoundedStateProvenanceExpr(value)) {
        continue;
      }
      mergeFactIntoMap(callee_incoming_stack, cell_id, value);
    }
  }
  log_localization_step("seed-direct-callee-liveins-done");

  for (unsigned callee_slot_id : callee_summary.live_in_slot_ids) {
    if (auto same_it = caller_outgoing.find(callee_slot_id);
        same_it != caller_outgoing.end() &&
        isBoundedStateProvenanceExpr(same_it->second)) {
      mergeFactIntoMap(callee_incoming, callee_slot_id, same_it->second);
    }

    auto info_it = slot_info.find(callee_slot_id);
    if (info_it == slot_info.end())
      continue;
    std::optional<unsigned> mapped_slot_id;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name);
        arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStateSlotSummary mapped_slot = *actual_slot;
          mapped_slot.offset += info_it->second->offset;
          mapped_slot.width = info_it->second->width;
          mapped_slot_id = lookupSlotIdForSummary(mapped_slot, slot_ids);
        }
      }
    }
    if (!mapped_slot_id)
      mapped_slot_id =
          lookupMappedCallerSlotId(call, *info_it->second, slot_ids, dl);
    if (!mapped_slot_id)
      continue;
    auto value_it = caller_outgoing.find(*mapped_slot_id);
    if (value_it == caller_outgoing.end() ||
        !isSimpleRemappableFactExpr(value_it->second)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming, callee_slot_id, value_it->second);
  }
  log_localization_step("slot-liveins-done");

  for (unsigned callee_cell_id : callee_summary.live_in_stack_cell_ids) {
    if (auto same_it = caller_outgoing_stack.find(callee_cell_id);
        same_it != caller_outgoing_stack.end() &&
        isBoundedStateProvenanceExpr(same_it->second)) {
      mergeFactIntoMap(callee_incoming_stack, callee_cell_id, same_it->second);
    }

    auto info_it = stack_cell_info.find(callee_cell_id);
    if (info_it == stack_cell_info.end())
      continue;
    std::optional<unsigned> mapped_cell_id;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name);
        arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStackCellSummary mapped_cell;
          mapped_cell.base_name = actual_slot->base_name;
          mapped_cell.base_offset =
              actual_slot->offset + info_it->second->base_offset;
          mapped_cell.base_width = actual_slot->width;
          mapped_cell.base_from_argument = actual_slot->from_argument;
          mapped_cell.base_from_alloca = actual_slot->from_alloca;
          mapped_cell.offset = info_it->second->cell_offset;
          mapped_cell.width = info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        } else if (auto actual_cell = extractStackCellSummaryFromExpr(
                       expr_it->second, info_it->second->width)) {
          VirtualStackCellSummary mapped_cell = *actual_cell;
          mapped_cell.base_offset += info_it->second->base_offset;
          mapped_cell.offset += info_it->second->cell_offset;
          mapped_cell.width = info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        }
      }
    }
    if (!mapped_cell_id) {
      mapped_cell_id = lookupMappedCallerStackCellId(
          call, *info_it->second, slot_ids, stack_cell_ids, dl);
    }
    if (!mapped_cell_id)
      continue;
    auto value_it = caller_outgoing_stack.find(*mapped_cell_id);
    if (value_it == caller_outgoing_stack.end() ||
        !isSimpleRemappableFactExpr(value_it->second)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming_stack, callee_cell_id, value_it->second);
  }
  log_localization_step("stack-liveins-done");

  for (const auto &[arg_index, specialized] : specialized_call_args) {
    if (!isBoundedArgumentFactExpr(specialized))
      continue;
    mergeFactIntoMap(callee_incoming_args, arg_index, specialized);
  }
  for (const auto &[arg_index, specialized] : specialized_call_args)
    callee_localized_args[arg_index] = specialized;
  log_localization_step("argument-facts-done");

  seedLiftedCallContinuationStackCell(call, callee_summary, stack_cell_info,
                                      callee_incoming_stack);
  log_localization_step("seed-continuation-done");

  CallsiteLocalizedOutgoingFacts localized;
  if (canComputeLocalizedSingleBlockOutgoingFacts(*callee_fn, callee_summary)) {
    log_localization_step("leaf-replay-begin");
    if (auto leaf_localized = computeLocalizedSingleBlockOutgoingFacts(
            *callee_fn, model, callee_summary, slot_ids, stack_cell_ids,
            callee_incoming, callee_incoming_stack, callee_localized_args,
            handler_index, outgoing_maps, outgoing_stack_maps, binary_memory,
            depth + 1, visiting, &call, &caller_outgoing_stack,
            &caller_outgoing, caller_structural_stack_facts,
            fallback_caller_stack_facts, fallback_caller_slot_facts,
            fallback_caller_structural_stack_facts)) {
      log_localization_step("leaf-replay-done");
      visiting.erase(callee_fn);
      return leaf_localized;
    }
    log_localization_step("leaf-replay-failed");
  }

  log_localization_step("summary-outgoing-begin");
  for (const auto &fact : computeOutgoingFacts(callee_summary, callee_incoming,
                                               callee_incoming_stack,
                                               callee_incoming_args)) {
    localized.outgoing_slots.emplace(fact.slot_id, fact.value);
  }
  for (const auto &fact :
       computeOutgoingStackFacts(callee_summary, callee_incoming,
                                 callee_incoming_stack, callee_incoming_args)) {
    localized.outgoing_stack.emplace(fact.cell_id, fact.value);
  }
  log_localization_step("summary-outgoing-done");
  if (!callee_summary.direct_callees.empty()) {
    log_localization_step("direct-callees-begin");
    applyDirectCalleeEffectsImpl(
        *callee_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming_args, localized.outgoing_slots, localized.outgoing_stack,
        localized.structural_outgoing_stack, slot_ids, slot_info, stack_cell_ids,
        stack_cell_info, dl, binary_memory, depth + 1, visiting);
    log_localization_step("direct-callees-done");
  }
  if (!callee_summary.callsites.empty()) {
    log_localization_step("callsites-begin");
    applyLocalizedCallsiteReturnEffects(
        *callee_fn, model, callee_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming, callee_incoming_stack, callee_incoming_args,
        localized.outgoing_slots, localized.outgoing_stack, binary_memory,
        depth + 1, visiting);
    log_localization_step("callsites-done");
  }
  if (!callee_summary.direct_callees.empty()) {
    log_localization_step("specialize-outgoing-begin");
    const auto snapshot_slots = localized.outgoing_slots;
    const auto snapshot_stack = localized.outgoing_stack;
    for (auto &[slot_id, value] : localized.outgoing_slots) {
      (void)slot_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[cell_id, value] : localized.outgoing_stack) {
      (void)cell_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[key, value] : localized.structural_outgoing_stack) {
      (void)key;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    log_localization_step("specialize-outgoing-done");
  }
  log_localization_step("rebase-stack-begin");
  localized.outgoing_stack =
      rebaseOutgoingStackFacts(model, localized.outgoing_slots,
                               localized.outgoing_stack);
  log_localization_step("rebase-stack-done");
  visiting.erase(callee_fn);
  log_localization_step("done");
  return localized;
}

std::optional<CallsiteLocalizedOutgoingFacts>
computeResolvedCallTargetOutgoingFacts(
    llvm::CallBase &call, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    const ResolvedCallSiteInfo &callsite,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  auto *target_fn = call.getModule()
                        ? call.getModule()->getFunction(target_summary.function_name)
                        : nullptr;
  if (!target_fn)
    return std::nullopt;
  if (depth > kMaxCallsiteLocalizationDepth)
    return std::nullopt;
  if (!callsite.target_pc.has_value())
    return std::nullopt;

  auto state_arg = summarizeSpecializedCallArg(
      call, 1, dl, slot_ids, stack_cell_ids, caller_outgoing,
      caller_outgoing_stack, caller_argument_map);
  if (!isCallerStateArgumentExpr(state_arg))
    return std::nullopt;

  if (!visiting.insert(target_fn).second)
    return std::nullopt;

  std::map<unsigned, VirtualValueExpr> callee_incoming;
  std::map<unsigned, VirtualValueExpr> callee_incoming_stack;
  std::map<unsigned, VirtualValueExpr> callee_incoming_args;

  for (const auto &fact : target_summary.specialization_facts)
    callee_incoming[fact.slot_id] = fact.value;
  for (const auto &fact : target_summary.specialization_stack_facts)
    callee_incoming_stack[fact.cell_id] = fact.value;

  callee_incoming_args[0] = state_arg;
  callee_incoming_args[1] = constantExpr(*callsite.target_pc, 64);
  if (call.arg_size() >= 1) {
    auto memory_arg = summarizeSpecializedCallArg(
        call, 0, dl, slot_ids, stack_cell_ids, caller_outgoing,
        caller_outgoing_stack, caller_argument_map);
    if (isBoundedArgumentFactExpr(memory_arg))
      callee_incoming_args[2] = std::move(memory_arg);
  }

  for (unsigned slot_id : target_summary.live_in_slot_ids) {
    auto value_it = caller_outgoing.find(slot_id);
    if (value_it == caller_outgoing.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming, slot_id, value_it->second);
  }
  for (unsigned cell_id : target_summary.live_in_stack_cell_ids) {
    auto value_it = caller_outgoing_stack.find(cell_id);
    if (value_it == caller_outgoing_stack.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming_stack, cell_id, value_it->second);
  }

  if (callsite.continuation_pc.has_value() && call.getModule()) {
    seedCallContinuationStackCell(*call.getModule(), *callsite.continuation_pc,
                                  stack_cell_info, callee_incoming_stack);
  }

  CallsiteLocalizedOutgoingFacts localized;
  if (canComputeLocalizedSingleBlockOutgoingFacts(*target_fn, target_summary)) {
    if (auto leaf_localized = computeLocalizedSingleBlockOutgoingFacts(
            *target_fn, model, target_summary, slot_ids, stack_cell_ids,
            callee_incoming, callee_incoming_stack, callee_incoming_args,
            handler_index, outgoing_maps, outgoing_stack_maps, binary_memory,
            depth + 1, visiting, nullptr, nullptr, &caller_outgoing, nullptr,
            nullptr, nullptr, nullptr)) {
      visiting.erase(target_fn);
      return leaf_localized;
    }
  }

  for (const auto &fact : computeOutgoingFacts(target_summary, callee_incoming,
                                               callee_incoming_stack,
                                               callee_incoming_args)) {
    localized.outgoing_slots.emplace(fact.slot_id, fact.value);
  }
  for (const auto &fact :
       computeOutgoingStackFacts(target_summary, callee_incoming,
                                 callee_incoming_stack, callee_incoming_args)) {
    localized.outgoing_stack.emplace(fact.cell_id, fact.value);
  }

  if (!target_summary.direct_callees.empty()) {
    applyDirectCalleeEffectsImpl(
        *target_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming_args, localized.outgoing_slots, localized.outgoing_stack,
        localized.structural_outgoing_stack, slot_ids, slot_info, stack_cell_ids,
        stack_cell_info, dl, binary_memory, depth + 1, visiting);
  }
  if (!target_summary.callsites.empty()) {
    applyLocalizedCallsiteReturnEffects(
        *target_fn, model, target_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming, callee_incoming_stack, callee_incoming_args,
        localized.outgoing_slots, localized.outgoing_stack, binary_memory,
        depth + 1, visiting);
  }
  if (!target_summary.direct_callees.empty() || !target_summary.callsites.empty()) {
    const auto snapshot_slots = localized.outgoing_slots;
    const auto snapshot_stack = localized.outgoing_stack;
    for (auto &[slot_id, value] : localized.outgoing_slots) {
      (void)slot_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[cell_id, value] : localized.outgoing_stack) {
      (void)cell_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[key, value] : localized.structural_outgoing_stack) {
      (void)key;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
  }

  localized.outgoing_stack =
      rebaseOutgoingStackFacts(model, localized.outgoing_slots,
                               localized.outgoing_stack);
  visiting.erase(target_fn);
  return localized;
}

static void applyLocalizedCallsiteReturnEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const VirtualHandlerSummary &caller_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  const auto &dl = caller_fn.getParent()->getDataLayout();

  size_t callsite_index = 0;
  for (auto &BB : caller_fn) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isCallSiteHelper(*callee))
        continue;
      if (callsite_index >= caller_summary.callsites.size())
        continue;
      ++callsite_index;

      auto local_state = computeLocalFactsBeforeCall(
          *call, dl, slot_ids, stack_cell_ids, caller_incoming,
          caller_incoming_stack, caller_argument_map);
      auto resolved = resolveCallSiteInfo(
          *call, dl, slot_ids, stack_cell_ids, local_state.slot_facts,
          local_state.stack_facts, caller_argument_map);
      auto resolved_slot_facts = local_state.slot_facts;
      auto resolved_stack_facts = local_state.stack_facts;

      if (!resolved.target_pc.has_value()) {
        auto outgoing_local_state = computeLocalFactsBeforeCall(
            *call, dl, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, caller_argument_map);
        auto outgoing_resolved = resolveCallSiteInfo(
            *call, dl, slot_ids, stack_cell_ids,
            outgoing_local_state.slot_facts, outgoing_local_state.stack_facts,
            caller_argument_map);
        if (outgoing_resolved.target_pc.has_value()) {
          resolved = std::move(outgoing_resolved);
          resolved_slot_facts = std::move(outgoing_local_state.slot_facts);
          resolved_stack_facts = std::move(outgoing_local_state.stack_facts);
        }
      }

      if (!resolved.target_pc.has_value())
        continue;

      const auto *target_summary =
          lookupHandlerByEntryVA(model, *resolved.target_pc);
      if (!target_summary)
        continue;

      auto localized = computeResolvedCallTargetOutgoingFacts(
          *call, model, *target_summary, slot_info, stack_cell_info, slot_ids,
          stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
          resolved_slot_facts, resolved_stack_facts, caller_argument_map,
          resolved, binary_memory, depth + 1, visiting);
      if (!localized)
        continue;

      llvm::SmallDenseSet<unsigned, 16> written_slots(
          target_summary->written_slot_ids.begin(),
          target_summary->written_slot_ids.end());
      auto written_stack_cells = rebaseWrittenStackCellIds(
          model, localized->outgoing_slots,
          target_summary->written_stack_cell_ids);

      for (const auto &[slot_id, value] : localized->outgoing_slots) {
        if (!written_slots.empty() && !written_slots.count(slot_id))
          continue;
        auto normalized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, nullptr, caller_argument_map);
        if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
            !isBoundedLocalizedTransferExpr(*normalized)) {
          continue;
        }
        mergeFactIntoMap(caller_outgoing, slot_id, *normalized);
      }

      for (const auto &[cell_id, value] : localized->outgoing_stack) {
        if (!written_stack_cells.empty() && !written_stack_cells.count(cell_id))
          continue;
        auto normalized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, nullptr, caller_argument_map);
        if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
            !isBoundedLocalizedTransferExpr(*normalized)) {
          continue;
        }
        mergeFactIntoMap(caller_outgoing_stack, cell_id, *normalized);
      }
    }
  }
}

std::optional<CallsiteLocalizedOutgoingFacts>
computeEntryPreludeCallOutgoingFacts(
    llvm::Module &M, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    uint64_t continuation_pc, const BinaryMemoryMap &binary_memory,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  auto *target_fn = M.getFunction(target_summary.function_name);
  if (!target_fn)
    return std::nullopt;
  if (depth > kMaxCallsiteLocalizationDepth)
    return std::nullopt;
  if (!target_summary.entry_va.has_value())
    return std::nullopt;
  if (!visiting.insert(target_fn).second)
    return std::nullopt;

  std::map<unsigned, VirtualValueExpr> callee_incoming;
  std::map<unsigned, VirtualValueExpr> callee_incoming_stack;
  std::map<unsigned, VirtualValueExpr> callee_incoming_args;

  for (const auto &fact : target_summary.specialization_facts)
    callee_incoming[fact.slot_id] = fact.value;
  for (const auto &fact : target_summary.specialization_stack_facts)
    callee_incoming_stack[fact.cell_id] = fact.value;

  callee_incoming_args[0] = argumentExpr(0, 64);
  if (auto it = caller_argument_map.find(0); it != caller_argument_map.end())
    callee_incoming_args[0] = it->second;
  callee_incoming_args[1] = constantExpr(*target_summary.entry_va, 64);
  if (auto it = caller_argument_map.find(2);
      it != caller_argument_map.end() &&
      isBoundedArgumentFactExpr(it->second)) {
    callee_incoming_args[2] = it->second;
  } else {
    callee_incoming_args[2] = argumentExpr(2, 64);
  }

  for (unsigned slot_id : target_summary.live_in_slot_ids) {
    auto value_it = caller_incoming.find(slot_id);
    if (value_it == caller_incoming.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming, slot_id, value_it->second);
  }
  for (unsigned cell_id : target_summary.live_in_stack_cell_ids) {
    auto value_it = caller_incoming_stack.find(cell_id);
    if (value_it == caller_incoming_stack.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming_stack, cell_id, value_it->second);
  }

  seedCallContinuationStackCell(M, continuation_pc, stack_cell_info,
                                callee_incoming_stack);

  CallsiteLocalizedOutgoingFacts localized;
  if (canComputeLocalizedSingleBlockOutgoingFacts(*target_fn, target_summary)) {
    if (auto leaf_localized = computeLocalizedSingleBlockOutgoingFacts(
            *target_fn, model, target_summary, slot_ids, stack_cell_ids,
            callee_incoming, callee_incoming_stack, callee_incoming_args,
            handler_index, outgoing_maps, outgoing_stack_maps, binary_memory,
            depth + 1, visiting, nullptr, nullptr, &caller_incoming, nullptr,
            nullptr, nullptr, nullptr)) {
      visiting.erase(target_fn);
      return leaf_localized;
    }
  }

  for (const auto &fact : computeOutgoingFacts(target_summary, callee_incoming,
                                               callee_incoming_stack,
                                               callee_incoming_args)) {
    localized.outgoing_slots.emplace(fact.slot_id, fact.value);
  }
  for (const auto &fact :
       computeOutgoingStackFacts(target_summary, callee_incoming,
                                 callee_incoming_stack, callee_incoming_args)) {
    localized.outgoing_stack.emplace(fact.cell_id, fact.value);
  }

  if (!target_summary.direct_callees.empty()) {
    applyDirectCalleeEffectsImpl(
        *target_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming_args, localized.outgoing_slots, localized.outgoing_stack,
        localized.structural_outgoing_stack, slot_ids, slot_info, stack_cell_ids,
        stack_cell_info, M.getDataLayout(), binary_memory, depth + 1,
        visiting);
  }
  if (!target_summary.callsites.empty()) {
    applyLocalizedCallsiteReturnEffects(
        *target_fn, model, target_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming, callee_incoming_stack, callee_incoming_args,
        localized.outgoing_slots, localized.outgoing_stack, binary_memory,
        depth + 1, visiting);
  }
  if (!target_summary.direct_callees.empty() || !target_summary.callsites.empty()) {
    const auto snapshot_slots = localized.outgoing_slots;
    const auto snapshot_stack = localized.outgoing_stack;
    for (auto &[slot_id, value] : localized.outgoing_slots) {
      (void)slot_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[cell_id, value] : localized.outgoing_stack) {
      (void)cell_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[key, value] : localized.structural_outgoing_stack) {
      (void)key;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
  }

  localized.outgoing_stack =
      rebaseOutgoingStackFacts(model, localized.outgoing_slots,
                               localized.outgoing_stack);
  visiting.erase(target_fn);
  return localized;
}

}  // namespace omill::virtual_model::detail

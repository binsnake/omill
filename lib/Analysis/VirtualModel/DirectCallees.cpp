#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

namespace omill::virtual_model::detail {

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
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts) {
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
  llvm::SmallDenseSet<unsigned, 16> written_slots(
      callee_summary.written_slot_ids.begin(),
      callee_summary.written_slot_ids.end());
  auto localized_outgoing = computeCallsiteLocalizedOutgoingFacts(
      call, model, callee_summary, slot_info, stack_cell_info, slot_ids,
      stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
      caller_outgoing, caller_outgoing_stack, caller_argument_map,
      binary_memory, depth + 1, visiting, &caller_structural_outgoing_stack,
      fallback_caller_stack_facts, fallback_caller_slot_facts,
      fallback_caller_structural_stack_facts);
  vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                       " callee=" + callee->getName().str() +
                       " step=localized-callsite-done success=" +
                       llvm::Twine(localized_outgoing.has_value()).str());
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

    auto remapped =
        remapCalleeExprToCaller(callee_value, call, slot_info, stack_cell_info,
                                slot_ids, stack_cell_ids, dl);
    vmModelImportDebugLog("slot-import before call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(callee_value) +
                          " remapped=" + renderVirtualValueExpr(remapped));
    auto specialized =
        localized_outgoing
            ? normalizeLocalizedExprForCaller(
                  callee_value, caller_fn, slot_ids, stack_cell_ids,
                  caller_outgoing, caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map)
            : normalizeImportedExprForCaller(
                  callee_value, call, slot_info, stack_cell_info, slot_ids,
                  stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map);
    if (localized_outgoing && specialized.has_value() &&
        containsArgumentExpr(*specialized)) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
        specialized = std::move(remapped);
      }
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         (specialized.has_value() &&
          (isUnknownLikeExpr(*specialized) ||
           !isBoundedLocalizedTransferExpr(*specialized))))) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
        specialized = std::move(remapped);
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
      continue;
    }
    auto cell_info_it = stack_cell_info.find(callee_cell_id);
    if (cell_info_it == stack_cell_info.end())
      continue;
    std::optional<unsigned> mapped_cell_id;
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
        } else if (auto actual_cell = extractStackCellSummaryFromExpr(
                       expr_it->second, cell_info_it->second->width)) {
          VirtualStackCellSummary mapped_cell = *actual_cell;
          mapped_cell.base_offset += cell_info_it->second->base_offset;
          mapped_cell.offset += cell_info_it->second->cell_offset;
          mapped_cell.width = cell_info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        }
      }
    }
    if (!mapped_cell_id) {
      mapped_cell_id = lookupMappedCallerStackCellId(
          call, *cell_info_it->second, slot_ids, stack_cell_ids, dl);
    }
    if (!mapped_cell_id)
      continue;

    auto remapped =
        remapCalleeExprToCaller(callee_value, call, slot_info, stack_cell_info,
                                slot_ids, stack_cell_ids, dl);
    vmModelImportDebugLog("stack-import before call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(callee_value) +
                          " remapped=" + renderVirtualValueExpr(remapped));
    auto specialized =
        localized_outgoing
            ? normalizeLocalizedExprForCaller(
                  callee_value, caller_fn, slot_ids, stack_cell_ids,
                  caller_outgoing, caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map)
            : normalizeImportedExprForCaller(
                  callee_value, call, slot_info, stack_cell_info, slot_ids,
                  stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
                  &caller_structural_outgoing_stack, caller_argument_map);
    if (localized_outgoing && specialized.has_value() &&
        containsArgumentExpr(*specialized)) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
        specialized = std::move(remapped);
      }
    }
    if (localized_outgoing &&
        (!specialized.has_value() ||
         (specialized.has_value() &&
          (isUnknownLikeExpr(*specialized) ||
           !isBoundedLocalizedTransferExpr(*specialized))))) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
              &caller_structural_outgoing_stack, caller_argument_map)) {
        specialized = std::move(remapped);
      }
    }
    bool acceptable =
        specialized.has_value() &&
        (localized_outgoing ? isBoundedLocalizedTransferExpr(*specialized)
                            : isBoundedStateProvenanceExpr(*specialized));
    if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
        !acceptable) {
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
      auto specialized = normalizeLocalizedExprForCaller(
          callee_value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
          caller_outgoing_stack, &caller_structural_outgoing_stack,
          caller_argument_map);
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
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
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
              depth, visiting)) {
        continue;
      }

      if (!isCallSiteHelper(*callee))
        continue;
      vmModelStageDebugLog("direct-callee: caller=" + caller_fn.getName().str() +
                           " helper-callsite=" + callee->getName().str() +
                           " step=resolve-begin");

      auto local_state = computeLocalFactsBeforeCall(
          *call, dl, slot_ids, stack_cell_ids,
          /*base_slot_facts=*/{}, /*base_stack_facts=*/{}, caller_argument_map);
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
        auto specialized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, &caller_structural_outgoing_stack,
            caller_argument_map);
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
        auto specialized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, &caller_structural_outgoing_stack,
            caller_argument_map);
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
    const BinaryMemoryMap &binary_memory) {
  const auto slot_ids = buildSlotIdMap(model);
  const auto slot_info = buildSlotInfoMap(model);
  const auto stack_cell_ids = buildStackCellIdMap(model);
  const auto stack_cell_info = buildStackCellInfoMap(model);
  const auto &dl = caller_fn.getParent()->getDataLayout();
  std::map<StackCellKey, VirtualValueExpr> caller_structural_outgoing_stack;
  llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
  visiting.insert(&caller_fn);
  applyDirectCalleeEffectsImpl(
      caller_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
      caller_argument_map, caller_outgoing, caller_outgoing_stack,
      caller_structural_outgoing_stack, slot_ids, slot_info, stack_cell_ids,
      stack_cell_info, dl, binary_memory, /*depth=*/0, visiting);
}

}  // namespace omill::virtual_model::detail

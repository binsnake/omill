#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <map>
#include <optional>
#include <string>
#include <vector>

namespace omill::virtual_model::detail {

namespace {

static VirtualValueExpr constantExprForCallSites(uint64_t value, unsigned bits) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kConstant;
  expr.bit_width = bits;
  expr.complete = true;
  expr.constant = value;
  return expr;
}

static std::optional<unsigned> lookupNamedSlotId(
    const std::map<SlotKey, unsigned> &slot_ids, llvm::StringRef base_name) {
  auto it = llvm::find_if(slot_ids, [&](const auto &entry) {
    return entry.first.base_name == base_name && entry.first.offset == 0;
  });
  if (it == slot_ids.end())
    return std::nullopt;
  return it->second;
}

static bool exprMatchesSlot(const VirtualValueExpr &expr, unsigned slot_id) {
  if (expr.kind != VirtualExprKind::kStateSlot || !expr.slot_id.has_value())
    return false;
  return *expr.slot_id == slot_id;
}

static bool exprMatchesBasePlusOrMinusConst(const VirtualValueExpr &expr,
                                            unsigned slot_id,
                                            VirtualExprKind &op_kind,
                                            uint64_t &imm) {
  if (expr.kind == VirtualExprKind::kAdd && expr.operands.size() == 2) {
    if (exprMatchesSlot(expr.operands[0], slot_id) &&
        expr.operands[1].constant.has_value()) {
      op_kind = VirtualExprKind::kAdd;
      imm = *expr.operands[1].constant;
      return true;
    }
    if (expr.operands[0].constant.has_value() &&
        exprMatchesSlot(expr.operands[1], slot_id)) {
      op_kind = VirtualExprKind::kAdd;
      imm = *expr.operands[0].constant;
      return true;
    }
  }

  if (expr.kind == VirtualExprKind::kSub && expr.operands.size() == 2 &&
      exprMatchesSlot(expr.operands[0], slot_id) &&
      expr.operands[1].constant.has_value()) {
    op_kind = VirtualExprKind::kSub;
    imm = *expr.operands[1].constant;
    return true;
  }

  return false;
}

static bool isReturnPcAnchoredOutgoingNextPcForCallsiteTarget(
    const VirtualValueExpr &callsite_target, const VirtualValueExpr &next_pc_expr,
    unsigned next_pc_slot_id, unsigned return_pc_slot_id) {
  VirtualExprKind callsite_op = VirtualExprKind::kUnknown;
  VirtualExprKind next_pc_op = VirtualExprKind::kUnknown;
  uint64_t callsite_imm = 0;
  uint64_t next_pc_imm = 0;
  if (!exprMatchesBasePlusOrMinusConst(callsite_target, next_pc_slot_id,
                                       callsite_op, callsite_imm)) {
    return false;
  }
  if (!exprMatchesBasePlusOrMinusConst(next_pc_expr, return_pc_slot_id,
                                       next_pc_op, next_pc_imm)) {
    return false;
  }
  return callsite_op == next_pc_op && callsite_imm == next_pc_imm;
}

static std::optional<ResolvedCallSiteInfo>
resolveCallSiteInfoFromOutgoingNextPc(
    const VirtualHandlerSummary &summary, const VirtualValueExpr &callsite_target,
    std::optional<uint64_t> continuation_pc,
    const std::map<SlotKey, unsigned> &slot_ids) {
  if (!continuation_pc)
    return std::nullopt;

  auto next_pc_slot_id = lookupNamedSlotId(slot_ids, "NEXT_PC");
  auto return_pc_slot_id = lookupNamedSlotId(slot_ids, "RETURN_PC");
  if (!next_pc_slot_id || !return_pc_slot_id)
    return std::nullopt;

  const VirtualSlotFact *next_pc_fact = nullptr;
  for (const auto &fact : summary.outgoing_facts) {
    if (fact.slot_id == *next_pc_slot_id) {
      next_pc_fact = &fact;
      break;
    }
  }
  if (!next_pc_fact)
    return std::nullopt;

  if (!isReturnPcAnchoredOutgoingNextPcForCallsiteTarget(
          callsite_target, next_pc_fact->value, *next_pc_slot_id,
          *return_pc_slot_id)) {
    return std::nullopt;
  }

  auto seeded_slot_facts = summary.outgoing_facts;
  auto return_fact_it =
      llvm::find_if(seeded_slot_facts, [&](const VirtualSlotFact &fact) {
        return fact.slot_id == *return_pc_slot_id;
      });
  VirtualValueExpr return_pc_expr =
      constantExprForCallSites(*continuation_pc, next_pc_fact->value.bit_width
                                                     ? next_pc_fact->value.bit_width
                                                     : 64);
  if (return_fact_it == seeded_slot_facts.end()) {
    seeded_slot_facts.push_back(
        VirtualSlotFact{*return_pc_slot_id, std::move(return_pc_expr)});
  } else {
    return_fact_it->value = std::move(return_pc_expr);
  }

  auto resolved_pc = evaluateVirtualExpr(next_pc_fact->value, seeded_slot_facts,
                                         summary.outgoing_stack_facts);
  if (!resolved_pc)
    return std::nullopt;

  ResolvedCallSiteInfo info;
  info.target_expr = next_pc_fact->value;
  info.target_source = VirtualDispatchResolutionSource::kOutgoingFacts;
  info.target_pc = resolved_pc;
  info.continuation_pc = continuation_pc;
  return info;
}

static void seedNamedSlotFact(const std::map<SlotKey, unsigned> &slot_ids,
                              llvm::StringRef base_name, uint64_t value,
                              std::map<unsigned, VirtualValueExpr> &slot_facts) {
  auto it = llvm::find_if(slot_ids, [&](const auto &entry) {
    return entry.first.base_name == base_name && entry.first.offset == 0;
  });
  if (it == slot_ids.end())
    return;
  unsigned width_bits = it->first.width ? it->first.width * 8 : 64;
  slot_facts[it->second] = constantExpr(value, width_bits);
}

}  // namespace

ResolvedCallSiteInfo resolveCallSiteInfo(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  ResolvedCallSiteInfo info;
  std::map<unsigned, VirtualValueExpr> callsite_slots = caller_outgoing;
  std::map<unsigned, VirtualValueExpr> callsite_stack = caller_outgoing_stack;

  if (call.arg_size() >= 5) {
    auto continuation_expr = summarizeSpecializedCallArg(
        call, 4, dl, slot_ids, stack_cell_ids, callsite_slots, callsite_stack,
        caller_argument_map);
    info.continuation_pc =
        resolveSpecializedExprToConstant(continuation_expr, callsite_slots,
                                         callsite_stack);
  }
  if (!info.continuation_pc)
    info.continuation_pc = inferLiftedCallContinuationPc(call);
  if (info.continuation_pc.has_value()) {
    seedNamedSlotFact(slot_ids, "RETURN_PC", *info.continuation_pc,
                      callsite_slots);
    specializeFactStateToFixpoint(callsite_slots, callsite_stack,
                                  &caller_argument_map, slot_ids,
                                  stack_cell_ids);
  }

  if (call.arg_size() >= 3) {
    auto direct_target = summarizeValueExpr(call.getArgOperand(2), dl);
    annotateExprSlots(direct_target, slot_ids);
    annotateExprStackCells(direct_target, stack_cell_ids, slot_ids);
    auto specialized_target = specializeExprToFixpoint(
        direct_target, callsite_slots, &callsite_stack, &caller_argument_map,
        slot_ids, stack_cell_ids);
    info.target_expr = specialized_target;
    info.target_source = exprEquals(specialized_target, direct_target)
                             ? VirtualDispatchResolutionSource::kDirect
                             : VirtualDispatchResolutionSource::
                                   kHelperArgumentSpecialization;
    info.target_pc =
        resolveSpecializedExprToConstant(specialized_target, callsite_slots,
                                         callsite_stack);
  }
  return info;
}

void summarizeCallSites(llvm::Module &M, VirtualMachineModel &model,
                        const BinaryMemoryMap &binary_memory) {
  auto target_arch = targetArchForModule(M);
  auto slot_ids = buildSlotIdMap(model);
  auto slot_info = buildSlotInfoMap(model);
  auto stack_cell_ids = buildStackCellIdMap(model);
  auto stack_cell_info = buildStackCellInfoMap(model);
  std::map<std::string, size_t> handler_index;
  for (size_t i = 0; i < model.handlers().size(); ++i)
    handler_index.emplace(model.handlers()[i].function_name, i);

  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_maps(
      model.handlers().size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_stack_maps(
      model.handlers().size());
  for (size_t i = 0; i < model.handlers().size(); ++i) {
    outgoing_maps[i] = factMapFor(model.handlers()[i].outgoing_facts);
    outgoing_stack_maps[i] =
        stackFactMapFor(model.handlers()[i].outgoing_stack_facts);
  }

  auto &handlers = model.mutableHandlers();
  const auto &dl = M.getDataLayout();
  for (auto &summary : handlers) {
    for (auto &callsite : summary.callsites) {
      callsite.specialized_target = callsite.target;
      callsite.specialized_target_source =
          VirtualDispatchResolutionSource::kUnknown;
      callsite.resolved_target_pc.reset();
      callsite.recovered_entry_pc.reset();
      callsite.continuation_pc.reset();
      callsite.is_executable_in_image = false;
      callsite.is_decodable_entry = false;
      callsite.target_function_name.reset();
      callsite.recovered_target_function_name.reset();
      callsite.return_slot_facts.clear();
      callsite.return_stack_facts.clear();
      callsite.unresolved_reason.clear();
    }

    auto *caller_fn = M.getFunction(summary.function_name);
    if (!caller_fn)
      continue;

    auto caller_incoming = factMapFor(summary.incoming_facts);
    auto caller_incoming_stack = stackFactMapFor(summary.incoming_stack_facts);
    auto caller_outgoing = factMapFor(summary.outgoing_facts);
    auto caller_outgoing_stack = stackFactMapFor(summary.outgoing_stack_facts);
    auto caller_argument_map = argumentFactMapFor(summary.incoming_argument_facts);
    size_t callsite_index = 0;

    for (auto &BB : *caller_fn) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || !isCallSiteHelper(*callee))
          continue;
        if (callsite_index >= summary.callsites.size())
          continue;

        auto &callsite_summary = summary.callsites[callsite_index++];
        auto local_state = computeLocalFactsBeforeCall(
            *call, dl, slot_ids, stack_cell_ids, caller_incoming,
            caller_incoming_stack, caller_argument_map);
        auto resolved = resolveCallSiteInfo(
            *call, dl, slot_ids, stack_cell_ids, local_state.slot_facts,
            local_state.stack_facts, caller_argument_map);
        if (!resolved.target_pc.has_value()) {
          auto outgoing_local_state = computeLocalFactsBeforeCall(
              *call, dl, slot_ids, stack_cell_ids, caller_outgoing,
              caller_outgoing_stack, caller_argument_map);
          auto outgoing_resolved = resolveCallSiteInfo(
              *call, dl, slot_ids, stack_cell_ids,
              outgoing_local_state.slot_facts, outgoing_local_state.stack_facts,
              caller_argument_map);
          vmModelImportDebugLog("callsite-fallback handler=" +
                                summary.function_name + " incoming=" +
                                renderVirtualValueExpr(resolved.target_expr) +
                                " outgoing=" +
                                renderVirtualValueExpr(
                                    outgoing_resolved.target_expr) +
                                " incoming_pc=" +
                                (resolved.target_pc
                                     ? ("0x" +
                                        llvm::utohexstr(*resolved.target_pc))
                                     : std::string("<none>")) +
                                " outgoing_pc=" +
                                (outgoing_resolved.target_pc
                                     ? ("0x" + llvm::utohexstr(
                                                  *outgoing_resolved.target_pc))
                                     : std::string("<none>")));
          if (outgoing_resolved.target_pc.has_value())
            resolved = std::move(outgoing_resolved);
        }

        bool target_is_executable =
            resolved.target_pc.has_value() &&
            isTargetExecutable(binary_memory, *resolved.target_pc);
        if ((!resolved.target_pc.has_value() || !target_is_executable) &&
            resolved.continuation_pc.has_value()) {
          if (auto next_pc_resolved = resolveCallSiteInfoFromOutgoingNextPc(
                  summary, callsite_summary.target, resolved.continuation_pc,
                  slot_ids)) {
            vmModelImportDebugLog(
                "callsite-nextpc-fallback handler=" + summary.function_name +
                " direct=" + renderVirtualValueExpr(callsite_summary.target) +
                " outgoing_next_pc=" +
                renderVirtualValueExpr(next_pc_resolved->target_expr) +
                " target_pc=0x" +
                llvm::utohexstr(*next_pc_resolved->target_pc));
            resolved = std::move(*next_pc_resolved);
          }
        }
        callsite_summary.specialized_target = resolved.target_expr;
        callsite_summary.specialized_target_source = resolved.target_source;
        callsite_summary.resolved_target_pc = resolved.target_pc;
        callsite_summary.continuation_pc = resolved.continuation_pc;

        if (!resolved.target_pc.has_value()) {
          callsite_summary.unresolved_reason = "call_target_unresolved";
          continue;
        }
        callsite_summary.is_executable_in_image =
            isTargetExecutable(binary_memory, *resolved.target_pc);
        if (!callsite_summary.is_executable_in_image) {
          callsite_summary.unresolved_reason = "call_target_not_executable";
          continue;
        }

        auto decodable_entry = isTargetDecodableEntry(
            binary_memory, *resolved.target_pc, target_arch);
        const auto *target_summary =
            lookupHandlerByEntryVA(model, *resolved.target_pc);
        std::optional<uint64_t> nearby_entry_pc;
        const VirtualHandlerSummary *nearby_summary = nullptr;
        if (target_summary) {
          callsite_summary.is_decodable_entry = true;
        } else if (decodable_entry.has_value()) {
          callsite_summary.is_decodable_entry = *decodable_entry;
          if (!*decodable_entry) {
            nearby_summary = findNearbyLiftedHandlerEntry(
                model, *resolved.target_pc, target_arch);
            if (nearby_summary && nearby_summary->entry_va.has_value()) {
              nearby_entry_pc = nearby_summary->entry_va;
              callsite_summary.recovered_target_function_name =
                  nearby_summary->function_name;
            } else {
              nearby_entry_pc = findNearbyExecutableEntry(
                  binary_memory, *resolved.target_pc, target_arch);
              if (nearby_entry_pc) {
                nearby_summary = lookupHandlerByEntryVA(model, *nearby_entry_pc);
                if (nearby_summary) {
                  callsite_summary.recovered_target_function_name =
                      nearby_summary->function_name;
                }
              }
            }
            callsite_summary.recovered_entry_pc = nearby_entry_pc;
          }
        }
        if (!target_summary && !nearby_summary) {
          if (nearby_entry_pc) {
            callsite_summary.unresolved_reason = "call_target_nearby_unlifted";
          } else {
            callsite_summary.unresolved_reason =
                (decodable_entry.has_value() && !*decodable_entry)
                    ? "call_target_undecodable"
                    : "call_target_unlifted";
          }
          continue;
        }

        const auto *localized_target_summary =
            target_summary ? target_summary : nearby_summary;
        if (!target_summary) {
          if (nearby_summary)
            callsite_summary.unresolved_reason = "call_target_mid_instruction";
        } else {
          callsite_summary.target_function_name = target_summary->function_name;
        }

        llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
        visiting.insert(caller_fn);
        auto localized = computeResolvedCallTargetOutgoingFacts(
            *call, model, *localized_target_summary, slot_info, stack_cell_info,
            slot_ids, stack_cell_ids, dl, handler_index, outgoing_maps,
            outgoing_stack_maps, caller_outgoing, caller_outgoing_stack,
            caller_argument_map, resolved, binary_memory, /*depth=*/1,
            visiting);
        if (!localized) {
          if (callsite_summary.unresolved_reason.empty())
            callsite_summary.unresolved_reason = "call_return_unresolved";
          continue;
        }

        llvm::SmallDenseSet<unsigned, 16> written_slots(
            localized_target_summary->written_slot_ids.begin(),
            localized_target_summary->written_slot_ids.end());
        auto written_stack_cells = rebaseWrittenStackCellIds(
            model, localized->outgoing_slots,
            localized_target_summary->written_stack_cell_ids);

        for (const auto &[slot_id, value] : localized->outgoing_slots) {
          if (!written_slots.empty() && !written_slots.count(slot_id))
            continue;
          auto normalized = normalizeLocalizedExprForCaller(
              value, *caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
              caller_outgoing_stack, nullptr, caller_argument_map);
          if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
              !isBoundedLocalizedTransferExpr(*normalized)) {
            continue;
          }
          callsite_summary.return_slot_facts.push_back(
              VirtualSlotFact{slot_id, std::move(*normalized)});
        }
        for (const auto &[cell_id, value] : localized->outgoing_stack) {
          if (!written_stack_cells.empty() &&
              !written_stack_cells.count(cell_id)) {
            continue;
          }
          auto normalized = normalizeLocalizedExprForCaller(
              value, *caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
              caller_outgoing_stack, nullptr, caller_argument_map);
          if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
              !isBoundedLocalizedTransferExpr(*normalized)) {
            continue;
          }
          callsite_summary.return_stack_facts.push_back(
              VirtualStackFact{cell_id, std::move(*normalized)});
        }

        if (callsite_summary.unresolved_reason.empty() &&
            callsite_summary.continuation_pc.has_value() &&
            callsite_summary.return_slot_facts.empty() &&
            callsite_summary.return_stack_facts.empty()) {
          callsite_summary.unresolved_reason = "call_return_unresolved";
        }
      }
    }
  }
}

}  // namespace omill::virtual_model::detail

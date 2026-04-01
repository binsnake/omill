#include "Analysis/VirtualModel/Internal.h"

#include "omill/Analysis/VMTraceMap.h"

#include <llvm/ADT/STLExtras.h>
#include <llvm/IR/Module.h>

#include <optional>
#include <string>

namespace omill::virtual_model::detail {

namespace {

static std::optional<unsigned> lookupNamedSummarySlotId(
    const VirtualHandlerSummary &summary, llvm::StringRef base_name) {
  for (const auto &slot : summary.state_slots) {
    if (slot.base_name == base_name && slot.offset == 0 &&
        slot.canonical_id.has_value()) {
      return slot.canonical_id;
    }
  }
  return std::nullopt;
}

static const VirtualSlotFact *lookupSlotFactById(
    llvm::ArrayRef<VirtualSlotFact> facts, unsigned slot_id) {
  auto it = llvm::find_if(facts, [&](const VirtualSlotFact &fact) {
    return fact.slot_id == slot_id;
  });
  return it == facts.end() ? nullptr : &*it;
}

static bool exprMatchesSlot(const VirtualValueExpr &expr, unsigned slot_id) {
  return expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value() &&
         *expr.slot_id == slot_id;
}

static bool exprMatchesBasePlusOrMinusConst(const VirtualValueExpr &expr,
                                            unsigned slot_id,
                                            int64_t &delta) {
  if (exprMatchesSlot(expr, slot_id)) {
    delta = 0;
    return true;
  }

  if (expr.kind == VirtualExprKind::kAdd && expr.operands.size() == 2) {
    if (exprMatchesSlot(expr.operands[0], slot_id) &&
        expr.operands[1].constant.has_value()) {
      delta = static_cast<int64_t>(*expr.operands[1].constant);
      return true;
    }
    if (expr.operands[0].constant.has_value() &&
        exprMatchesSlot(expr.operands[1], slot_id)) {
      delta = static_cast<int64_t>(*expr.operands[0].constant);
      return true;
    }
  }

  if (expr.kind == VirtualExprKind::kSub && expr.operands.size() == 2 &&
      exprMatchesSlot(expr.operands[0], slot_id) &&
      expr.operands[1].constant.has_value()) {
    delta = -static_cast<int64_t>(*expr.operands[1].constant);
    return true;
  }

  return false;
}

static VirtualValueExpr unknownVipExpr() {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kUnknown;
  return expr;
}

static std::optional<uint64_t> resolveExprFromSummary(
    const VirtualValueExpr &expr, const VirtualHandlerSummary &summary) {
  if (auto resolved =
          evaluateVirtualExpr(expr, summary.outgoing_facts,
                              summary.outgoing_stack_facts)) {
    return resolved;
  }
  for (const auto &state : expandIncomingContextStates(summary)) {
    if (auto resolved =
            evaluateVirtualExpr(expr, state.slot_facts, state.stack_facts)) {
      return resolved;
    }
  }
  if (summary.incoming_slot_phis.empty() && summary.incoming_stack_phis.empty()) {
    if (auto resolved =
            evaluateVirtualExpr(expr, summary.incoming_facts,
                                summary.incoming_stack_facts)) {
      return resolved;
    }
  }
  return std::nullopt;
}

static VirtualInstructionPointerSourceKind detectVipSourceKind(
    const VirtualValueExpr &expr) {
  if (containsMemoryReadExpr(expr))
    return VirtualInstructionPointerSourceKind::kBytecodeRead;
  if (containsStackCellExpr(expr))
    return VirtualInstructionPointerSourceKind::kStackCell;
  if (expr.kind == VirtualExprKind::kStateSlot || expr.slot_id.has_value() ||
      (expr.state_base_name.has_value() &&
       (*expr.state_base_name == "NEXT_PC" || *expr.state_base_name == "VIP" ||
        *expr.state_base_name == "VPC"))) {
    return VirtualInstructionPointerSourceKind::kNamedSlot;
  }
  return VirtualInstructionPointerSourceKind::kDispatchOperand;
}

static VirtualInstructionPointerSummary buildVipSummary(
    const VirtualHandlerSummary &summary, const VirtualValueExpr &before,
    const VirtualValueExpr &after) {
  VirtualInstructionPointerSummary vip;
  vip.expr_before_dispatch = before;
  vip.expr_after_dispatch = after;
  vip.source_kind = detectVipSourceKind(after);
  vip.symbolic = !isUnknownLikeExpr(after);
  if (after.slot_id.has_value())
    vip.slot_id = after.slot_id;
  if (after.stack_cell_id.has_value())
    vip.stack_cell_id = after.stack_cell_id;
  if (auto resolved = resolveExprFromSummary(after, summary)) {
    vip.resolved_pc = resolved;
    vip.symbolic = false;
  }
  return vip;
}

static VirtualInstructionPointerSummary buildContinuationVip(
    std::optional<uint64_t> continuation_pc) {
  VirtualInstructionPointerSummary vip;
  if (!continuation_pc)
    return vip;
  vip.expr_before_dispatch = constantExpr(*continuation_pc, 64);
  vip.expr_after_dispatch = constantExpr(*continuation_pc, 64);
  vip.resolved_pc = continuation_pc;
  vip.source_kind = VirtualInstructionPointerSourceKind::kNamedSlot;
  return vip;
}

struct ContinuationLocationSummary {
  std::optional<unsigned> slot_id;
  std::optional<unsigned> stack_cell_id;
};

static bool exprReferencesSlotId(const VirtualValueExpr &expr,
                                 unsigned slot_id) {
  if (expr.slot_id && *expr.slot_id == slot_id)
    return true;
  return llvm::any_of(expr.operands, [&](const VirtualValueExpr &operand) {
    return exprReferencesSlotId(operand, slot_id);
  });
}

static ContinuationLocationSummary inferContinuationLocationFromSummary(
    const VirtualHandlerSummary &summary, std::optional<uint64_t> continuation_pc) {
  ContinuationLocationSummary location;
  location.slot_id = lookupNamedSummarySlotId(summary, "RETURN_PC");

  if (continuation_pc) {
    auto stack_it = llvm::find_if(
        summary.outgoing_stack_facts, [&](const VirtualStackFact &fact) {
          return fact.value.constant && *fact.value.constant == *continuation_pc;
        });
    if (stack_it != summary.outgoing_stack_facts.end())
      location.stack_cell_id = stack_it->cell_id;
  }

  if (!location.stack_cell_id && location.slot_id) {
    auto stack_it = llvm::find_if(
        summary.outgoing_stack_facts, [&](const VirtualStackFact &fact) {
          return exprReferencesSlotId(fact.value, *location.slot_id);
        });
    if (stack_it != summary.outgoing_stack_facts.end())
      location.stack_cell_id = stack_it->cell_id;
  }

  return location;
}

static ContinuationLocationSummary inferContinuationLocationFromCallsite(
    const VirtualHandlerSummary &summary, const VirtualCallSiteSummary &callsite) {
  auto location =
      inferContinuationLocationFromSummary(summary, callsite.continuation_pc);
  if (callsite.continuation_slot_id)
    location.slot_id = callsite.continuation_slot_id;
  if (callsite.continuation_stack_cell_id)
    location.stack_cell_id = callsite.continuation_stack_cell_id;
  const auto matches_continuation = [&](const VirtualValueExpr &expr) {
    if (callsite.continuation_pc && expr.constant &&
        *expr.constant == *callsite.continuation_pc) {
      return true;
    }
    return location.slot_id &&
           exprReferencesSlotId(expr, *location.slot_id);
  };

  auto stack_it = llvm::find_if(callsite.return_stack_facts,
                                [&](const VirtualStackFact &fact) {
                                  return matches_continuation(fact.value);
                                });
  if (stack_it != callsite.return_stack_facts.end())
    location.stack_cell_id = stack_it->cell_id;

  auto slot_it = llvm::find_if(callsite.return_slot_facts,
                               [&](const VirtualSlotFact &fact) {
                                 return matches_continuation(fact.value);
                               });
  if (slot_it != callsite.return_slot_facts.end())
    location.slot_id = slot_it->slot_id;

  return location;
}

static void applyContinuationLocation(VirtualInstructionPointerSummary &vip,
                                      const ContinuationLocationSummary &location) {
  if (location.slot_id)
    vip.slot_id = location.slot_id;
  if (location.stack_cell_id)
    vip.stack_cell_id = location.stack_cell_id;
  if (location.stack_cell_id) {
    vip.source_kind = VirtualInstructionPointerSourceKind::kStackCell;
  } else if (location.slot_id) {
    vip.source_kind = VirtualInstructionPointerSourceKind::kNamedSlot;
  }
}

static std::pair<VirtualExitStackDeltaKind, std::optional<int64_t>>
classifyStackDelta(const VirtualHandlerSummary &summary) {
  std::optional<unsigned> sp_slot_id;
  for (llvm::StringRef sp_name : {"RSP", "SP", "sp"}) {
    if (auto slot_id = lookupNamedSummarySlotId(summary, sp_name)) {
      sp_slot_id = slot_id;
      break;
    }
  }
  if (!sp_slot_id)
    return {VirtualExitStackDeltaKind::kUnknown, std::nullopt};

  const auto *outgoing = lookupSlotFactById(summary.outgoing_facts, *sp_slot_id);
  if (!outgoing)
    return {VirtualExitStackDeltaKind::kUnknown, std::nullopt};

  int64_t delta = 0;
  if (!exprMatchesBasePlusOrMinusConst(outgoing->value, *sp_slot_id, delta)) {
    return {VirtualExitStackDeltaKind::kUnknown, std::nullopt};
  }

  if (delta == 0)
    return {VirtualExitStackDeltaKind::kUnchanged, delta};
  if (delta == 8)
    return {VirtualExitStackDeltaKind::kPlusPointer, delta};
  if (delta == 16)
    return {VirtualExitStackDeltaKind::kPlusDoublePointer, delta};
  return {VirtualExitStackDeltaKind::kOther, delta};
}

static std::optional<uint64_t> resolveReturnPcFromSummary(
    const VirtualHandlerSummary &summary) {
  auto return_pc_slot_id = lookupNamedSummarySlotId(summary, "RETURN_PC");
  if (!return_pc_slot_id)
    return std::nullopt;
  const auto *return_pc_fact =
      lookupSlotFactById(summary.outgoing_facts, *return_pc_slot_id);
  if (!return_pc_fact)
    return std::nullopt;
  return resolveExprFromSummary(return_pc_fact->value, summary);
}

static bool isLiftedHandlerTarget(const VirtualMachineModel &model,
                                  const std::optional<uint64_t> &target_pc,
                                  const std::optional<std::string> &target_name) {
  if (target_name.has_value() && model.lookupHandler(*target_name))
    return true;
  if (target_pc.has_value() && lookupHandlerByEntryVA(model, *target_pc))
    return true;
  return false;
}

static bool isBoundaryTarget(const VirtualMachineModel &model,
                             const BinaryMemoryMap &binary_memory,
                             const std::optional<uint64_t> &target_pc) {
  return target_pc.has_value() &&
         resolveBoundaryNameForTarget(model, binary_memory, *target_pc)
             .has_value();
}

static VirtualExitSummary classifyDispatchExit(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    const VirtualHandlerSummary &summary, const VirtualDispatchSummary &dispatch) {
  VirtualExitSummary exit;
  const auto [stack_delta_kind, stack_delta_bytes] = classifyStackDelta(summary);
  exit.stack_delta_kind = stack_delta_kind;
  exit.stack_delta_bytes = stack_delta_bytes;
  exit.continuation_pc = resolveReturnPcFromSummary(summary);
  exit.continuation_vip = buildContinuationVip(exit.continuation_pc);
  applyContinuationLocation(
      exit.continuation_vip,
      inferContinuationLocationFromSummary(summary, exit.continuation_pc));

  if (llvm::any_of(dispatch.successors, [](const VirtualDispatchSuccessorSummary &s) {
        return s.kind == VirtualSuccessorKind::kLiftedHandler ||
               s.kind == VirtualSuccessorKind::kLiftedBlock ||
               s.kind == VirtualSuccessorKind::kTraceBlock;
      })) {
    exit.disposition = VirtualExitDisposition::kStayInVm;
    return exit;
  }

  if (llvm::any_of(dispatch.successors, [](const VirtualDispatchSuccessorSummary &s) {
        return s.kind == VirtualSuccessorKind::kProtectedBoundary;
      })) {
    const bool reenters = exit.continuation_pc.has_value() &&
                          (stack_delta_kind ==
                               VirtualExitStackDeltaKind::kPlusPointer ||
                           stack_delta_kind ==
                               VirtualExitStackDeltaKind::kPlusDoublePointer);
    exit.disposition = reenters
                           ? VirtualExitDisposition::kVmExitNativeCallReenter
                           : VirtualExitDisposition::kVmExitTerminal;
    exit.is_partial_exit = reenters;
    exit.reenters_vm = reenters;
    exit.is_full_exit = !reenters;
    return exit;
  }

  auto first_unknown = llvm::find_if(
      dispatch.successors, [](const VirtualDispatchSuccessorSummary &successor) {
        return successor.kind == VirtualSuccessorKind::kUnknown &&
               successor.target_pc != 0;
      });
  if (first_unknown != dispatch.successors.end()) {
    if (exit.continuation_pc.has_value()) {
      exit.disposition = VirtualExitDisposition::kVmExitNativeCallReenter;
      exit.native_target_pc = first_unknown->target_pc;
      exit.is_partial_exit = true;
      exit.reenters_vm = true;
    } else {
      exit.disposition = VirtualExitDisposition::kVmExitTerminal;
      exit.native_target_pc = first_unknown->target_pc;
      exit.is_full_exit = true;
    }
    return exit;
  }

  if (!dispatch.unresolved_reason.empty() && exit.continuation_pc.has_value()) {
    exit.disposition = VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
    exit.is_partial_exit = true;
  }
  return exit;
}

static VirtualExitSummary classifyCallsiteExit(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    const VirtualHandlerSummary &summary, const VirtualCallSiteSummary &callsite) {
  VirtualExitSummary exit;
  const auto [stack_delta_kind, stack_delta_bytes] = classifyStackDelta(summary);
  exit.stack_delta_kind = stack_delta_kind;
  exit.stack_delta_bytes = stack_delta_bytes;
  exit.continuation_pc = callsite.continuation_pc;
  exit.continuation_vip = buildContinuationVip(callsite.continuation_pc);
  applyContinuationLocation(exit.continuation_vip,
                            inferContinuationLocationFromCallsite(summary,
                                                                 callsite));

  const auto effective_target_pc =
      callsite.resolved_target_pc ? callsite.resolved_target_pc
                                  : callsite.recovered_entry_pc;
  const auto effective_target_name =
      callsite.target_function_name ? callsite.target_function_name
                                    : callsite.recovered_target_function_name;

  if (effective_target_pc.has_value() &&
      isBoundaryTarget(model, binary_memory, effective_target_pc)) {
    exit.disposition = summary.called_boundaries.empty()
                           ? VirtualExitDisposition::kVmEnter
                           : VirtualExitDisposition::kNestedVmEnter;
    return exit;
  }

  if (isLiftedHandlerTarget(model, effective_target_pc, effective_target_name)) {
    exit.disposition = VirtualExitDisposition::kStayInVm;
    return exit;
  }

  if (callsite.continuation_pc.has_value()) {
    exit.disposition = VirtualExitDisposition::kVmExitNativeCallReenter;
    exit.native_target_pc = effective_target_pc;
    exit.is_partial_exit = true;
    exit.reenters_vm = true;
    return exit;
  }

  if (effective_target_pc.has_value() || !callsite.unresolved_reason.empty()) {
    exit.disposition = VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
    exit.native_target_pc = effective_target_pc;
    exit.is_partial_exit = true;
  }
  return exit;
}

static void corroborateExitFromTrace(const VMTraceMap &trace_map,
                                     std::optional<uint64_t> handler_va,
                                     VirtualExitSummary &exit) {
  if (!handler_va)
    return;
  auto records = trace_map.getTraceRecords(*handler_va);
  if (records.empty())
    return;

  for (const auto &record : records) {
    if (record.native_target_va != 0) {
      if (exit.disposition == VirtualExitDisposition::kUnknown ||
          exit.disposition == VirtualExitDisposition::kVmExitTerminal) {
        exit.disposition = VirtualExitDisposition::kVmExitNativeCallReenter;
        exit.native_target_pc = record.native_target_va;
        exit.is_partial_exit = true;
        exit.reenters_vm = !record.successors.empty();
        exit.is_full_exit = false;
      }
      exit.corroborated_by_trace = true;
      return;
    }
    if (record.is_vmexit &&
        exit.disposition == VirtualExitDisposition::kUnknown) {
      exit.disposition = VirtualExitDisposition::kVmExitTerminal;
      exit.is_full_exit = true;
      exit.corroborated_by_trace = true;
      return;
    }
  }
}

}  // namespace

void summarizeVirtualInstructionPointers(llvm::Module &M,
                                         VirtualMachineModel &model,
                                         const BinaryMemoryMap &binary_memory) {
  (void)M;
  (void)binary_memory;
  auto &handlers = model.mutableHandlers();
  for (auto &summary : handlers) {
    auto next_pc_slot_id = lookupNamedSummarySlotId(summary, "NEXT_PC");
    const auto *incoming_next_pc_fact =
        next_pc_slot_id ? lookupSlotFactById(summary.incoming_facts, *next_pc_slot_id)
                        : nullptr;
    const auto *outgoing_next_pc_fact =
        next_pc_slot_id ? lookupSlotFactById(summary.outgoing_facts, *next_pc_slot_id)
                        : nullptr;

    VirtualValueExpr vip_before =
        incoming_next_pc_fact ? incoming_next_pc_fact->value : unknownVipExpr();
    VirtualValueExpr vip_after =
        outgoing_next_pc_fact ? outgoing_next_pc_fact->value : unknownVipExpr();

    if (isUnknownLikeExpr(vip_before) && !summary.dispatches.empty())
      vip_before = summary.dispatches.front().target;
    if (isUnknownLikeExpr(vip_after) && !summary.dispatches.empty())
      vip_after = summary.dispatches.front().target;

    summary.canonical_vip = buildVipSummary(summary, vip_before, vip_after);
    if (next_pc_slot_id) {
      summary.canonical_vip.slot_id = *next_pc_slot_id;
      summary.canonical_vip.source_kind =
          VirtualInstructionPointerSourceKind::kNamedSlot;
    }

    for (auto &dispatch : summary.dispatches) {
      auto before = isUnknownLikeExpr(summary.canonical_vip.expr_before_dispatch)
                        ? dispatch.target
                        : summary.canonical_vip.expr_before_dispatch;
      auto after = outgoing_next_pc_fact ? outgoing_next_pc_fact->value
                                         : dispatch.specialized_target;
      if (isUnknownLikeExpr(after))
        after = dispatch.target;
      dispatch.vip = buildVipSummary(summary, before, after);
      if (next_pc_slot_id) {
        dispatch.vip.slot_id = *next_pc_slot_id;
        dispatch.vip.source_kind =
            VirtualInstructionPointerSourceKind::kNamedSlot;
      }
    }

    for (auto &callsite : summary.callsites) {
      callsite.vip = summary.canonical_vip;
    }
  }
}

void summarizeVirtualExits(llvm::Module &M, VirtualMachineModel &model,
                           const BinaryMemoryMap &binary_memory,
                           const VMTraceMap *trace_map) {
  (void)M;
  auto &handlers = model.mutableHandlers();
  for (auto &summary : handlers) {
    auto next_pc_slot_id = lookupNamedSummarySlotId(summary, "NEXT_PC");
    const auto *outgoing_next_pc_fact =
        next_pc_slot_id ? lookupSlotFactById(summary.outgoing_facts, *next_pc_slot_id)
                        : nullptr;
    for (auto &dispatch : summary.dispatches) {
      auto after = outgoing_next_pc_fact ? outgoing_next_pc_fact->value
                                         : dispatch.specialized_target;
      if (isUnknownLikeExpr(after))
        after = dispatch.target;
      dispatch.vip = buildVipSummary(summary, summary.canonical_vip.expr_before_dispatch,
                                     after);
      if (next_pc_slot_id) {
        dispatch.vip.slot_id = *next_pc_slot_id;
        dispatch.vip.source_kind =
            VirtualInstructionPointerSourceKind::kNamedSlot;
      }
      dispatch.exit = classifyDispatchExit(model, binary_memory, summary, dispatch);
      if (trace_map)
        corroborateExitFromTrace(*trace_map, summary.entry_va, dispatch.exit);
    }
    for (auto &callsite : summary.callsites) {
      callsite.vip = summary.canonical_vip;
      if (callsite.continuation_pc.has_value()) {
        callsite.vip.expr_after_dispatch =
            constantExpr(*callsite.continuation_pc, 64);
        callsite.vip.resolved_pc = callsite.continuation_pc;
        callsite.vip.symbolic = false;
      }
      callsite.exit = classifyCallsiteExit(model, binary_memory, summary, callsite);
      if (trace_map)
        corroborateExitFromTrace(*trace_map, summary.entry_va, callsite.exit);
    }
  }
}

}  // namespace omill::virtual_model::detail

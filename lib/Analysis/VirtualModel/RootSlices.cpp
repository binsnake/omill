#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/Twine.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <cstdlib>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "omill/Utils/LiftedNames.h"

namespace omill::virtual_model::detail {

namespace {

static bool terminalBoundaryRecoveryModeEnabled() {
  const char *mode = std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY");
  if (mode && mode[0] != '\0')
    return true;
  const char *root = std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA");
  return root && root[0] != '\0';
}

static std::string normalizeBoundaryNameForRootSlice(llvm::StringRef name) {
  return name.lower();
}

static std::optional<std::string> importBoundaryName(
    const BinaryMemoryMap &binary_memory, std::optional<uint64_t> target_pc) {
  if (!target_pc.has_value())
    return std::nullopt;
  auto *entry = lookupImportTarget(binary_memory, *target_pc);
  if (!entry)
    return std::nullopt;
  return entry->module + "!" + entry->function;
}

static bool isTerminalExitDisposition(
    VirtualExitDisposition disposition) {
  switch (disposition) {
    case VirtualExitDisposition::kVmExitTerminal:
    case VirtualExitDisposition::kVmExitNativeCallReenter:
    case VirtualExitDisposition::kVmExitNativeExecUnknownReturn:
      return true;
    case VirtualExitDisposition::kUnknown:
    case VirtualExitDisposition::kStayInVm:
    case VirtualExitDisposition::kVmEnter:
    case VirtualExitDisposition::kNestedVmEnter:
      return false;
  }
  return false;
}

static bool isOpenExecutableFrontierReason(VirtualRootFrontierKind kind,
                                           llvm::StringRef reason) {
  switch (kind) {
    case VirtualRootFrontierKind::kCall:
      return reason == "call_target_unlifted" ||
             reason == "call_target_nearby_unlifted" ||
             reason == "call_target_desynchronized" ||
             reason == "call_target_undecodable";
    case VirtualRootFrontierKind::kDispatch:
      return reason == "dispatch_target_unlifted" ||
             reason == "dispatch_target_nearby_unlifted" ||
             reason == "dispatch_target_desynchronized";
  }
  return false;
}

static uint64_t nearbyEntrySearchWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 4;
    case TargetArch::kX86_64:
    default:
      return 64;
  }
}

template <typename HandlerPtr>
static HandlerPtr findNearbyLiftedHandlerEntry(
    const std::map<uint64_t, HandlerPtr> &handler_by_pc, uint64_t target_pc,
    TargetArch arch) {
  const auto window = nearbyEntrySearchWindow(arch);
  HandlerPtr best = nullptr;
  uint64_t best_distance = std::numeric_limits<uint64_t>::max();

  auto consider = [&](auto it) {
    if (it == handler_by_pc.end())
      return;
    const uint64_t candidate_pc = it->first;
    const uint64_t distance =
        candidate_pc > target_pc ? (candidate_pc - target_pc)
                                 : (target_pc - candidate_pc);
    if (distance > window)
      return;
    if (!best || distance < best_distance ||
        (distance == best_distance && candidate_pc < target_pc)) {
      best = it->second;
      best_distance = distance;
    }
  };

  auto it = handler_by_pc.lower_bound(target_pc);
  consider(it);
  if (it != handler_by_pc.begin())
    consider(std::prev(it));
  return best;
}

struct DispatchFrontierClassification {
  std::string reason;
  std::optional<uint64_t> canonical_target_va;
};

static DispatchFrontierClassification classifyUnknownDispatchFrontier(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch target_arch) {
  DispatchFrontierClassification classification;
  classification.reason = "missing_lifted_target";
  if (!target_pc)
    return classification;

  if (!isTargetExecutable(binary_memory, target_pc)) {
    classification.reason = "dispatch_target_not_executable";
    return classification;
  }

  auto decodable_entry =
      isTargetDecodableEntry(binary_memory, target_pc, target_arch);
    if (decodable_entry.has_value() && !*decodable_entry) {
      if (auto nearby_entry =
              findNearbyExecutableEntry(binary_memory, target_pc, target_arch)) {
        classification.reason =
            isLikelyDisassemblyDesyncTarget(binary_memory, target_pc,
                                           nearby_entry, target_arch)
                ? "dispatch_target_desynchronized"
                : "dispatch_target_nearby_unlifted";
        classification.canonical_target_va = nearby_entry;
      } else {
        classification.reason = "dispatch_target_undecodable";
      }
    return classification;
  }

  classification.reason = "dispatch_target_unlifted";
  return classification;
}

static std::optional<unsigned> lookupSummaryNamedSlotId(
    const VirtualHandlerSummary &summary, llvm::StringRef base_name) {
  for (const auto &slot : summary.state_slots) {
    if (slot.base_name != base_name || slot.offset != 0 ||
        !slot.canonical_id.has_value()) {
      continue;
    }
    return slot.canonical_id;
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
                                            unsigned slot_id, int64_t &delta) {
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

static std::optional<unsigned> lookupSummarySlotId(
    const VirtualHandlerSummary &summary, llvm::StringRef base_name,
    int64_t offset) {
  for (const auto &slot : summary.state_slots) {
    if (slot.base_name != base_name || slot.offset != offset ||
        !slot.canonical_id.has_value()) {
      continue;
    }
    return slot.canonical_id;
  }
  return std::nullopt;
}

static std::optional<uint64_t> resolveTerminalNextPcFromFacts(
    const VirtualHandlerSummary &summary) {
  auto next_pc_slot_id = lookupSummaryNamedSlotId(summary, "NEXT_PC");
  if (!next_pc_slot_id)
    return std::nullopt;

  const auto *next_pc_fact =
      lookupSlotFactById(summary.outgoing_facts, *next_pc_slot_id);
  if (!next_pc_fact)
    return std::nullopt;

  if (auto resolved = evaluateVirtualExpr(next_pc_fact->value,
                                          summary.outgoing_facts,
                                          summary.outgoing_stack_facts)) {
    return resolved;
  }
  for (const auto &state : expandIncomingContextStates(summary)) {
    if (auto resolved = evaluateVirtualExpr(next_pc_fact->value,
                                            state.slot_facts,
                                            state.stack_facts)) {
      return resolved;
    }
  }
  if (summary.incoming_slot_phis.empty() && summary.incoming_stack_phis.empty()) {
    return evaluateVirtualExpr(next_pc_fact->value, summary.incoming_facts,
                               summary.incoming_stack_facts);
  }
  return std::nullopt;
}

}  // namespace

void summarizeRootSlices(llvm::Module &M, VirtualMachineModel &model,
                         const BinaryMemoryMap &binary_memory) {
  auto target_arch = targetArchForModule(M);
  const bool terminal_boundary_recovery_mode =
      terminalBoundaryRecoveryModeEnabled();
  auto &root_slices = model.mutableRootSlices();
  root_slices.clear();

  const auto &handlers = model.handlers();
  if (handlers.empty())
    return;
  const bool explicit_dirty_scope = llvm::any_of(
      handlers, [](const VirtualHandlerSummary &handler) {
        return handler.is_dirty_seed;
      });

  std::map<std::string, const VirtualHandlerSummary *> handler_by_name;
  std::map<uint64_t, const VirtualHandlerSummary *> handler_by_pc;
  for (const auto &handler : handlers) {
    handler_by_name.emplace(handler.function_name, &handler);
    if (handler.entry_va.has_value())
      handler_by_pc.emplace(*handler.entry_va, &handler);
  }

  auto is_root_slice_member = [](const VirtualHandlerSummary &handler) {
    return handler.entry_va.has_value() || handler.is_output_root ||
           handler.is_specialized || handler.is_candidate ||
           !handler.dispatches.empty() || !handler.called_boundaries.empty() ||
           !handler.callsites.empty();
  };

  auto enqueue_handler =
      [&](const VirtualHandlerSummary *handler, std::optional<uint64_t> vip_pc,
          std::vector<std::pair<const VirtualHandlerSummary *,
                                std::optional<uint64_t>>> &queue,
          std::set<std::string> &queued, std::set<std::string> &reachable) {
    if (!handler)
      return;
    std::string queue_key = handler->function_name;
    if (vip_pc.has_value())
      queue_key += "#0x" + llvm::utohexstr(*vip_pc);
    if (!queued.insert(queue_key).second)
      return;
    if (is_root_slice_member(*handler))
      reachable.insert(handler->function_name);
    queue.push_back({handler, vip_pc});
  };

  auto lookup_handler_by_pc_or_name =
      [&](uint64_t pc) -> const VirtualHandlerSummary * {
        if (!pc)
          return nullptr;
        if (auto it = handler_by_pc.find(pc); it != handler_by_pc.end())
          return it->second;

        auto lifted_name = omill::liftedFunctionName(pc);
        if (auto it = handler_by_name.find(lifted_name);
            it != handler_by_name.end()) {
          return it->second;
        }

        auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
        if (auto it = handler_by_name.find(block_name); it != handler_by_name.end())
          return it->second;

        auto trace_block_name =
            (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
        if (auto it = handler_by_name.find(trace_block_name);
            it != handler_by_name.end()) {
          return it->second;
        }

        return findNearbyLiftedHandlerEntry(handler_by_pc, pc, target_arch);
      };

  auto lookup_exact_lifted_leaf =
      [&](std::optional<uint64_t> pc,
          const std::optional<std::string> &function_name)
          -> llvm::Function * {
        if (function_name.has_value()) {
          if (auto *exact = M.getFunction(*function_name);
              exact && !exact->isDeclaration()) {
            return exact;
          }
        }
        if (pc.has_value()) {
          if (auto *exact = findLiftedOrCoveredFunctionByPC(M, *pc);
              exact && !exact->isDeclaration()) {
            return exact;
          }
        }
        return nullptr;
      };

  auto has_lifted_direct_callee =
      [&](const VirtualHandlerSummary &handler) -> bool {
    for (const auto &callee_name : handler.direct_callees) {
      auto it = handler_by_name.find(callee_name);
      if (it == handler_by_name.end())
        continue;
      if (it->second->entry_va.has_value())
        return true;
    }
    return false;
  };

  auto exprReferencesNamedSlot =
      [&](const VirtualValueExpr &expr, llvm::StringRef slot_name,
          const auto &self) -> bool {
        if (expr.kind == VirtualExprKind::kStateSlot) {
          if (expr.state_base_name.has_value() &&
              *expr.state_base_name == slot_name) {
            return true;
          }
          if (expr.slot_id.has_value()) {
            if (const auto *slot = model.lookupSlot(*expr.slot_id);
                slot && slot->base_name == slot_name) {
              return true;
            }
          }
        }
        if (expr.kind == VirtualExprKind::kStackCell &&
            expr.state_base_name.has_value() &&
            *expr.state_base_name == slot_name) {
          return true;
        }
        for (const auto &operand : expr.operands) {
          if (self(operand, slot_name, self))
            return true;
        }
        return false;
      };

  auto has_handler_localized_continuation =
      [&](const VirtualHandlerSummary &handler,
          uint64_t continuation_pc) -> bool {
        if (!handler.dispatches.empty())
          return false;

        auto is_return_pc_slot = [&](uint32_t slot_id) {
          if (const auto *slot = model.lookupSlot(slot_id))
            return slot->base_name == "RETURN_PC";
          return false;
        };

        auto is_localized_expr = [&](const VirtualValueExpr &expr) {
          return exprReferencesNamedSlot(expr, "RETURN_PC",
                                         exprReferencesNamedSlot) ||
                 (expr.kind == VirtualExprKind::kConstant &&
                  expr.constant.has_value() &&
                  *expr.constant == continuation_pc);
        };

        for (const auto &fact : handler.outgoing_facts) {
          if (is_return_pc_slot(fact.slot_id))
            continue;
          if (is_localized_expr(fact.value)) {
            vmModelImportDebugLog("root-same-handler-localized handler=" +
                                  handler.function_name + " slot=" +
                                  llvm::Twine(fact.slot_id).str() + " value=" +
                                  renderVirtualValueExpr(fact.value));
            return true;
          }
        }
        return false;
      };

  auto has_same_handler_localized_continuation =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
        if (!callsite.continuation_pc.has_value())
          return false;
        return has_handler_localized_continuation(handler,
                                                  *callsite.continuation_pc);
      };

  auto lookup_stack_cell = [&](unsigned cell_id)
      -> const VirtualStackCellInfo * {
    auto it = llvm::find_if(model.stackCells(),
                            [&](const VirtualStackCellInfo &cell) {
                              return cell.id == cell_id;
                            });
    return it == model.stackCells().end() ? nullptr : &*it;
  };

  auto has_initial_stack_anchored_continuation =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite,
          std::optional<unsigned> &concrete_stack_slot_id) -> bool {
        if (callsite.continuation_stack_cell_id) {
          const auto *cell =
              lookup_stack_cell(*callsite.continuation_stack_cell_id);
          if (!cell)
            return false;

          concrete_stack_slot_id =
              lookupSummarySlotId(handler, cell->base_name, cell->base_offset);
          return cell->cell_offset == 0;
        }

        return false;
      };

  auto has_stack_reentry_to_initial_slot =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
        if (!callsite.continuation_pc.has_value())
          return false;
        if (callsite.exit.disposition !=
            VirtualExitDisposition::kVmExitNativeCallReenter) {
          return false;
        }
        std::optional<unsigned> concrete_stack_slot_id;
        if (!has_initial_stack_anchored_continuation(handler, callsite,
                                                     concrete_stack_slot_id)) {
          return false;
        }

        if (!concrete_stack_slot_id)
          return true;

        const auto *stack_fact =
            lookupSlotFactById(handler.outgoing_facts, *concrete_stack_slot_id);
        if (!stack_fact)
          return true;

        int64_t delta = 0;
        if (!exprMatchesBasePlusOrMinusConst(stack_fact->value,
                                             *concrete_stack_slot_id, delta)) {
          return true;
        }
        return delta == 8 || delta == 16;
      };

  auto is_stack_reentry_frontier =
      [&](const VirtualRootSliceSummary::FrontierEdge &frontier) -> bool {
        if (frontier.kind != VirtualRootFrontierKind::kCall)
          return false;
        if (frontier.callsite_index == 0 &&
            frontier.source_handler_name.empty()) {
          return false;
        }
        auto handler_it = handler_by_name.find(frontier.source_handler_name);
        if (handler_it == handler_by_name.end())
          return false;
        const auto *handler = handler_it->second;
        if (frontier.callsite_index >= handler->callsites.size())
          return false;
        return has_stack_reentry_to_initial_slot(
            *handler, handler->callsites[frontier.callsite_index]);
      };

  auto has_lifted_continuation_handler =
      [&](const VirtualCallSiteSummary &callsite) -> bool {
        if (!callsite.continuation_pc.has_value())
          return false;
        auto it = handler_by_pc.find(*callsite.continuation_pc);
        if (it != handler_by_pc.end())
          return true;
        return lookup_exact_lifted_leaf(callsite.continuation_pc,
                                        std::nullopt) != nullptr;
      };

  auto is_semantically_localized_callsite =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
        if (!callsite.continuation_pc.has_value())
          return false;
        if (has_stack_reentry_to_initial_slot(handler, callsite)) {
          return callsite.unresolved_reason.empty() ||
                 callsite.unresolved_reason == "call_target_unlifted" ||
                 callsite.unresolved_reason == "call_return_unresolved";
        }
        if (callsite.exit.disposition == VirtualExitDisposition::kVmEnter ||
            callsite.exit.disposition ==
                VirtualExitDisposition::kNestedVmEnter) {
          return false;
        }
        if (!has_lifted_direct_callee(handler) &&
            !has_lifted_continuation_handler(callsite) &&
            !has_same_handler_localized_continuation(handler, callsite)) {
          return false;
        }
        return callsite.unresolved_reason ==
                   "call_target_import_pointer" ||
               callsite.unresolved_reason ==
                   "call_target_not_executable_in_image" ||
               callsite.unresolved_reason == "call_target_undecodable" ||
               callsite.unresolved_reason == "call_target_desynchronized" ||
               callsite.unresolved_reason == "call_target_mid_instruction" ||
               (callsite.unresolved_reason == "call_target_unresolved" &&
                !handler.is_candidate && handler.dispatches.empty() &&
                !callsite.resolved_target_pc.has_value());
      };

  auto is_semantically_localized_unlifted_callsite =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
        return !terminal_boundary_recovery_mode &&
               callsite.unresolved_reason == "call_target_unlifted" &&
               callsite.resolved_target_pc.has_value() &&
               callsite.is_executable_in_image && callsite.is_decodable_entry &&
               (callsite.exit.disposition == VirtualExitDisposition::kStayInVm ||
                callsite.exit.disposition == VirtualExitDisposition::kUnknown) &&
               handler.dispatches.empty() &&
               (has_lifted_direct_callee(handler) ||
                has_lifted_continuation_handler(callsite) ||
                has_same_handler_localized_continuation(handler, callsite));
      };

  auto classify_frontier_reason =
      [&](const VirtualHandlerSummary &handler,
          const VirtualDispatchSummary &dispatch) {
        if (!dispatch.unresolved_reason.empty() &&
            dispatch.unresolved_reason != "dynamic_target") {
          return dispatch.unresolved_reason;
        }
        if (handler.stack_memory_budget_exceeded)
          return std::string("stack_fact_budget_exceeded");
        if (handler.has_unsupported_stack_memory)
          return std::string("unsupported_memory_target");
        for (const auto &callee_name : handler.direct_callees) {
          auto it = handler_by_name.find(callee_name);
          if (it == handler_by_name.end())
            continue;
          if (it->second->has_unsupported_stack_memory)
            return std::string("unsupported_memory_target");
          if (it->second->stack_memory_budget_exceeded)
            return std::string("stack_fact_budget_exceeded");
        }
        return std::string("dynamic_target");
      };

  auto is_terminal_frontier =
      [&](const VirtualRootSliceSummary::FrontierEdge &frontier) {
        const bool has_image_context =
            binary_memory.imageBase() != 0 && binary_memory.imageSize() != 0;
        switch (frontier.kind) {
          case VirtualRootFrontierKind::kCall:
            if (is_stack_reentry_frontier(frontier))
              return true;
            if (isOpenExecutableFrontierReason(frontier.kind, frontier.reason))
              return false;
            if (isTerminalExitDisposition(frontier.exit_disposition))
              return true;
            if (frontier.exit_disposition == VirtualExitDisposition::kStayInVm ||
                frontier.exit_disposition == VirtualExitDisposition::kVmEnter ||
                frontier.exit_disposition ==
                    VirtualExitDisposition::kNestedVmEnter) {
              return false;
            }
            return frontier.reason == "call_target_import_pointer" ||
                   frontier.reason == "call_target_not_executable_in_image" ||
                   frontier.reason == "call_target_out_of_image";

          case VirtualRootFrontierKind::kDispatch:
            if (isOpenExecutableFrontierReason(frontier.kind, frontier.reason))
              return false;
            if (frontier.reason == "boundary_target_unlifted") {
              if (!frontier.canonical_target_va.has_value() &&
                  !frontier.target_pc.has_value()) {
                return has_image_context;
              }
              if (!has_image_context)
                return false;
              if (frontier.canonical_target_va.has_value()) {
                return !isTargetMapped(binary_memory,
                                       *frontier.canonical_target_va) ||
                       !isTargetExecutable(binary_memory,
                                           *frontier.canonical_target_va);
              }
              return !isTargetMapped(binary_memory, *frontier.target_pc) ||
                     !isTargetExecutable(binary_memory, *frontier.target_pc);
            }
            if (isTerminalExitDisposition(frontier.exit_disposition))
              return true;
            if (frontier.exit_disposition == VirtualExitDisposition::kStayInVm ||
                frontier.exit_disposition == VirtualExitDisposition::kVmEnter ||
                frontier.exit_disposition ==
                    VirtualExitDisposition::kNestedVmEnter) {
              return false;
            }
            if (frontier.reason == "dispatch_target_not_executable" ||
                frontier.reason == "dispatch_target_undecodable") {
              return true;
            }
            return false;
        }
        return false;
      };

  for (const auto &root_handler : handlers) {
    if (!root_handler.is_output_root || !root_handler.entry_va.has_value())
      continue;
    if (explicit_dirty_scope && !root_handler.is_dirty_seed &&
        !root_handler.is_closed_root_slice_root)
      continue;

    VirtualRootSliceSummary slice;
    slice.root_va = *root_handler.entry_va;
    std::set<std::string> reachable_names;
    std::set<std::string> queued_names;
    std::set<std::string> frontier_keys;
    std::vector<std::pair<const VirtualHandlerSummary *, std::optional<uint64_t>>>
        worklist;
    auto add_frontier =
        [&](VirtualRootSliceSummary::FrontierEdge frontier) {
          std::string key =
              std::to_string(static_cast<unsigned>(frontier.kind)) + "|" +
              frontier.source_handler_name + "|" +
              std::to_string(frontier.dispatch_index) + "|" +
              std::to_string(frontier.callsite_index) + "|" + frontier.reason +
              "|" +
              (frontier.target_pc.has_value()
                   ? ("0x" + llvm::utohexstr(*frontier.target_pc))
                   : std::string("-")) +
              "|" +
              (frontier.canonical_target_va.has_value()
                   ? ("0x" + llvm::utohexstr(*frontier.canonical_target_va))
                   : std::string("-")) +
              "|" + frontier.boundary_name.value_or("-") + "|" +
              (frontier.vip_pc.has_value()
                   ? ("0x" + llvm::utohexstr(*frontier.vip_pc))
                   : std::string("-")) +
              "|" +
              std::to_string(static_cast<unsigned>(frontier.exit_disposition));
          if (!frontier_keys.insert(key).second)
            return;
          slice.frontier_edges.push_back(std::move(frontier));
        };
    enqueue_handler(&root_handler, root_handler.canonical_vip.resolved_pc,
                    worklist, queued_names, reachable_names);

    while (!worklist.empty()) {
      const auto [handler, incoming_vip_pc] = worklist.back();
      worklist.pop_back();
      const auto *current_handler = handler;

      bool traverse_direct_callees =
          handler->entry_va.has_value() || handler->is_output_root ||
          handler->is_candidate || has_lifted_direct_callee(*handler) ||
          !handler->dispatches.empty() || !handler->called_boundaries.empty() ||
          llvm::any_of(handler->callsites, [](const VirtualCallSiteSummary &cs) {
            return cs.continuation_pc.has_value();
          });
      if (traverse_direct_callees) {
        for (const auto &callee_name : handler->direct_callees) {
          auto it = handler_by_name.find(callee_name);
          if (it != handler_by_name.end())
            enqueue_handler(it->second, std::nullopt, worklist, queued_names,
                            reachable_names);
        }
      }

      if (handler->entry_va.has_value()) {
        auto prelude =
            detectEntryPreludeDirectCall(binary_memory, *handler->entry_va);
        if (prelude.has_value()) {
          const VirtualHandlerSummary *target = nullptr;
          auto it = handler_by_pc.find(prelude->target_pc);
          if (it != handler_by_pc.end())
            target = it->second;
          if (target) {
            enqueue_handler(target, prelude->target_pc, worklist, queued_names,
                            reachable_names);
          } else {
            auto reason = std::string("call_target_out_of_image");
            std::optional<uint64_t> recovered_entry_pc;
            const VirtualHandlerSummary *recovered_target = nullptr;
            if (isTargetExecutable(binary_memory, prelude->target_pc)) {
              auto decodable = isTargetDecodableEntry(
                  binary_memory, prelude->target_pc, target_arch);
              recovered_target = findNearbyLiftedHandlerEntry(
                  handler_by_pc, prelude->target_pc, target_arch);
              if (recovered_target && recovered_target->entry_va.has_value()) {
                recovered_entry_pc = recovered_target->entry_va;
                reason = std::string("call_target_mid_instruction");
              } else if (decodable.has_value() && !*decodable) {
                recovered_entry_pc = findNearbyExecutableEntry(
                    binary_memory, prelude->target_pc, target_arch);
                if (recovered_entry_pc) {
                  auto recovered_it = handler_by_pc.find(*recovered_entry_pc);
                  if (recovered_it != handler_by_pc.end()) {
                    recovered_target = recovered_it->second;
                    reason = std::string("call_target_mid_instruction");
                  } else {
                    reason = isLikelyDisassemblyDesyncTarget(
                                 binary_memory, prelude->target_pc,
                                 recovered_entry_pc, target_arch)
                                 ? std::string("call_target_desynchronized")
                                 : std::string("call_target_nearby_unlifted");
                  }
                } else {
                  reason = std::string("call_target_undecodable");
                }
              } else {
                reason = std::string("call_target_unlifted");
              }
            } else if (lookupImportTarget(binary_memory, prelude->target_pc)) {
              reason = std::string("call_target_import_pointer");
            } else if (isTargetMapped(binary_memory, prelude->target_pc)) {
              reason = std::string("call_target_not_executable_in_image");
            }

            auto prelude_target_decodable = isTargetDecodableEntry(
                binary_memory, prelude->target_pc, target_arch);
            bool semantically_localized_unlifted_prelude_target =
                !terminal_boundary_recovery_mode &&
                reason == "call_target_unlifted" &&
                handler->dispatches.empty() &&
                isTargetExecutable(binary_memory, prelude->target_pc) &&
                prelude_target_decodable.has_value() &&
                *prelude_target_decodable &&
                (has_lifted_direct_callee(*handler) ||
                 has_handler_localized_continuation(*handler,
                                                    prelude->continuation_pc));
            if (semantically_localized_unlifted_prelude_target)
              continue;

            bool skip_mid_instruction_wrapper =
                reason == "call_target_mid_instruction" &&
                !handler->is_candidate && !handler->is_output_root &&
                !handler->callsites.empty();
            if (skip_mid_instruction_wrapper)
              continue;

            if (recovered_target && recovered_target->entry_va.has_value())
              enqueue_handler(recovered_target, recovered_entry_pc, worklist,
                              queued_names,
                              reachable_names);
            else if (auto *exact = lookup_exact_lifted_leaf(
                         recovered_entry_pc
                             ? recovered_entry_pc
                             : std::optional<uint64_t>(prelude->target_pc),
                         std::nullopt)) {
              reachable_names.insert(exact->getName().str());
              continue;
            }

            add_frontier(VirtualRootSliceSummary::FrontierEdge{
                VirtualRootFrontierKind::kCall,
                handler->function_name,
                0,
                0,
                std::move(reason),
                prelude->target_pc,
                recovered_entry_pc,
                importBoundaryName(binary_memory, prelude->target_pc),
                incoming_vip_pc,
                VirtualExitDisposition::kVmExitNativeCallReenter});
          }
        }
      }

      for (size_t dispatch_index = 0; dispatch_index < handler->dispatches.size();
           ++dispatch_index) {
        const auto &dispatch = handler->dispatches[dispatch_index];
        if (dispatch.successors.empty()) {
          add_frontier(VirtualRootSliceSummary::FrontierEdge{
                  VirtualRootFrontierKind::kDispatch,
                  handler->function_name, static_cast<unsigned>(dispatch_index),
                  0, classify_frontier_reason(*handler, dispatch),
                  std::nullopt, std::nullopt, std::nullopt,
                  dispatch.vip.resolved_pc, dispatch.exit.disposition});
          continue;
        }

        for (const auto &successor : dispatch.successors) {
          switch (successor.kind) {
            case VirtualSuccessorKind::kLiftedHandler:
            case VirtualSuccessorKind::kLiftedBlock:
            case VirtualSuccessorKind::kTraceBlock: {
              const VirtualHandlerSummary *target = nullptr;
              if (successor.target_function_name.has_value()) {
                auto it = handler_by_name.find(*successor.target_function_name);
                if (it != handler_by_name.end())
                  target = it->second;
              }
              if (!target && successor.target_pc != 0) {
                auto it = handler_by_pc.find(successor.target_pc);
                if (it != handler_by_pc.end())
                  target = it->second;
              }
              if (target) {
                enqueue_handler(target, successor.target_pc, worklist,
                                queued_names, reachable_names);
              } else if (auto *exact = lookup_exact_lifted_leaf(
                             successor.target_pc,
                             successor.target_function_name)) {
                reachable_names.insert(exact->getName().str());
              } else {
                add_frontier(VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0, "missing_lifted_target", successor.target_pc,
                        std::nullopt, std::nullopt, dispatch.vip.resolved_pc,
                        dispatch.exit.disposition});
              }
              break;
            }
            case VirtualSuccessorKind::kProtectedBoundary: {
              const VirtualHandlerSummary *target = nullptr;
              if (successor.canonical_boundary_target_va.has_value()) {
                target = lookup_handler_by_pc_or_name(
                    *successor.canonical_boundary_target_va);
              }
              if (target) {
                enqueue_handler(target, successor.canonical_boundary_target_va,
                                worklist, queued_names, reachable_names);
              } else {
                add_frontier(VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0, "boundary_target_unlifted", successor.target_pc,
                        successor.canonical_boundary_target_va,
                        successor.boundary_name, dispatch.vip.resolved_pc,
                        dispatch.exit.disposition});
              }
              break;
            }
            case VirtualSuccessorKind::kUnknown:
              if (successor.target_pc != 0) {
                if (auto boundary_name = resolveBoundaryNameForTarget(
                        model, binary_memory, successor.target_pc)) {
                  const auto *boundary = model.lookupBoundary(*boundary_name);
                  add_frontier(VirtualRootSliceSummary::FrontierEdge{
                          VirtualRootFrontierKind::kDispatch,
                          handler->function_name,
                          static_cast<unsigned>(dispatch_index),
                          0,
                          "boundary_target_unlifted",
                          successor.target_pc,
                          boundary ? boundary->target_va : std::nullopt,
                          boundary_name, dispatch.vip.resolved_pc,
                          dispatch.exit.disposition});
                  break;
                }
                auto classification = classifyUnknownDispatchFrontier(
                    binary_memory, successor.target_pc, target_arch);
                add_frontier(VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0,
                        std::move(classification.reason),
                        successor.target_pc,
                        classification.canonical_target_va,
                        std::nullopt, dispatch.vip.resolved_pc,
                        dispatch.exit.disposition});
                break;
              }
              add_frontier(VirtualRootSliceSummary::FrontierEdge{
                      VirtualRootFrontierKind::kDispatch,
                      handler->function_name, static_cast<unsigned>(dispatch_index),
                      0,
                      dispatch.unresolved_reason.empty()
                          ? "missing_lifted_target"
                          : dispatch.unresolved_reason,
                      successor.target_pc, std::nullopt, std::nullopt,
                      dispatch.vip.resolved_pc, dispatch.exit.disposition});
              break;
          }
        }
      }

      for (size_t callsite_index = 0; callsite_index < handler->callsites.size();
           ++callsite_index) {
        const auto &callsite = handler->callsites[callsite_index];

        const VirtualHandlerSummary *target = nullptr;
        if (callsite.target_function_name.has_value()) {
          auto it = handler_by_name.find(*callsite.target_function_name);
          if (it != handler_by_name.end())
            target = it->second;
        }
        if (!target && callsite.resolved_target_pc.has_value()) {
          auto it = handler_by_pc.find(*callsite.resolved_target_pc);
          if (it != handler_by_pc.end())
            target = it->second;
        }
        if (!target && callsite.recovered_target_function_name.has_value()) {
          auto it = handler_by_name.find(*callsite.recovered_target_function_name);
          if (it != handler_by_name.end())
            target = it->second;
        }
        if (!target && callsite.recovered_entry_pc.has_value()) {
          auto it = handler_by_pc.find(*callsite.recovered_entry_pc);
          if (it != handler_by_pc.end())
            target = it->second;
        }
        if (target && callsite.continuation_pc.has_value())
          enqueue_handler(target, callsite.continuation_pc, worklist,
                          queued_names, reachable_names);
        else if (auto *exact = lookup_exact_lifted_leaf(
                     callsite.recovered_entry_pc
                         ? callsite.recovered_entry_pc
                         : callsite.resolved_target_pc,
                     callsite.recovered_target_function_name
                         ? callsite.recovered_target_function_name
                         : callsite.target_function_name)) {
          reachable_names.insert(exact->getName().str());
        }

        bool semantically_localized_callsite =
            is_semantically_localized_callsite(*handler, callsite);
        bool semantically_localized_unlifted_target =
            !target &&
            is_semantically_localized_unlifted_callsite(*handler, callsite);
        const bool has_direct_callee = has_lifted_direct_callee(*handler);
        const bool has_cont_handler = has_lifted_continuation_handler(callsite);
        const bool has_same_local =
            has_same_handler_localized_continuation(*handler, callsite);
        vmModelImportDebugLog(
            "root-callsite handler=" + handler->function_name +
            " unresolved=" + callsite.unresolved_reason +
            " cont=" +
            (callsite.continuation_pc
                 ? ("0x" + llvm::utohexstr(*callsite.continuation_pc))
                 : std::string("-")) +
            " target=" +
            (callsite.resolved_target_pc
                 ? ("0x" + llvm::utohexstr(*callsite.resolved_target_pc))
                 : std::string("-")) +
            " recovered=" +
            (callsite.recovered_entry_pc
                 ? ("0x" + llvm::utohexstr(*callsite.recovered_entry_pc))
                 : std::string("-")) +
            " target_found=" + (target ? std::string("true") : std::string("false")) +
            " direct_callee=" +
            (has_direct_callee ? std::string("true") : std::string("false")) +
            " cont_handler=" +
            (has_cont_handler ? std::string("true") : std::string("false")) +
            " same_local=" +
            (has_same_local ? std::string("true") : std::string("false")) +
            " localized=" +
            (semantically_localized_callsite ? std::string("true")
                                             : std::string("false")) +
            " localized_unlifted=" +
            (semantically_localized_unlifted_target ? std::string("true")
                                                    : std::string("false")));
        if (semantically_localized_callsite ||
            semantically_localized_unlifted_target) {
          continue;
        }

        if (!callsite.unresolved_reason.empty() || !target) {
          vmModelImportDebugLog("root-callsite-frontier handler=" +
                                handler->function_name + " reason=" +
                                (callsite.unresolved_reason.empty()
                                     ? std::string("call_target_unlifted")
                                     : callsite.unresolved_reason));
          add_frontier(VirtualRootSliceSummary::FrontierEdge{
              VirtualRootFrontierKind::kCall,
              handler->function_name,
              0,
              static_cast<unsigned>(callsite_index),
              callsite.unresolved_reason.empty() ? "call_target_unlifted"
                                                 : callsite.unresolved_reason,
              callsite.resolved_target_pc,
              callsite.recovered_entry_pc,
              importBoundaryName(binary_memory, callsite.resolved_target_pc),
              callsite.vip.resolved_pc,
              callsite.exit.disposition});
        }
      }

      bool has_semantically_localized_callsite =
          llvm::any_of(current_handler->callsites,
                       [&](const VirtualCallSiteSummary &cs) {
                         return is_semantically_localized_callsite(
                                    *current_handler, cs) ||
                                is_semantically_localized_unlifted_callsite(
                                    *current_handler, cs);
                       });
      if (handler->dispatches.empty() && !has_semantically_localized_callsite) {
        if (auto terminal_next_pc = resolveTerminalNextPcFromFacts(*handler)) {
          const VirtualHandlerSummary *target = nullptr;
          auto it = handler_by_pc.find(*terminal_next_pc);
          if (it != handler_by_pc.end())
            target = it->second;
          if (!target) {
            target = findNearbyLiftedHandlerEntry(handler_by_pc, *terminal_next_pc,
                                                  target_arch);
          }
          if (target) {
            enqueue_handler(target, *terminal_next_pc, worklist, queued_names,
                            reachable_names);
          } else if (auto *exact =
                         lookup_exact_lifted_leaf(terminal_next_pc, std::nullopt)) {
            reachable_names.insert(exact->getName().str());
          } else {
            if (auto boundary_name = resolveBoundaryNameForTarget(
                    model, binary_memory, *terminal_next_pc)) {
              const auto *boundary = model.lookupBoundary(*boundary_name);
              add_frontier(VirtualRootSliceSummary::FrontierEdge{
                      VirtualRootFrontierKind::kDispatch,
                      handler->function_name,
                      static_cast<unsigned>(handler->dispatches.size()),
                      0,
                      "boundary_target_unlifted",
                      *terminal_next_pc,
                      boundary ? boundary->target_va : std::nullopt,
                      boundary_name, handler->canonical_vip.resolved_pc,
                      VirtualExitDisposition::kUnknown});
              continue;
            }
            auto classification = classifyUnknownDispatchFrontier(
                binary_memory, *terminal_next_pc, target_arch);
            add_frontier(VirtualRootSliceSummary::FrontierEdge{
                    VirtualRootFrontierKind::kDispatch,
                    handler->function_name,
                    static_cast<unsigned>(handler->dispatches.size()),
                    0,
                    std::move(classification.reason),
                    *terminal_next_pc,
                    classification.canonical_target_va,
                    std::nullopt, handler->canonical_vip.resolved_pc,
                    VirtualExitDisposition::kUnknown});
          }
        }
      }

      for (const auto &boundary_name : handler->called_boundaries) {
        const auto *boundary = model.lookupBoundary(boundary_name);
        if (!boundary || !boundary->target_va.has_value())
          continue;
        auto *target = lookup_handler_by_pc_or_name(*boundary->target_va);
        if (target) {
          enqueue_handler(target, boundary->target_va, worklist,
                          queued_names, reachable_names);
          continue;
        }
        if (auto *exact =
                lookup_exact_lifted_leaf(boundary->target_va, std::nullopt)) {
          reachable_names.insert(exact->getName().str());
          continue;
        }
        add_frontier(VirtualRootSliceSummary::FrontierEdge{
            VirtualRootFrontierKind::kDispatch,
            handler->function_name,
            static_cast<unsigned>(handler->dispatches.size()),
            0,
            "boundary_target_unlifted",
            std::nullopt,
            boundary->target_va,
            normalizeBoundaryNameForRootSlice(boundary->name),
            handler->canonical_vip.resolved_pc,
            VirtualExitDisposition::kUnknown});
      }
    }

    slice.reachable_handler_names.assign(reachable_names.begin(),
                                         reachable_names.end());
    slice.specialization_count = static_cast<unsigned>(std::count_if(
        slice.reachable_handler_names.begin(), slice.reachable_handler_names.end(),
        [&](const std::string &handler_name) {
          auto it = handler_by_name.find(handler_name);
          if (it == handler_by_name.end())
            return false;
          const auto *handler = it->second;
          if (!handler->is_specialized)
            return false;
          return !handler->specialization_root_va.has_value() ||
                 *handler->specialization_root_va == slice.root_va;
        }));
    slice.is_closed =
        slice.frontier_edges.empty() ||
        llvm::all_of(slice.frontier_edges, is_terminal_frontier);
    root_slices.push_back(std::move(slice));
  }
}

}  // namespace omill::virtual_model::detail

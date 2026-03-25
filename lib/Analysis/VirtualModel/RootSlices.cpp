#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>

#include <algorithm>
#include <cstdlib>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

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
  auto it = handler_by_pc.lower_bound(target_pc);
  while (it != handler_by_pc.begin()) {
    --it;
    if ((target_pc - it->first) > window)
      break;
    return it->second;
  }
  return nullptr;
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
      classification.reason = "dispatch_target_nearby_unlifted";
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

static std::optional<uint64_t> resolveTerminalNextPcFromFacts(
    const VirtualHandlerSummary &summary) {
  auto next_pc_slot_id = lookupSummaryNamedSlotId(summary, "NEXT_PC");
  if (!next_pc_slot_id)
    return std::nullopt;

  const auto *next_pc_fact =
      lookupSlotFactById(summary.outgoing_facts, *next_pc_slot_id);
  if (!next_pc_fact)
    return std::nullopt;

  struct FactStateRef {
    llvm::ArrayRef<VirtualSlotFact> slots;
    llvm::ArrayRef<VirtualStackFact> stack;
  };

  const FactStateRef states[] = {
      {summary.outgoing_facts, summary.outgoing_stack_facts},
      {summary.outgoing_facts, summary.incoming_stack_facts},
      {summary.incoming_facts, summary.outgoing_stack_facts},
      {summary.incoming_facts, summary.incoming_stack_facts},
  };

  std::optional<uint64_t> first_resolved;
  for (const auto &state : states) {
    if (auto resolved =
            evaluateVirtualExpr(next_pc_fact->value, state.slots, state.stack)) {
      if (!first_resolved)
        first_resolved = resolved;
    }
  }

  return first_resolved;
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

  auto enqueue_handler = [&](const VirtualHandlerSummary *handler,
                             std::vector<const VirtualHandlerSummary *> &queue,
                             std::set<std::string> &queued,
                             std::set<std::string> &reachable) {
    if (!handler || !queued.insert(handler->function_name).second)
      return;
    if (is_root_slice_member(*handler))
      reachable.insert(handler->function_name);
    queue.push_back(handler);
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
                                         exprReferencesNamedSlot);
        };

        for (const auto &fact : handler.outgoing_facts) {
          if (is_return_pc_slot(fact.slot_id) &&
              fact.value.kind == VirtualExprKind::kConstant &&
              fact.value.constant.has_value() &&
              *fact.value.constant == continuation_pc) {
            return true;
          }
          if (is_localized_expr(fact.value))
            return true;
        }
        for (const auto &fact : handler.outgoing_stack_facts) {
          if (is_localized_expr(fact.value))
            return true;
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

  auto is_semantically_localized_callsite =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
        if (!callsite.continuation_pc.has_value())
          return false;
        if (!has_lifted_direct_callee(handler) &&
            !has_same_handler_localized_continuation(handler, callsite)) {
          return false;
        }
        return callsite.unresolved_reason ==
                   "call_target_import_pointer" ||
               callsite.unresolved_reason ==
                   "call_target_not_executable_in_image" ||
               callsite.unresolved_reason == "call_target_undecodable" ||
               callsite.unresolved_reason == "call_target_mid_instruction" ||
               (callsite.unresolved_reason == "call_target_unresolved" &&
                !handler.is_candidate && handler.dispatches.empty() &&
                !callsite.resolved_target_pc.has_value());
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
        switch (frontier.kind) {
          case VirtualRootFrontierKind::kCall:
            return frontier.reason == "call_target_import_pointer" ||
                   frontier.reason == "call_target_not_executable_in_image" ||
                   frontier.reason == "call_target_out_of_image" ||
                   frontier.reason == "call_target_undecodable";

          case VirtualRootFrontierKind::kDispatch:
            if (frontier.reason == "dispatch_target_not_executable" ||
                frontier.reason == "dispatch_target_undecodable") {
              return true;
            }
            if (frontier.reason != "boundary_target_unlifted")
              return false;
            if (!frontier.canonical_target_va.has_value() &&
                !frontier.target_pc.has_value()) {
              return true;
            }
            if (frontier.canonical_target_va.has_value()) {
              return !isTargetExecutable(binary_memory,
                                         *frontier.canonical_target_va);
            }
            return !isTargetExecutable(binary_memory, *frontier.target_pc);
        }
        return false;
      };

  for (const auto &root_handler : handlers) {
    if (!root_handler.is_output_root || !root_handler.entry_va.has_value())
      continue;

    VirtualRootSliceSummary slice;
    slice.root_va = *root_handler.entry_va;
    std::set<std::string> reachable_names;
    std::set<std::string> queued_names;
    std::vector<const VirtualHandlerSummary *> worklist;
    enqueue_handler(&root_handler, worklist, queued_names, reachable_names);

    while (!worklist.empty()) {
      const auto *handler = worklist.back();
      worklist.pop_back();

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
            enqueue_handler(it->second, worklist, queued_names, reachable_names);
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
            enqueue_handler(target, worklist, queued_names, reachable_names);
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
                    reason = std::string("call_target_nearby_unlifted");
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
              enqueue_handler(recovered_target, worklist, queued_names,
                              reachable_names);

            slice.frontier_edges.push_back(VirtualRootSliceSummary::FrontierEdge{
                VirtualRootFrontierKind::kCall,
                handler->function_name,
                0,
                0,
                std::move(reason),
                prelude->target_pc,
                recovered_entry_pc,
                importBoundaryName(binary_memory, prelude->target_pc)});
          }
        }
      }

      for (size_t dispatch_index = 0; dispatch_index < handler->dispatches.size();
           ++dispatch_index) {
        const auto &dispatch = handler->dispatches[dispatch_index];
        if (dispatch.successors.empty()) {
          slice.frontier_edges.push_back(
              VirtualRootSliceSummary::FrontierEdge{
                  VirtualRootFrontierKind::kDispatch,
                  handler->function_name, static_cast<unsigned>(dispatch_index),
                  0, classify_frontier_reason(*handler, dispatch),
                  std::nullopt, std::nullopt, std::nullopt});
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
                enqueue_handler(target, worklist, queued_names, reachable_names);
              } else {
                slice.frontier_edges.push_back(
                    VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0, "missing_lifted_target", successor.target_pc,
                        std::nullopt, std::nullopt});
              }
              break;
            }
            case VirtualSuccessorKind::kProtectedBoundary: {
              const VirtualHandlerSummary *target = nullptr;
              if (successor.canonical_boundary_target_va.has_value()) {
                auto it =
                    handler_by_pc.find(*successor.canonical_boundary_target_va);
                if (it != handler_by_pc.end())
                  target = it->second;
              }
              if (target) {
                enqueue_handler(target, worklist, queued_names, reachable_names);
              } else {
                slice.frontier_edges.push_back(
                    VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0, "boundary_target_unlifted", successor.target_pc,
                        successor.canonical_boundary_target_va,
                        successor.boundary_name});
              }
              break;
            }
            case VirtualSuccessorKind::kUnknown:
              if (successor.target_pc != 0) {
                auto classification = classifyUnknownDispatchFrontier(
                    binary_memory, successor.target_pc, target_arch);
                slice.frontier_edges.push_back(
                    VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0,
                        std::move(classification.reason),
                        successor.target_pc,
                        classification.canonical_target_va,
                        std::nullopt});
                break;
              }
              slice.frontier_edges.push_back(
                  VirtualRootSliceSummary::FrontierEdge{
                      VirtualRootFrontierKind::kDispatch,
                      handler->function_name, static_cast<unsigned>(dispatch_index),
                      0,
                      dispatch.unresolved_reason.empty()
                          ? "missing_lifted_target"
                          : dispatch.unresolved_reason,
                      successor.target_pc, std::nullopt, std::nullopt});
              break;
          }
        }
      }

      for (size_t callsite_index = 0; callsite_index < handler->callsites.size();
           ++callsite_index) {
        const auto &callsite = handler->callsites[callsite_index];
        if (!callsite.continuation_pc.has_value())
          continue;

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
        if (target)
          enqueue_handler(target, worklist, queued_names, reachable_names);

        bool semantically_localized_unlifted_target =
            !terminal_boundary_recovery_mode &&
            !target &&
            callsite.unresolved_reason == "call_target_unlifted" &&
            callsite.resolved_target_pc.has_value() &&
            callsite.is_executable_in_image && callsite.is_decodable_entry &&
            handler->dispatches.empty() &&
            (has_lifted_direct_callee(*handler) ||
             has_same_handler_localized_continuation(*handler, callsite));

        if (is_semantically_localized_callsite(*handler, callsite) ||
            semantically_localized_unlifted_target) {
          continue;
        }

        if (!callsite.unresolved_reason.empty() || !target) {
          slice.frontier_edges.push_back(VirtualRootSliceSummary::FrontierEdge{
              VirtualRootFrontierKind::kCall,
              handler->function_name,
              0,
              static_cast<unsigned>(callsite_index),
              callsite.unresolved_reason.empty() ? "call_target_unlifted"
                                                 : callsite.unresolved_reason,
              callsite.resolved_target_pc,
              callsite.recovered_entry_pc,
              importBoundaryName(binary_memory, callsite.resolved_target_pc)});
        }
      }

      if (handler->dispatches.empty()) {
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
            enqueue_handler(target, worklist, queued_names, reachable_names);
          } else {
            auto classification = classifyUnknownDispatchFrontier(
                binary_memory, *terminal_next_pc, target_arch);
            slice.frontier_edges.push_back(
                VirtualRootSliceSummary::FrontierEdge{
                    VirtualRootFrontierKind::kDispatch,
                    handler->function_name,
                    static_cast<unsigned>(handler->dispatches.size()),
                    0,
                    std::move(classification.reason),
                    *terminal_next_pc,
                    classification.canonical_target_va,
                    std::nullopt});
          }
        }
      }

      for (const auto &boundary_name : handler->called_boundaries) {
        const auto *boundary = model.lookupBoundary(boundary_name);
        if (!boundary || !boundary->target_va.has_value())
          continue;
        auto it = handler_by_pc.find(*boundary->target_va);
        if (it != handler_by_pc.end()) {
          enqueue_handler(it->second, worklist, queued_names, reachable_names);
          continue;
        }
        slice.frontier_edges.push_back(VirtualRootSliceSummary::FrontierEdge{
            VirtualRootFrontierKind::kDispatch,
            handler->function_name,
            static_cast<unsigned>(handler->dispatches.size()),
            0,
            "boundary_target_unlifted",
            std::nullopt,
            boundary->target_va,
            normalizeBoundaryNameForRootSlice(boundary->name)});
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

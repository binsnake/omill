#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/ProtectedBoundaryUtils.h"
#include "omill/Support/JumpTableDiscovery.h"

namespace omill::virtual_model::detail {

namespace {

static std::string normalizeBoundaryNameForDispatch(llvm::StringRef name) {
  return name.lower();
}

static std::string syntheticBoundaryNameForDispatch(uint64_t entry_va) {
  return normalizeBoundaryNameForDispatch(
      (llvm::Twine("vm_entry_") + llvm::Twine::utohexstr(entry_va)).str());
}

static const VirtualBoundaryInfo *lookupBoundaryByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va) {
  for (const auto &boundary : model.boundaries()) {
    if (boundary.entry_va.has_value() && *boundary.entry_va == entry_va)
      return &boundary;
  }
  return nullptr;
}

struct BoundaryTargetSummary {
  std::string name;
  std::optional<uint64_t> canonical_target_va;
};

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

static std::optional<VirtualValueExpr> structurallySpecializeDispatchExpr(
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
    if (auto rewritten = structurallySpecializeDispatchExpr(
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

static std::optional<BoundaryTargetSummary> lookupBoundaryTargetSummary(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    uint64_t pc) {
  if (const auto *boundary = lookupBoundaryByEntryVA(model, pc)) {
    return BoundaryTargetSummary{
        normalizeBoundaryNameForDispatch(boundary->name), boundary->target_va};
  }

  auto fallback_name = syntheticBoundaryNameForDispatch(pc);
  if (const auto *boundary = model.lookupBoundary(fallback_name)) {
    return BoundaryTargetSummary{
        normalizeBoundaryNameForDispatch(boundary->name), boundary->target_va};
  }

  if (auto boundary = classifyProtectedBoundary(binary_memory, pc)) {
    BoundaryTargetSummary summary;
    if (const auto *existing =
            lookupBoundaryByEntryVA(model, boundary->entry_va)) {
      summary.name = normalizeBoundaryNameForDispatch(existing->name);
      summary.canonical_target_va = existing->target_va.has_value()
                                        ? existing->target_va
                                        : std::optional<uint64_t>(
                                              boundary->canonical_target_va);
    } else {
      summary.name = syntheticBoundaryNameForDispatch(boundary->entry_va);
      summary.canonical_target_va = boundary->canonical_target_va;
    }
    return summary;
  }

  return std::nullopt;
}

static std::optional<VirtualDispatchSuccessorSummary>
classifyDispatchSuccessor(const VirtualMachineModel &model,
                         const BinaryMemoryMap &binary_memory,
                         uint64_t pc, TargetArch target_arch) {
  if (auto boundary =
          lookupBoundaryTargetSummary(model, binary_memory, pc)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kProtectedBoundary;
    successor.target_pc = pc;
    successor.boundary_name = boundary->name;
    successor.canonical_boundary_target_va = boundary->canonical_target_va;
    return successor;
  }

  for (const auto &handler : model.handlers()) {
    if (!handler.entry_va.has_value() || *handler.entry_va != pc)
      continue;

    VirtualDispatchSuccessorSummary successor;
    llvm::StringRef handler_name(handler.function_name);
    if (handler_name.starts_with("blk_")) {
      successor.kind = VirtualSuccessorKind::kLiftedBlock;
    } else if (handler_name.starts_with("block_")) {
      successor.kind = VirtualSuccessorKind::kTraceBlock;
    } else {
      successor.kind = VirtualSuccessorKind::kLiftedHandler;
    }
    successor.target_pc = pc;
    successor.target_function_name = handler.function_name;
    return successor;
  }

  auto lifted_name = liftedFunctionName(pc);
  if (model.lookupHandler(lifted_name)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kLiftedHandler;
    successor.target_pc = pc;
    successor.target_function_name = lifted_name;
    return successor;
  }

  auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (model.lookupHandler(block_name)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kLiftedBlock;
    successor.target_pc = pc;
    successor.target_function_name = block_name;
    return successor;
  }

  auto trace_block_name =
      (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  if (model.lookupHandler(trace_block_name)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kTraceBlock;
    successor.target_pc = pc;
    successor.target_function_name = trace_block_name;
    return successor;
  }

  if (const auto *nearby = findNearbyLiftedHandlerEntry(model, pc, target_arch)) {
    if (nearby->entry_va.has_value() && *nearby->entry_va != pc) {
      VirtualDispatchSuccessorSummary successor;
      llvm::StringRef handler_name(nearby->function_name);
      if (handler_name.starts_with("blk_")) {
        successor.kind = VirtualSuccessorKind::kLiftedBlock;
      } else if (handler_name.starts_with("block_")) {
        successor.kind = VirtualSuccessorKind::kTraceBlock;
      } else {
        successor.kind = VirtualSuccessorKind::kLiftedHandler;
      }
      successor.target_pc = *nearby->entry_va;
      successor.target_function_name = nearby->function_name;
      return successor;
    }
  }

  return std::nullopt;
}

static std::map<unsigned, VirtualValueExpr> buildPreludeTargetArgumentMap(
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  std::map<unsigned, VirtualValueExpr> result;
  result[0] = argumentExpr(0, 64);
  if (auto it = caller_argument_map.find(0); it != caller_argument_map.end())
    result[0] = it->second;
  if (target_summary.entry_va.has_value())
    result[1] = constantExpr(*target_summary.entry_va, 64);
  if (auto it = caller_argument_map.find(2);
      it != caller_argument_map.end() &&
      isBoundedArgumentFactExpr(it->second)) {
    result[2] = it->second;
  } else {
    result[2] = argumentExpr(2, 64);
  }
  return result;
}

}  // namespace

void summarizeDispatchSuccessors(llvm::Module &M, VirtualMachineModel &model,
                                 const BinaryMemoryMap &binary_memory) {
  auto target_arch = targetArchForModule(M);
  auto slot_ids = buildSlotIdMap(model);
  auto slot_info = buildSlotInfoMap(model);
  auto stack_cell_ids = buildStackCellIdMap(model);
  auto stack_cell_info = buildStackCellInfoMap(model);
  auto boolean_slot_ids = buildBooleanFlagSlotIds(M, model);
  auto boolean_slot_expr_keys = buildBooleanFlagExprKeys(M, model);
  auto &handlers = model.mutableHandlers();
  std::map<std::string, size_t> handler_index;
  std::map<uint64_t, size_t> handler_index_by_entry_va;
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_stack_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_stack_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_argument_maps(
      handlers.size());
  std::vector<std::optional<EntryPreludeCallInfo>> prelude_infos(
      handlers.size());
  std::vector<llvm::SmallVector<size_t, 2>> reverse_prelude_indices(
      handlers.size());
  for (size_t i = 0; i < handlers.size(); ++i) {
    handler_index.emplace(handlers[i].function_name, i);
    if (handlers[i].entry_va.has_value())
      handler_index_by_entry_va.emplace(*handlers[i].entry_va, i);
    outgoing_maps[i] = factMapFor(handlers[i].outgoing_facts);
    outgoing_stack_maps[i] = stackFactMapFor(handlers[i].outgoing_stack_facts);
    incoming_maps[i] = factMapFor(handlers[i].incoming_facts);
    incoming_stack_maps[i] = stackFactMapFor(handlers[i].incoming_stack_facts);
    incoming_argument_maps[i] = argumentFactMapFor(handlers[i].incoming_argument_facts);
  }
  for (size_t i = 0; i < handlers.size(); ++i) {
    if (!handlers[i].entry_va.has_value())
      continue;
    auto prelude =
        detectEntryPreludeDirectCall(binary_memory, *handlers[i].entry_va);
    if (!prelude.has_value())
      continue;
    prelude_infos[i] = prelude;
    auto target_it = handler_index_by_entry_va.find(prelude->target_pc);
    if (target_it != handler_index_by_entry_va.end())
      reverse_prelude_indices[target_it->second].push_back(i);
  }
  for (size_t summary_index = 0; summary_index < handlers.size();
       ++summary_index) {
    auto &summary = handlers[summary_index];
    const auto *region = model.lookupRegionForHandler(summary.function_name);
    auto outgoing_map = factMapFor(summary.outgoing_facts);
    auto incoming_map = factMapFor(summary.incoming_facts);
    auto incoming_arg_map = argumentFactMapFor(summary.incoming_argument_facts);
    auto outgoing_stack_map = stackFactMapFor(summary.outgoing_stack_facts);
    auto incoming_stack_map = stackFactMapFor(summary.incoming_stack_facts);
    std::map<unsigned, VirtualValueExpr> region_outgoing_map;
    std::map<unsigned, VirtualValueExpr> region_incoming_map;
    std::map<unsigned, VirtualValueExpr> region_outgoing_stack_map;
    std::map<unsigned, VirtualValueExpr> region_incoming_stack_map;
    if (region) {
      region_outgoing_map = factMapFor(region->outgoing_facts);
      region_incoming_map = factMapFor(region->incoming_facts);
      region_outgoing_stack_map = stackFactMapFor(region->outgoing_stack_facts);
      region_incoming_stack_map = stackFactMapFor(region->incoming_stack_facts);
    }

    for (auto &dispatch : summary.dispatches) {
      dispatch.successors.clear();
      dispatch.unresolved_reason.clear();
      dispatch.specialized_target = dispatch.target;
      dispatch.specialized_target_source =
          VirtualDispatchResolutionSource::kDirect;

      auto note_target_expr = [&](const VirtualValueExpr &expr,
                                  VirtualDispatchResolutionSource source) {
        unsigned current_refs = countSymbolicRefs(dispatch.specialized_target);
        unsigned new_refs = countSymbolicRefs(expr);
        bool current_is_unknown = isUnknownLikeExpr(dispatch.specialized_target);
        bool new_is_unknown = isUnknownLikeExpr(expr);
        bool current_is_original =
            exprEquals(dispatch.specialized_target, dispatch.target);
        bool new_is_original = exprEquals(expr, dispatch.target);
        if (new_is_unknown && !current_is_unknown)
          return;
        if ((current_is_original && !new_is_original && !new_is_unknown) ||
            new_refs < current_refs ||
            (current_is_unknown && !new_is_unknown) ||
            (new_refs == current_refs && current_is_original &&
             !new_is_original)) {
          dispatch.specialized_target = expr;
          dispatch.specialized_target_source = source;
        }
      };

      struct ResolvedPC {
        uint64_t pc = 0;
        VirtualDispatchResolutionSource source =
            VirtualDispatchResolutionSource::kUnknown;
      };
      llvm::SmallVector<ResolvedPC, 4> resolved_pcs;
      auto append_pc = [&](uint64_t pc, VirtualDispatchResolutionSource source) {
        auto it = llvm::find_if(resolved_pcs, [&](const ResolvedPC &resolved) {
          return resolved.pc == pc;
        });
        if (it == resolved_pcs.end())
          resolved_pcs.push_back(ResolvedPC{pc, source});
      };

      auto collect_from_expr =
          [&](VirtualValueExpr expr,
              const std::vector<VirtualSlotFact> &slot_facts,
              const std::vector<VirtualStackFact> &stack_facts,
              VirtualDispatchResolutionSource source) {
            auto try_collect_expr = [&](VirtualValueExpr candidate) {
              annotateExprSlots(candidate, slot_ids);
              annotateExprStackCells(candidate, stack_cell_ids, slot_ids);
              note_target_expr(candidate, source);
              if (auto pc =
                      evaluateVirtualExpr(candidate, slot_facts, stack_facts,
                                          &binary_memory)) {
                append_pc(*pc, source);
                return true;
              }
              llvm::SmallVector<uint64_t, 4> choices;
              if (collectEvaluatedTargetChoices(candidate, slot_facts,
                                                stack_facts, &boolean_slot_ids,
                                                &boolean_slot_expr_keys,
                                                choices, &binary_memory)) {
                for (uint64_t pc : choices)
                  append_pc(pc, source);
                return true;
              }
              if (collectEvaluatedValueChoices(candidate, slot_facts,
                                               stack_facts, choices,
                                               &binary_memory) &&
                  !choices.empty()) {
                for (uint64_t pc : choices)
                  append_pc(pc, source);
                return true;
              }
              return false;
            };

            if (try_collect_expr(expr))
              return;

            if (auto structural = structurallySpecializeDispatchExpr(
                    expr, slot_facts, stack_facts, slot_info,
                    stack_cell_info)) {
              try_collect_expr(*structural);
            }
          };

      collect_from_expr(dispatch.target, summary.outgoing_facts,
                        summary.outgoing_stack_facts,
                        VirtualDispatchResolutionSource::kDirect);
      if (resolved_pcs.empty()) {
        auto specialized = specializeExpr(dispatch.target, outgoing_map,
                                          &outgoing_stack_map,
                                          &incoming_arg_map);
        collect_from_expr(
            specialized, summary.outgoing_facts, summary.outgoing_stack_facts,
            exprEquals(specialized, dispatch.target)
                ? VirtualDispatchResolutionSource::kOutgoingFacts
                : VirtualDispatchResolutionSource::kHelperArgumentSpecialization);
      }
      if (resolved_pcs.empty() && region) {
        auto specialized = specializeExpr(dispatch.target, region_outgoing_map,
                                          &region_outgoing_stack_map,
                                          &incoming_arg_map);
        collect_from_expr(
            specialized, region->outgoing_facts, region->outgoing_stack_facts,
            exprEquals(specialized, dispatch.target)
                ? VirtualDispatchResolutionSource::kRegionOutgoingFacts
                : VirtualDispatchResolutionSource::kHelperArgumentSpecialization);
      }
      if (resolved_pcs.empty()) {
        collect_from_expr(
            specializeExpr(dispatch.target, incoming_map, &incoming_stack_map,
                           &incoming_arg_map),
            summary.incoming_facts, summary.incoming_stack_facts,
            VirtualDispatchResolutionSource::kIncomingFacts);
      }
      if (resolved_pcs.empty() && region) {
        collect_from_expr(
            specializeExpr(dispatch.target, region_incoming_map,
                           &region_incoming_stack_map, &incoming_arg_map),
            region->incoming_facts, region->incoming_stack_facts,
            VirtualDispatchResolutionSource::kRegionIncomingFacts);
      }
      if (resolved_pcs.empty() && !reverse_prelude_indices[summary_index].empty()) {
        for (size_t predecessor_index : reverse_prelude_indices[summary_index]) {
          if (!prelude_infos[predecessor_index].has_value())
            continue;
          llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
          auto localized = computeEntryPreludeCallOutgoingFacts(
              M, model, summary, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
              incoming_maps[predecessor_index],
              incoming_stack_maps[predecessor_index],
              incoming_argument_maps[predecessor_index],
              prelude_infos[predecessor_index]->continuation_pc, binary_memory,
              /*depth=*/1, visiting);
          if (!localized)
            continue;
          auto localized_args = buildPreludeTargetArgumentMap(
              summary, incoming_argument_maps[predecessor_index]);
          auto specialized = specializeExpr(dispatch.target,
                                            localized->outgoing_slots,
                                            &localized->outgoing_stack,
                                            &localized_args);
          collect_from_expr(
              specialized, slotFactsForMap(localized->outgoing_slots),
              stackFactsForMap(localized->outgoing_stack),
              VirtualDispatchResolutionSource::kPreludeLocalization);
        }
      }
      if (resolved_pcs.empty() && summary.entry_va.has_value()) {
        auto binary_targets = discoverImageBaseRelativeTargetsInRegion(
            binary_memory, binary_memory.imageBase(), *summary.entry_va);
        if (binary_targets.empty()) {
          binary_targets =
              discoverJumpTableTargets(binary_memory, *summary.entry_va);
        }
        for (uint64_t pc : binary_targets)
          append_pc(pc, VirtualDispatchResolutionSource::kDirect);
      }

      for (const auto &resolved_pc : resolved_pcs) {
        if (auto successor =
                classifyDispatchSuccessor(model, binary_memory, resolved_pc.pc,
                                          target_arch)) {
          successor->resolution_source = resolved_pc.source;
          dispatch.successors.push_back(*successor);
          continue;
        }

        VirtualDispatchSuccessorSummary successor;
        successor.kind = VirtualSuccessorKind::kUnknown;
        successor.target_pc = resolved_pc.pc;
        successor.resolution_source = resolved_pc.source;
        dispatch.successors.push_back(std::move(successor));
      }

      if (dispatch.successors.empty()) {
        if (summary.stack_memory_budget_exceeded) {
          dispatch.unresolved_reason = "stack_fact_budget_exceeded";
        } else if (containsStateSlotExpr(dispatch.specialized_target) &&
                   !isBoundedStateProvenanceExpr(dispatch.specialized_target)) {
          dispatch.unresolved_reason = "unsupported_slot_provenance_target";
        } else if (summary.has_unsupported_stack_memory ||
                   ((containsStackCellExpr(dispatch.specialized_target) ||
                     containsMemoryReadExpr(dispatch.specialized_target)) &&
                    !isBoundedStateProvenanceExpr(
                        dispatch.specialized_target))) {
          dispatch.unresolved_reason = "unsupported_memory_target";
        } else {
          dispatch.unresolved_reason = "dynamic_target";
        }
        continue;
      }

      bool has_unknown = std::any_of(
          dispatch.successors.begin(), dispatch.successors.end(),
          [](const VirtualDispatchSuccessorSummary &successor) {
            return successor.kind == VirtualSuccessorKind::kUnknown;
          });
      if (has_unknown)
        dispatch.unresolved_reason = "missing_lifted_target";
    }
  }
}

}  // namespace omill::virtual_model::detail

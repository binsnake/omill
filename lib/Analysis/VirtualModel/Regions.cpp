#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace omill::virtual_model::detail {

namespace {

static std::string normalizeBoundaryNameForRegion(llvm::StringRef name) {
  return name.lower();
}

template <typename SummaryT>
static std::optional<uint64_t> resolveFromIncomingPhiStates(
    const VirtualValueExpr &expr, const SummaryT &summary) {
  for (const auto &state : expandIncomingContextStates(summary)) {
    if (auto resolved =
            evaluateVirtualExpr(expr, state.slot_facts, state.stack_facts)) {
      return resolved;
    }
  }
  return std::nullopt;
}

}  // namespace

void summarizeVirtualRegions(VirtualMachineModel &model,
                             const BinaryMemoryMap &binary_memory) {
  auto &regions = model.mutableRegions();
  regions.clear();

  const auto &handlers = model.handlers();
  if (handlers.empty())
    return;

  auto lookup_stack_cell = [&](unsigned id) -> const VirtualStackCellInfo * {
    auto it = llvm::find_if(model.stackCells(),
                            [&](const VirtualStackCellInfo &cell) {
                              return cell.id == id;
                            });
    return it == model.stackCells().end() ? nullptr : &*it;
  };

  std::map<std::string, size_t> handler_index;
  for (size_t i = 0; i < handlers.size(); ++i)
    handler_index.emplace(handlers[i].function_name, i);

  std::vector<std::vector<size_t>> undirected_edges(handlers.size());
  std::vector<bool> boundary_seed(handlers.size(), false);
  std::vector<std::vector<std::string>> adjacent_boundary_names(handlers.size());
  auto is_region_eligible = [&](const VirtualHandlerSummary &summary) {
    if (summary.is_candidate)
      return true;
    auto name = llvm::StringRef(summary.function_name);
    return name.starts_with("sub_") || name.starts_with("blk_");
  };

  for (size_t i = 0; i < handlers.size(); ++i) {
    const auto &summary = handlers[i];
    auto &boundary_names = adjacent_boundary_names[i];
    for (const auto &boundary_name : summary.called_boundaries)
      boundary_names.push_back(normalizeBoundaryNameForRegion(boundary_name));
    for (const auto &dispatch : summary.dispatches) {
      auto target_pc = evaluateVirtualExpr(dispatch.target, summary.outgoing_facts,
                                           summary.outgoing_stack_facts);
      if (!target_pc) {
        target_pc = resolveFromIncomingPhiStates(dispatch.target, summary);
      }
      if (!target_pc) {
        target_pc = evaluateVirtualExpr(dispatch.target, summary.incoming_facts,
                                        summary.incoming_stack_facts);
      }
      if (!target_pc)
        continue;
      auto boundary_name =
          resolveBoundaryNameForTarget(model, binary_memory, *target_pc);
      if (!boundary_name || llvm::is_contained(boundary_names, *boundary_name))
        continue;
      boundary_names.push_back(*boundary_name);
    }
    boundary_seed[i] = !boundary_names.empty();
    for (const auto &callee_name : summary.direct_callees) {
      auto it = handler_index.find(callee_name);
      if (it == handler_index.end())
        continue;
      undirected_edges[i].push_back(it->second);
      undirected_edges[it->second].push_back(i);
    }
  }

  auto merge_fact_maps = [](std::map<unsigned, VirtualValueExpr> &dst,
                            const std::vector<VirtualSlotFact> &facts) {
    for (const auto &fact : facts) {
      auto it = dst.find(fact.slot_id);
      if (it == dst.end()) {
        dst.emplace(fact.slot_id, fact.value);
        continue;
      }
      auto merged = mergeIncomingExpr(it->second, fact.value);
      if (merged.has_value()) {
        it->second = std::move(*merged);
      } else {
        it->second = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                      : fact.value.bit_width);
      }
    }
  };

  auto merge_stack_fact_maps = [](std::map<unsigned, VirtualValueExpr> &dst,
                                  const std::vector<VirtualStackFact> &facts) {
    for (const auto &fact : facts) {
      auto it = dst.find(fact.cell_id);
      if (it == dst.end()) {
        dst.emplace(fact.cell_id, fact.value);
        continue;
      }
      auto merged = mergeIncomingExpr(it->second, fact.value);
      if (merged.has_value()) {
        it->second = std::move(*merged);
      } else {
        it->second = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                      : fact.value.bit_width);
      }
    }
  };

  auto merge_incoming_slot_phi = [](std::map<unsigned,
                                             std::map<std::string,
                                                      VirtualIncomingContextArm>>
                                        &dst,
                                    const VirtualIncomingSlotPhi &phi) {
    auto &arm_map = dst[phi.slot_id];
    for (const auto &arm : phi.arms) {
      auto existing = arm_map.find(arm.edge_identity);
      if (existing == arm_map.end()) {
        arm_map.emplace(arm.edge_identity, arm);
        continue;
      }
      auto merged = mergeIncomingExpr(existing->second.value, arm.value);
      if (merged.has_value())
        existing->second.value = std::move(*merged);
      else
        existing->second.value =
            unknownExpr(existing->second.value.bit_width
                            ? existing->second.value.bit_width
                            : arm.value.bit_width);
    }
  };

  auto merge_incoming_stack_phi = [](std::map<unsigned,
                                              std::map<std::string,
                                                       VirtualIncomingContextArm>>
                                         &dst,
                                     const VirtualIncomingStackPhi &phi) {
    auto &arm_map = dst[phi.cell_id];
    for (const auto &arm : phi.arms) {
      auto existing = arm_map.find(arm.edge_identity);
      if (existing == arm_map.end()) {
        arm_map.emplace(arm.edge_identity, arm);
        continue;
      }
      auto merged = mergeIncomingExpr(existing->second.value, arm.value);
      if (merged.has_value())
        existing->second.value = std::move(*merged);
      else
        existing->second.value =
            unknownExpr(existing->second.value.bit_width
                            ? existing->second.value.bit_width
                            : arm.value.bit_width);
    }
  };

  std::vector<uint8_t> visited(handlers.size(), 0);
  unsigned next_region_id = 0;
  for (size_t root = 0; root < handlers.size(); ++root) {
    if (visited[root] || !is_region_eligible(handlers[root]))
      continue;

    std::vector<size_t> component;
    std::vector<size_t> queue{root};
    visited[root] = 1;
    while (!queue.empty()) {
      auto index = queue.back();
      queue.pop_back();
      if (!is_region_eligible(handlers[index]))
        continue;
      component.push_back(index);
      for (size_t succ : undirected_edges[index]) {
        if (visited[succ])
          continue;
        visited[succ] = 1;
        queue.push_back(succ);
      }
    }

    if (component.empty())
      continue;

    std::set<std::string> handler_names;
    std::set<std::string> boundary_names;
    std::set<std::string> entry_handlers;
    std::set<std::string> exit_handlers;
    std::vector<VirtualRegionSummary::Edge> internal_edges;
    std::set<unsigned> live_in_ids;
    std::set<unsigned> written_ids;
    std::set<unsigned> live_in_stack_ids;
    std::set<unsigned> written_stack_ids;
    std::map<unsigned, VirtualValueExpr> incoming_map;
    std::map<unsigned, VirtualValueExpr> outgoing_map;
    std::map<unsigned, VirtualValueExpr> incoming_stack_map;
    std::map<unsigned, VirtualValueExpr> outgoing_stack_map;
    std::map<unsigned, std::map<std::string, VirtualIncomingContextArm>>
        incoming_slot_phi_arms;
    std::map<unsigned, std::map<std::string, VirtualIncomingContextArm>>
        incoming_stack_phi_arms;
    std::set<size_t> component_set(component.begin(), component.end());

    for (size_t index : component) {
      const auto &summary = handlers[index];
      handler_names.insert(summary.function_name);
      boundary_names.insert(adjacent_boundary_names[index].begin(),
                            adjacent_boundary_names[index].end());
      live_in_ids.insert(summary.live_in_slot_ids.begin(),
                         summary.live_in_slot_ids.end());
      written_ids.insert(summary.written_slot_ids.begin(),
                         summary.written_slot_ids.end());
      live_in_stack_ids.insert(summary.live_in_stack_cell_ids.begin(),
                               summary.live_in_stack_cell_ids.end());
      written_stack_ids.insert(summary.written_stack_cell_ids.begin(),
                               summary.written_stack_cell_ids.end());
      merge_fact_maps(outgoing_map, summary.outgoing_facts);
      merge_stack_fact_maps(outgoing_stack_map, summary.outgoing_stack_facts);

      bool has_region_predecessor = false;
      bool has_region_successor = false;
      for (const auto &callee_name : summary.direct_callees) {
        auto it = handler_index.find(callee_name);
        if (it == handler_index.end())
          continue;
        if (component_set.count(it->second)) {
          internal_edges.push_back(
              VirtualRegionSummary::Edge{summary.function_name, callee_name});
          has_region_successor = true;
        }
      }
      for (size_t pred = 0; pred < handlers.size(); ++pred) {
        if (!component_set.count(pred))
          continue;
        if (pred == index)
          continue;
        if (llvm::is_contained(handlers[pred].direct_callees,
                               summary.function_name)) {
          has_region_predecessor = true;
          break;
        }
      }

      if (!has_region_successor || !adjacent_boundary_names[index].empty())
        exit_handlers.insert(summary.function_name);
      if (!has_region_predecessor || !adjacent_boundary_names[index].empty()) {
        entry_handlers.insert(summary.function_name);
        merge_fact_maps(incoming_map, summary.incoming_facts);
        for (const auto &phi : summary.incoming_slot_phis)
          merge_incoming_slot_phi(incoming_slot_phi_arms, phi);
        merge_stack_fact_maps(incoming_stack_map, summary.incoming_stack_facts);
        for (const auto &phi : summary.incoming_stack_phis)
          merge_incoming_stack_phi(incoming_stack_phi_arms, phi);
        for (unsigned slot_id : summary.live_in_slot_ids) {
          if (incoming_map.find(slot_id) != incoming_map.end() ||
              incoming_slot_phi_arms.find(slot_id) !=
                  incoming_slot_phi_arms.end()) {
            continue;
          }
          unsigned bit_width = 64;
          if (const auto *slot = model.lookupSlot(slot_id); slot &&
              slot->width != 0) {
            bit_width = slot->width * 8u;
          }
          incoming_map.emplace(slot_id, unknownExpr(bit_width));
        }
        for (unsigned cell_id : summary.live_in_stack_cell_ids) {
          if (incoming_stack_map.find(cell_id) != incoming_stack_map.end() ||
              incoming_stack_phi_arms.find(cell_id) !=
                  incoming_stack_phi_arms.end()) {
            continue;
          }
          unsigned bit_width = 64;
          if (const auto *cell = lookup_stack_cell(cell_id); cell &&
              cell->width != 0) {
            bit_width = cell->width * 8u;
          }
          incoming_stack_map.emplace(cell_id, unknownExpr(bit_width));
        }
      }
    }

    VirtualRegionSummary region;
    region.id = next_region_id++;
    region.boundary_names.assign(boundary_names.begin(), boundary_names.end());
    region.handler_names.assign(handler_names.begin(), handler_names.end());
    region.entry_handler_names.assign(entry_handlers.begin(),
                                      entry_handlers.end());
    region.exit_handler_names.assign(exit_handlers.begin(), exit_handlers.end());
    std::sort(internal_edges.begin(), internal_edges.end(),
              [](const VirtualRegionSummary::Edge &lhs,
                 const VirtualRegionSummary::Edge &rhs) {
                if (lhs.source_handler_name != rhs.source_handler_name)
                  return lhs.source_handler_name < rhs.source_handler_name;
                return lhs.target_handler_name < rhs.target_handler_name;
              });
    internal_edges.erase(
        std::unique(internal_edges.begin(), internal_edges.end(),
                    [](const VirtualRegionSummary::Edge &lhs,
                       const VirtualRegionSummary::Edge &rhs) {
                      return lhs.source_handler_name == rhs.source_handler_name &&
                             lhs.target_handler_name == rhs.target_handler_name;
                    }),
        internal_edges.end());
    region.internal_edges = std::move(internal_edges);
    region.live_in_slot_ids.assign(live_in_ids.begin(), live_in_ids.end());
    region.written_slot_ids.assign(written_ids.begin(), written_ids.end());
    region.live_in_stack_cell_ids.assign(live_in_stack_ids.begin(),
                                         live_in_stack_ids.end());
    region.written_stack_cell_ids.assign(written_stack_ids.begin(),
                                         written_stack_ids.end());
    for (const auto &[slot_id, value] : outgoing_map)
      region.outgoing_facts.push_back(VirtualSlotFact{slot_id, value});
    for (const auto &[cell_id, value] : outgoing_stack_map)
      region.outgoing_stack_facts.push_back(VirtualStackFact{cell_id, value});
    for (const auto &[slot_id, arm_map] : incoming_slot_phi_arms) {
      VirtualIncomingSlotPhi phi;
      phi.slot_id = slot_id;
      for (const auto &[edge_identity, arm] : arm_map)
        phi.arms.push_back(arm);
      phi.merged_value = mergeIncomingContextArmValues(phi.arms);
      incoming_map[slot_id] = phi.merged_value;
      region.incoming_slot_phis.push_back(std::move(phi));
    }
    for (const auto &[cell_id, arm_map] : incoming_stack_phi_arms) {
      VirtualIncomingStackPhi phi;
      phi.cell_id = cell_id;
      for (const auto &[edge_identity, arm] : arm_map)
        phi.arms.push_back(arm);
      phi.merged_value = mergeIncomingContextArmValues(phi.arms);
      incoming_stack_map[cell_id] = phi.merged_value;
      region.incoming_stack_phis.push_back(std::move(phi));
    }
    for (const auto &[slot_id, value] : incoming_map)
      region.incoming_facts.push_back(VirtualSlotFact{slot_id, value});
    for (const auto &[cell_id, value] : incoming_stack_map)
      region.incoming_stack_facts.push_back(VirtualStackFact{cell_id, value});
    regions.push_back(std::move(region));
  }
}

}  // namespace omill::virtual_model::detail

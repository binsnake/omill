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

}  // namespace

void summarizeVirtualRegions(VirtualMachineModel &model,
                             const BinaryMemoryMap &binary_memory) {
  auto &regions = model.mutableRegions();
  regions.clear();

  const auto &handlers = model.handlers();
  if (handlers.empty())
    return;

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
      merge_fact_maps(incoming_map, summary.incoming_facts);
      merge_fact_maps(outgoing_map, summary.outgoing_facts);
      merge_stack_fact_maps(incoming_stack_map, summary.incoming_stack_facts);
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
      if (!has_region_predecessor || !adjacent_boundary_names[index].empty())
        entry_handlers.insert(summary.function_name);
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
    for (const auto &[slot_id, value] : incoming_map)
      region.incoming_facts.push_back(VirtualSlotFact{slot_id, value});
    for (const auto &[slot_id, value] : outgoing_map)
      region.outgoing_facts.push_back(VirtualSlotFact{slot_id, value});
    for (const auto &[cell_id, value] : incoming_stack_map)
      region.incoming_stack_facts.push_back(VirtualStackFact{cell_id, value});
    for (const auto &[cell_id, value] : outgoing_stack_map)
      region.outgoing_stack_facts.push_back(VirtualStackFact{cell_id, value});
    regions.push_back(std::move(region));
  }
}

}  // namespace omill::virtual_model::detail

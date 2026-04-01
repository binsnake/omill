#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>

#include <map>
#include <optional>
#include <set>
#include <vector>

namespace omill::virtual_model::detail {

SlotKey slotKeyForSummary(const VirtualStateSlotSummary &slot) {
  return SlotKey{slot.base_name, slot.offset, slot.width, slot.from_argument,
                 slot.from_alloca};
}

StackCellKey stackCellKeyForSummary(const VirtualStackCellSummary &cell) {
  return StackCellKey{
      SlotKey{cell.base_name, cell.base_offset, cell.base_width,
              cell.base_from_argument, cell.base_from_alloca},
      cell.offset, cell.width};
}

EquivalentStackCellGroupKey equivalentStackCellGroupKeyForSummary(
    const VirtualStackCellSummary &cell) {
  return EquivalentStackCellGroupKey{
      cell.base_from_argument ? std::string() : cell.base_name, cell.base_offset,
      cell.base_width, cell.base_from_argument, cell.base_from_alloca,
      cell.offset, cell.width};
}

EquivalentStackCellGroupKey equivalentStackCellGroupKeyForInfo(
    const VirtualStackCellInfo &cell) {
  return EquivalentStackCellGroupKey{
      cell.base_from_argument ? std::string() : cell.base_name, cell.base_offset,
      cell.base_width, cell.base_from_argument, cell.base_from_alloca,
      cell.cell_offset, cell.width};
}

std::optional<unsigned> findEquivalentArgumentStackCellId(
    int64_t base_offset, unsigned base_width, bool base_from_argument,
    bool base_from_alloca, int64_t cell_offset, unsigned width,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  if (!base_from_argument || base_from_alloca)
    return std::nullopt;

  std::optional<unsigned> mapped_cell_id;
  for (const auto &[cell_key, cell_id] : stack_cell_ids) {
    if (!cell_key.base_slot.from_argument || cell_key.base_slot.from_alloca)
      continue;
    if (cell_key.base_slot.offset != base_offset ||
        cell_key.base_slot.width != base_width ||
        cell_key.cell_offset != cell_offset || cell_key.width != width) {
      continue;
    }
    if (mapped_cell_id && *mapped_cell_id != cell_id)
      return std::nullopt;
    mapped_cell_id = cell_id;
  }
  return mapped_cell_id;
}

std::optional<unsigned> parseArgumentBaseName(llvm::StringRef base_name) {
  if (!base_name.starts_with("arg"))
    return std::nullopt;
  unsigned arg_index = 0;
  if (base_name.drop_front(3).getAsInteger(10, arg_index))
    return std::nullopt;
  return arg_index;
}

std::map<unsigned, VirtualValueExpr> factMapFor(
    llvm::ArrayRef<VirtualSlotFact> facts) {
  std::map<unsigned, VirtualValueExpr> result;
  for (const auto &fact : facts)
    result.emplace(fact.slot_id, fact.value);
  return result;
}

std::map<unsigned, VirtualValueExpr> stackFactMapFor(
    llvm::ArrayRef<VirtualStackFact> facts) {
  std::map<unsigned, VirtualValueExpr> result;
  for (const auto &fact : facts)
    result.emplace(fact.cell_id, fact.value);
  return result;
}

std::map<unsigned, VirtualValueExpr> argumentFactMapFor(
    llvm::ArrayRef<VirtualArgumentFact> facts) {
  std::map<unsigned, VirtualValueExpr> result;
  for (const auto &fact : facts)
    result.emplace(fact.argument_index, fact.value);
  return result;
}

VirtualValueExpr mergeIncomingContextArmValues(
    llvm::ArrayRef<VirtualIncomingContextArm> arms) {
  if (arms.empty())
    return unknownExpr();

  VirtualValueExpr merged = arms.front().value;
  for (size_t i = 1; i < arms.size(); ++i) {
    auto next = mergeIncomingExpr(merged, arms[i].value);
    if (!next.has_value()) {
      merged = unknownExpr(merged.bit_width ? merged.bit_width
                                            : arms[i].value.bit_width);
      return merged;
    }
    merged = std::move(*next);
  }
  return merged;
}

static std::vector<IncomingContextState> expandIncomingContextStatesImpl(
    llvm::ArrayRef<VirtualSlotFact> incoming_facts,
    llvm::ArrayRef<VirtualStackFact> incoming_stack_facts,
    llvm::ArrayRef<VirtualIncomingSlotPhi> incoming_slot_phis,
    llvm::ArrayRef<VirtualIncomingStackPhi> incoming_stack_phis) {
  std::set<std::string> edge_ids;
  std::set<unsigned> phi_slot_ids;
  std::set<unsigned> phi_stack_ids;
  for (const auto &phi : incoming_slot_phis) {
    phi_slot_ids.insert(phi.slot_id);
    for (const auto &arm : phi.arms)
      edge_ids.insert(arm.edge_identity);
  }
  for (const auto &phi : incoming_stack_phis) {
    phi_stack_ids.insert(phi.cell_id);
    for (const auto &arm : phi.arms)
      edge_ids.insert(arm.edge_identity);
  }
  if (edge_ids.empty())
    return {};

  auto slot_map = factMapFor(incoming_facts);
  for (unsigned slot_id : phi_slot_ids)
    slot_map.erase(slot_id);
  auto stack_map = stackFactMapFor(incoming_stack_facts);
  for (unsigned cell_id : phi_stack_ids)
    stack_map.erase(cell_id);

  std::vector<IncomingContextState> states;
  states.reserve(edge_ids.size());
  for (const auto &edge_identity : edge_ids) {
    auto state_slot_map = slot_map;
    auto state_stack_map = stack_map;
    bool has_any_phi_arm = false;

    for (const auto &phi : incoming_slot_phis) {
      auto arm_it = llvm::find_if(phi.arms, [&](const VirtualIncomingContextArm &arm) {
        return arm.edge_identity == edge_identity;
      });
      if (arm_it == phi.arms.end())
        continue;
      state_slot_map[phi.slot_id] = arm_it->value;
      has_any_phi_arm = true;
    }

    for (const auto &phi : incoming_stack_phis) {
      auto arm_it = llvm::find_if(phi.arms, [&](const VirtualIncomingContextArm &arm) {
        return arm.edge_identity == edge_identity;
      });
      if (arm_it == phi.arms.end())
        continue;
      state_stack_map[phi.cell_id] = arm_it->value;
      has_any_phi_arm = true;
    }

    if (!has_any_phi_arm)
      continue;

    IncomingContextState state;
    state.edge_identity = edge_identity;
    state.slot_facts = slotFactsForMap(state_slot_map);
    state.stack_facts = stackFactsForMap(state_stack_map);
    states.push_back(std::move(state));
  }

  return states;
}

std::vector<IncomingContextState> expandIncomingContextStates(
    llvm::ArrayRef<VirtualSlotFact> incoming_facts,
    llvm::ArrayRef<VirtualStackFact> incoming_stack_facts,
    llvm::ArrayRef<VirtualIncomingSlotPhi> incoming_slot_phis,
    llvm::ArrayRef<VirtualIncomingStackPhi> incoming_stack_phis) {
  return expandIncomingContextStatesImpl(incoming_facts, incoming_stack_facts,
                                         incoming_slot_phis,
                                         incoming_stack_phis);
}

std::vector<IncomingContextState> expandIncomingContextStates(
    const VirtualHandlerSummary &summary) {
  return expandIncomingContextStatesImpl(summary.incoming_facts,
                                         summary.incoming_stack_facts,
                                         summary.incoming_slot_phis,
                                         summary.incoming_stack_phis);
}

std::vector<IncomingContextState> expandIncomingContextStates(
    const VirtualRegionSummary &summary) {
  return expandIncomingContextStatesImpl(summary.incoming_facts,
                                         summary.incoming_stack_facts,
                                         summary.incoming_slot_phis,
                                         summary.incoming_stack_phis);
}

std::vector<VirtualSlotFact> slotFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts) {
  std::vector<VirtualSlotFact> result;
  result.reserve(facts.size());
  for (const auto &[slot_id, value] : facts)
    result.push_back(VirtualSlotFact{slot_id, value});
  return result;
}

std::vector<VirtualStackFact> stackFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts) {
  std::vector<VirtualStackFact> result;
  result.reserve(facts.size());
  for (const auto &[cell_id, value] : facts)
    result.push_back(VirtualStackFact{cell_id, value});
  return result;
}

std::map<unsigned, const VirtualStateSlotInfo *> buildSlotInfoMap(
    const VirtualMachineModel &model) {
  std::map<unsigned, const VirtualStateSlotInfo *> slot_info;
  for (const auto &slot : model.slots())
    slot_info.emplace(slot.id, &slot);
  return slot_info;
}

std::optional<unsigned> lookupSlotIdForSummary(
    const VirtualStateSlotSummary &summary,
    const std::map<SlotKey, unsigned> &slot_ids) {
  auto it = slot_ids.find(slotKeyForSummary(summary));
  if (it != slot_ids.end())
    return it->second;

  it = llvm::find_if(slot_ids, [&](const auto &entry) {
    return entry.first.base_name == summary.base_name &&
           entry.first.offset == summary.offset &&
           entry.first.from_argument == summary.from_argument &&
           entry.first.from_alloca == summary.from_alloca;
  });
  if (it == slot_ids.end())
    return std::nullopt;
  return it->second;
}

std::map<unsigned, const VirtualStackCellInfo *> buildStackCellInfoMap(
    const VirtualMachineModel &model) {
  std::map<unsigned, const VirtualStackCellInfo *> cell_info;
  for (const auto &cell : model.stackCells())
    cell_info.emplace(cell.id, &cell);
  return cell_info;
}

std::map<EquivalentStackCellGroupKey, llvm::SmallVector<unsigned, 4>>
buildEquivalentStackCellGroupMap(const VirtualMachineModel &model) {
  std::map<EquivalentStackCellGroupKey, llvm::SmallVector<unsigned, 4>> groups;
  for (const auto &cell : model.stackCells())
    groups[equivalentStackCellGroupKeyForInfo(cell)].push_back(cell.id);
  return groups;
}

std::optional<unsigned> lookupStackCellIdForSummary(
    const VirtualStackCellSummary &summary,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  auto it = stack_cell_ids.find(stackCellKeyForSummary(summary));
  if (it != stack_cell_ids.end())
    return it->second;

  it = llvm::find_if(stack_cell_ids, [&](const auto &entry) {
    return entry.first.base_slot.base_name == summary.base_name &&
           entry.first.base_slot.offset == summary.base_offset &&
           entry.first.base_slot.from_argument == summary.base_from_argument &&
           entry.first.base_slot.from_alloca == summary.base_from_alloca &&
           entry.first.cell_offset == summary.offset;
  });
  if (it != stack_cell_ids.end())
    return it->second;

  return findEquivalentArgumentStackCellId(
      summary.base_offset, summary.base_width, summary.base_from_argument,
      summary.base_from_alloca, summary.offset, summary.width, stack_cell_ids);
}

std::optional<VirtualStateSlotSummary> extractStateSlotSummaryFromExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info) {
  if (expr.kind != VirtualExprKind::kStateSlot)
    if (expr.kind != VirtualExprKind::kArgument || !expr.argument_index.has_value())
      return std::nullopt;

  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value()) {
    auto it = slot_info.find(*expr.slot_id);
    if (it != slot_info.end()) {
      VirtualStateSlotSummary summary;
      summary.base_name = it->second->base_name;
      summary.offset = it->second->offset;
      summary.width = it->second->width;
      summary.from_argument = it->second->from_argument;
      summary.from_alloca = it->second->from_alloca;
      return summary;
    }
  }

  VirtualStateSlotSummary summary;
  summary.width = expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u;
  if (expr.kind == VirtualExprKind::kArgument) {
    summary.base_name = "arg" + std::to_string(*expr.argument_index);
    summary.offset = 0;
    summary.from_argument = true;
    summary.from_alloca = false;
  } else {
    if (!expr.state_base_name || !expr.state_offset)
      return std::nullopt;
    summary.base_name = *expr.state_base_name;
    summary.offset = *expr.state_offset;
    summary.from_argument = parseArgumentBaseName(summary.base_name).has_value();
    summary.from_alloca = !summary.from_argument;
  }
  return summary;
}

}  // namespace omill::virtual_model::detail

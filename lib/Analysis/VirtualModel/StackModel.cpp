#include "Analysis/VirtualModel/Internal.h"

#include <algorithm>

namespace omill::virtual_model::detail {

StackModelBuilder::StackModelBuilder(VirtualMachineModel &model) : model_(model) {
  for (const auto &slot : model_.slots()) {
    slot_ids_.emplace(SlotKey{slot.base_name, slot.offset, slot.width,
                              slot.from_argument, slot.from_alloca},
                      slot.id);
    next_slot_id_ = std::max(next_slot_id_, slot.id + 1);
  }
  for (const auto &cell : model_.stackCells()) {
    stack_cell_ids_.emplace(
        StackCellKey{SlotKey{cell.base_name, cell.base_offset, cell.base_width,
                             cell.base_from_argument, cell.base_from_alloca},
                     cell.cell_offset, cell.width},
        cell.id);
    next_stack_cell_id_ = std::max(next_stack_cell_id_, cell.id + 1);
  }
}

void StackModelBuilder::internSlot(VirtualStateSlotSummary &slot,
                                   llvm::StringRef handler_name) {
  auto key = slotKeyForSummary(slot);
  auto it = slot_ids_.find(key);
  if (it == slot_ids_.end()) {
    unsigned id = next_slot_id_++;
    slot_ids_.emplace(key, id);
    model_.mutableSlots().push_back(VirtualStateSlotInfo{
        id, slot.base_name, slot.offset, slot.width, slot.from_argument,
        slot.from_alloca, {}});
    it = slot_ids_.find(key);
  }
  slot.canonical_id = it->second;
  auto &info = model_.mutableSlots()[it->second];
  if (std::find(info.handler_names.begin(), info.handler_names.end(),
                handler_name.str()) == info.handler_names.end()) {
    info.handler_names.push_back(handler_name.str());
  }
}

void StackModelBuilder::internStackCell(VirtualStackCellSummary &cell,
                                        llvm::StringRef handler_name) {
  VirtualStateSlotSummary base_slot;
  base_slot.base_name = cell.base_name;
  base_slot.offset = cell.base_offset;
  base_slot.width = cell.base_width;
  base_slot.from_argument = cell.base_from_argument;
  base_slot.from_alloca = cell.base_from_alloca;
  internSlot(base_slot, handler_name);
  cell.canonical_base_slot_id = base_slot.canonical_id;

  auto intern_cell_info = [&](VirtualStackCellSummary &summary) {
    auto key = stackCellKeyForSummary(summary);
    auto it = stack_cell_ids_.find(key);
    if (it == stack_cell_ids_.end()) {
      unsigned id = next_stack_cell_id_++;
      stack_cell_ids_.emplace(key, id);
      model_.mutableStackCells().push_back(VirtualStackCellInfo{
          id,
          *summary.canonical_base_slot_id,
          summary.owner_slot_id.value_or(*summary.canonical_base_slot_id),
          summary.owner_kind,
          summary.derived_from_owner_slot_id,
          summary.owner_constant_delta,
          summary.base_name,
          summary.base_offset,
          summary.base_width,
          summary.offset,
          summary.width,
          summary.base_from_argument,
          summary.base_from_alloca,
          {},
      });
      it = stack_cell_ids_.find(key);
    }
    auto &info = model_.mutableStackCells()[it->second];
    if (std::find(info.handler_names.begin(), info.handler_names.end(),
                  handler_name.str()) == info.handler_names.end()) {
      info.handler_names.push_back(handler_name.str());
    }
    return it;
  };

  if (cell.offset != 0) {
    VirtualStackCellSummary zero_cell = cell;
    zero_cell.offset = 0;
    zero_cell.canonical_id.reset();
    zero_cell.canonical_base_slot_id = cell.canonical_base_slot_id;
    (void) intern_cell_info(zero_cell);
  }

  auto it = intern_cell_info(cell);
  cell.canonical_id = it->second;
}

void StackModelBuilder::internExprReferencedSlots(const VirtualValueExpr &expr,
                                                  llvm::StringRef handler_name) {
  std::vector<VirtualStateSlotSummary> referenced_slots;
  collectExprReferencedStateSlots(expr, referenced_slots);
  for (auto &slot : referenced_slots)
    internSlot(slot, handler_name);
}

StackModelContext buildStackModelContext(const VirtualMachineModel &model) {
  StackModelContext context;
  for (const auto &slot : model.slots()) {
    context.slot_ids.emplace(
        SlotKey{slot.base_name, slot.offset, slot.width, slot.from_argument,
                slot.from_alloca},
        slot.id);
    context.slot_info.emplace(slot.id, &slot);
  }
  for (const auto &cell : model.stackCells()) {
    context.stack_cell_ids.emplace(
        StackCellKey{SlotKey{cell.base_name, cell.base_offset, cell.base_width,
                             cell.base_from_argument, cell.base_from_alloca},
                     cell.cell_offset, cell.width},
        cell.id);
    context.stack_cell_info.emplace(cell.id, &cell);
    context.equivalent_stack_cell_groups[equivalentStackCellGroupKeyForInfo(
        cell)].push_back(cell.id);
    context.materialized_stack_cell_ids.emplace(
        MaterializedStackCellKey{cell.base_slot_id, cell.cell_offset, cell.width},
        cell.id);
  }
  return context;
}

std::optional<unsigned> lookupStackCellIdForSummary(
    const VirtualStackCellSummary &summary, const StackModelContext &context) {
  return lookupStackCellIdForSummary(summary, context.stack_cell_ids);
}

std::optional<unsigned> resolveBaseSlotIdForSummary(
    const VirtualStackCellSummary &summary, const StackModelContext &context) {
  if (summary.canonical_base_slot_id.has_value())
    return summary.canonical_base_slot_id;

  VirtualStateSlotSummary base_slot;
  base_slot.base_name = summary.base_name;
  base_slot.offset = summary.base_offset;
  base_slot.width = summary.base_width;
  base_slot.from_argument = summary.base_from_argument;
  base_slot.from_alloca = summary.base_from_alloca;
  return lookupSlotIdForSummary(base_slot, context.slot_ids);
}

}  // namespace omill::virtual_model::detail

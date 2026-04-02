#include "Analysis/VirtualModel/Internal.h"

namespace omill::virtual_model::detail {

namespace {

static void decanonicalizeVirtualValueExpr(VirtualValueExpr &expr) {
  expr.slot_id.reset();
  expr.stack_cell_id.reset();
  for (auto &operand : expr.operands)
    decanonicalizeVirtualValueExpr(operand);
}

static VirtualStateSlotSummary stableSlotSummaryForInfo(
    const VirtualStateSlotInfo &slot) {
  VirtualStateSlotSummary summary;
  summary.base_name = slot.base_name;
  summary.offset = slot.offset;
  summary.width = slot.width;
  summary.from_argument = slot.from_argument;
  summary.from_alloca = slot.from_alloca;
  return summary;
}

static VirtualStackCellSummary stableStackCellSummaryForInfo(
    const VirtualStackCellInfo &cell) {
  VirtualStackCellSummary summary;
  summary.owner_slot_id = cell.owner_slot_id;
  summary.owner_kind = cell.owner_kind;
  summary.derived_from_owner_slot_id = cell.derived_from_owner_slot_id;
  summary.owner_constant_delta = cell.owner_constant_delta;
  summary.base_name = cell.base_name;
  summary.base_offset = cell.base_offset;
  summary.base_width = cell.base_width;
  summary.offset = cell.cell_offset;
  summary.width = cell.width;
  summary.base_from_argument = cell.base_from_argument;
  summary.base_from_alloca = cell.base_from_alloca;
  return summary;
}

}  // namespace

std::vector<CachedStableArgumentFactEntry> captureStableArgumentFacts(
    const std::map<unsigned, VirtualValueExpr> &facts) {
  std::vector<CachedStableArgumentFactEntry> captured;
  for (const auto &[argument_index, value] : facts) {
    auto stable_value = value;
    decanonicalizeVirtualValueExpr(stable_value);
    captured.push_back(
        CachedStableArgumentFactEntry{argument_index, std::move(stable_value)});
  }
  return captured;
}

std::vector<CachedStableSlotFactEntry> captureStableSlotFacts(
    const std::map<unsigned, VirtualValueExpr> &facts,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info) {
  std::vector<CachedStableSlotFactEntry> captured;
  for (const auto &[slot_id, value] : facts) {
    auto info_it = slot_info.find(slot_id);
    if (info_it == slot_info.end())
      continue;
    auto stable_value = value;
    decanonicalizeVirtualValueExpr(stable_value);
    captured.push_back(CachedStableSlotFactEntry{
        stableSlotSummaryForInfo(*info_it->second), std::move(stable_value)});
  }
  return captured;
}

std::vector<CachedStableStackFactEntry> captureStableStackFacts(
    const std::map<unsigned, VirtualValueExpr> &facts,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info) {
  std::vector<CachedStableStackFactEntry> captured;
  for (const auto &[cell_id, value] : facts) {
    auto info_it = stack_cell_info.find(cell_id);
    if (info_it == stack_cell_info.end())
      continue;
    auto stable_value = value;
    decanonicalizeVirtualValueExpr(stable_value);
    captured.push_back(CachedStableStackFactEntry{
        stableStackCellSummaryForInfo(*info_it->second), std::move(stable_value)});
  }
  return captured;
}

std::map<unsigned, VirtualValueExpr> restoreStableArgumentFactMap(
    const std::vector<CachedStableArgumentFactEntry> &facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  std::map<unsigned, VirtualValueExpr> restored;
  for (const auto &fact : facts) {
    auto value = fact.value;
    decanonicalizeVirtualValueExpr(value);
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
    canonicalizeMemoryReadsToStackCells(value, stack_cell_ids, slot_ids);
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
    restored[fact.argument_index] = std::move(value);
  }
  return restored;
}

std::map<unsigned, VirtualValueExpr> restoreStableSlotFactMap(
    const std::vector<CachedStableSlotFactEntry> &facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  std::map<unsigned, VirtualValueExpr> restored;
  for (const auto &fact : facts) {
    auto slot_id = lookupSlotIdForSummary(fact.slot, slot_ids);
    if (!slot_id)
      continue;
    auto value = fact.value;
    decanonicalizeVirtualValueExpr(value);
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
    canonicalizeMemoryReadsToStackCells(value, stack_cell_ids, slot_ids);
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
    restored[*slot_id] = std::move(value);
  }
  return restored;
}

std::map<unsigned, VirtualValueExpr> restoreStableStackFactMap(
    const std::vector<CachedStableStackFactEntry> &facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  std::map<unsigned, VirtualValueExpr> restored;
  for (const auto &fact : facts) {
    auto cell_id = lookupStackCellIdForSummary(fact.cell, stack_cell_ids);
    if (!cell_id)
      continue;
    auto value = fact.value;
    decanonicalizeVirtualValueExpr(value);
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
    canonicalizeMemoryReadsToStackCells(value, stack_cell_ids, slot_ids);
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
    restored[*cell_id] = std::move(value);
  }
  return restored;
}

}  // namespace omill::virtual_model::detail

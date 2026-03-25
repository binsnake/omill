#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>

#include <map>
#include <optional>
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

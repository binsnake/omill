#include "Analysis/VirtualModel/Internal.h"

namespace omill::virtual_model::detail {

namespace {

static std::optional<int64_t> stackBaseDeltaForExpr(const VirtualValueExpr &expr,
                                                    unsigned slot_id) {
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id == slot_id)
    return 0;

  if ((expr.kind == VirtualExprKind::kAdd || expr.kind == VirtualExprKind::kSub) &&
      expr.operands.size() == 2) {
    if (auto nested = stackBaseDeltaForExpr(expr.operands[0], slot_id);
        nested && expr.operands[1].constant.has_value()) {
      int64_t delta = static_cast<int64_t>(*expr.operands[1].constant);
      if (expr.kind == VirtualExprKind::kSub)
        delta = -delta;
      return *nested + delta;
    }
    if (expr.kind == VirtualExprKind::kAdd &&
        expr.operands[0].constant.has_value()) {
      if (auto nested = stackBaseDeltaForExpr(expr.operands[1], slot_id))
        return *nested + static_cast<int64_t>(*expr.operands[0].constant);
    }
  }

  return std::nullopt;
}

static std::optional<int64_t> findStackBaseDeltaForSlot(
    const std::map<unsigned, VirtualValueExpr> &slot_facts, unsigned slot_id) {
  std::optional<int64_t> found_delta;

  auto consider_delta = [&](const VirtualValueExpr &value) {
    auto delta = stackBaseDeltaForExpr(value, slot_id);
    if (!delta)
      return true;
    if (!found_delta) {
      found_delta = *delta;
      return true;
    }
    return *found_delta == *delta;
  };

  if (auto it = slot_facts.find(slot_id); it != slot_facts.end()) {
    if (!consider_delta(it->second))
      return std::nullopt;
  }

  for (const auto &[fact_slot_id, value] : slot_facts) {
    if (fact_slot_id == slot_id)
      continue;
    if (!consider_delta(value))
      return std::nullopt;
  }

  return found_delta;
}

}  // namespace

bool containsArgumentExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kArgument)
    return true;
  return llvm::any_of(expr.operands, containsArgumentExpr);
}

bool isBoundedLocalizedTransferExpr(const VirtualValueExpr &expr,
                                    unsigned depth) {
  if (depth > 6)
    return false;

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
    case VirtualExprKind::kStateSlot:
    case VirtualExprKind::kStackCell:
    case VirtualExprKind::kArgument:
      return true;
    case VirtualExprKind::kMemoryRead:
    case VirtualExprKind::kZExt:
    case VirtualExprKind::kSExt:
    case VirtualExprKind::kTrunc:
      return expr.operands.size() == 1 &&
             isBoundedLocalizedTransferExpr(expr.operands.front(), depth + 1);
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
    case VirtualExprKind::kXor:
    case VirtualExprKind::kAnd:
    case VirtualExprKind::kOr:
    case VirtualExprKind::kShl:
    case VirtualExprKind::kLShr:
    case VirtualExprKind::kAShr:
    case VirtualExprKind::kEq:
    case VirtualExprKind::kNe:
    case VirtualExprKind::kUlt:
    case VirtualExprKind::kUle:
    case VirtualExprKind::kUgt:
    case VirtualExprKind::kUge:
    case VirtualExprKind::kSlt:
    case VirtualExprKind::kSle:
    case VirtualExprKind::kSgt:
    case VirtualExprKind::kSge:
      if (expr.operands.size() != 2)
        return false;
      return countSymbolicRefs(expr) <= 4 &&
             isBoundedLocalizedTransferExpr(expr.operands[0], depth + 1) &&
             isBoundedLocalizedTransferExpr(expr.operands[1], depth + 1);
    case VirtualExprKind::kSelect:
      if (expr.operands.size() != 3)
        return false;
      return countSymbolicRefs(expr) <= 4 &&
             isBoundedLocalizedTransferExpr(expr.operands[0], depth + 1) &&
             isBoundedLocalizedTransferExpr(expr.operands[1], depth + 1) &&
             isBoundedLocalizedTransferExpr(expr.operands[2], depth + 1);
    case VirtualExprKind::kPhi:
      return !expr.operands.empty() && expr.operands.size() <= 4 &&
             countSymbolicRefs(expr) <= 4 &&
             std::all_of(expr.operands.begin(), expr.operands.end(),
                         [&](const VirtualValueExpr &operand) {
                           return isBoundedLocalizedTransferExpr(
                               operand, depth + 1);
                         });
    default:
      return false;
  }
}

std::map<unsigned, VirtualValueExpr> rebaseOutgoingStackFacts(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    const std::map<unsigned, VirtualValueExpr> &outgoing_stack) {
  std::map<unsigned, int64_t> base_deltas;
  for (const auto &slot : model.slots()) {
    if (auto delta = findStackBaseDeltaForSlot(outgoing_slots, slot.id))
      base_deltas.emplace(slot.id, *delta);
  }
  if (base_deltas.empty())
    return outgoing_stack;

  std::map<std::pair<unsigned, int64_t>, unsigned> cell_by_base_and_offset;
  std::map<unsigned, const VirtualStackCellInfo *> cell_info;
  for (const auto &cell : model.stackCells()) {
    cell_by_base_and_offset.emplace(
        std::make_pair(cell.base_slot_id, cell.cell_offset), cell.id);
    cell_info.emplace(cell.id, &cell);
  }

  std::map<unsigned, VirtualValueExpr> rebased;
  for (const auto &[cell_id, value] : outgoing_stack) {
    unsigned mapped_cell_id = cell_id;
    auto info_it = cell_info.find(cell_id);
    if (info_it != cell_info.end()) {
      const auto *info = info_it->second;
      auto delta_it = base_deltas.find(info->base_slot_id);
      if (delta_it != base_deltas.end()) {
        auto target_it = cell_by_base_and_offset.find(
            std::make_pair(info->base_slot_id,
                           info->cell_offset - delta_it->second));
        if (target_it != cell_by_base_and_offset.end())
          mapped_cell_id = target_it->second;
      }
    }

    auto existing = rebased.find(mapped_cell_id);
    if (existing == rebased.end()) {
      rebased.emplace(mapped_cell_id, value);
      continue;
    }
    auto merged = mergeIncomingExpr(existing->second, value);
    if (merged.has_value()) {
      existing->second = std::move(*merged);
    } else {
      existing->second = unknownExpr(existing->second.bit_width
                                         ? existing->second.bit_width
                                         : value.bit_width);
    }
  }

  return rebased;
}

bool mergeFactIntoMap(std::map<unsigned, VirtualValueExpr> &dst, unsigned id,
                      const VirtualValueExpr &value) {
  auto existing = dst.find(id);
  if (existing == dst.end()) {
    dst.emplace(id, value);
    return true;
  }
  if (exprEquals(existing->second, value))
    return false;

  auto merged = mergeIncomingExpr(existing->second, value);
  if (merged.has_value()) {
    if (!exprEquals(existing->second, *merged)) {
      existing->second = std::move(*merged);
      return true;
    }
    return false;
  }

  auto unknown = unknownExpr(existing->second.bit_width
                                 ? existing->second.bit_width
                                 : value.bit_width);
  if (!exprEquals(existing->second, unknown)) {
    existing->second = std::move(unknown);
    return true;
  }
  return false;
}

llvm::SmallDenseSet<unsigned, 16> rebaseWrittenStackCellIds(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    llvm::ArrayRef<unsigned> written_stack_cell_ids) {
  std::map<unsigned, int64_t> base_deltas;
  for (const auto &slot : model.slots()) {
    if (auto delta = findStackBaseDeltaForSlot(outgoing_slots, slot.id))
      base_deltas.emplace(slot.id, *delta);
  }
  if (base_deltas.empty()) {
    return llvm::SmallDenseSet<unsigned, 16>(written_stack_cell_ids.begin(),
                                             written_stack_cell_ids.end());
  }

  std::map<std::pair<unsigned, int64_t>, unsigned> cell_by_base_and_offset;
  std::map<unsigned, const VirtualStackCellInfo *> cell_info;
  for (const auto &cell : model.stackCells()) {
    cell_by_base_and_offset.emplace(
        std::make_pair(cell.base_slot_id, cell.cell_offset), cell.id);
    cell_info.emplace(cell.id, &cell);
  }

  llvm::SmallDenseSet<unsigned, 16> rebased_ids;
  for (unsigned cell_id : written_stack_cell_ids) {
    unsigned mapped_cell_id = cell_id;
    auto info_it = cell_info.find(cell_id);
    if (info_it != cell_info.end()) {
      const auto *info = info_it->second;
      auto delta_it = base_deltas.find(info->base_slot_id);
      if (delta_it != base_deltas.end()) {
        auto target_it = cell_by_base_and_offset.find(
            std::make_pair(info->base_slot_id,
                           info->cell_offset - delta_it->second));
        if (target_it != cell_by_base_and_offset.end())
          mapped_cell_id = target_it->second;
      }
    }
    rebased_ids.insert(mapped_cell_id);
  }

  return rebased_ids;
}

unsigned rebaseSingleStackCellId(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    unsigned cell_id) {
  auto rebased = rebaseWrittenStackCellIds(model, outgoing_slots, {cell_id});
  return rebased.empty() ? cell_id : *rebased.begin();
}

}  // namespace omill::virtual_model::detail

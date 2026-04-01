#include "Analysis/VirtualModel/Internal.h"

namespace omill::virtual_model::detail {

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
  auto stack_model = buildStackModelContext(model);
  auto tracked =
      buildTrackedFactState(stack_model, outgoing_slots, outgoing_stack);
  return tracked.materialized_stack_facts;
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
  auto stack_model = buildStackModelContext(model);
  auto tracked = buildTrackedFactState(stack_model, outgoing_slots, {});
  std::set<CanonicalStackFactKey> written_keys;
  for (unsigned cell_id : written_stack_cell_ids) {
    if (auto key =
            canonicalStackFactKeyForCellId(stack_model, tracked, cell_id))
      written_keys.insert(*key);
  }
  return materializeTrackedWrittenStackCellIds(stack_model, tracked,
                                               written_keys);
}

unsigned rebaseSingleStackCellId(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    unsigned cell_id) {
  auto rebased = rebaseWrittenStackCellIds(model, outgoing_slots, {cell_id});
  return rebased.empty() ? cell_id : *rebased.begin();
}

}  // namespace omill::virtual_model::detail

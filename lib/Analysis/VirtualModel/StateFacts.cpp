#include "Analysis/VirtualModel/Internal.h"

#include <algorithm>

namespace omill::virtual_model::detail {

static bool exprReferencesSlotId(const VirtualValueExpr &expr,
                                 unsigned slot_id) {
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value() &&
      *expr.slot_id == slot_id) {
    return true;
  }
  return llvm::any_of(expr.operands, [&](const VirtualValueExpr &operand) {
    return exprReferencesSlotId(operand, slot_id);
  });
}

VirtualValueExpr castExprToBitWidth(const VirtualValueExpr &expr,
                                    unsigned target_bits) {
  VirtualValueExpr casted = expr;
  unsigned source_bits = expr.bit_width ? expr.bit_width : target_bits;
  if (source_bits == target_bits) {
    casted.bit_width = target_bits;
    return casted;
  }
  auto opcode = source_bits > target_bits ? llvm::Instruction::Trunc
                                          : llvm::Instruction::ZExt;
  return castExpr(expr, opcode, target_bits);
}

static VirtualValueExpr binaryExpr(VirtualExprKind kind, VirtualValueExpr lhs,
                                   VirtualValueExpr rhs, unsigned bit_width) {
  VirtualValueExpr result;
  result.kind = kind;
  result.bit_width = bit_width;
  result.complete = lhs.complete && rhs.complete;
  result.operands.push_back(std::move(lhs));
  result.operands.push_back(std::move(rhs));
  return result;
}

static bool isContiguousLowBitMask(uint64_t mask) {
  return mask && ((mask & (mask + 1)) == 0);
}

static unsigned contiguousLowBitMaskWidth(uint64_t mask) {
  unsigned width = 0;
  while ((mask & 1u) != 0u) {
    ++width;
    mask >>= 1u;
  }
  return width;
}

static bool matchAndConstantMask(const VirtualValueExpr &expr,
                                 const VirtualValueExpr *&base,
                                 uint64_t &mask) {
  if (expr.kind != VirtualExprKind::kAnd || expr.operands.size() != 2)
    return false;

  if (expr.operands[0].constant.has_value()) {
    base = &expr.operands[1];
    mask = *expr.operands[0].constant;
    return true;
  }
  if (expr.operands[1].constant.has_value()) {
    base = &expr.operands[0];
    mask = *expr.operands[1].constant;
    return true;
  }
  return false;
}

static bool isLowBitsProjectionOfExpr(const VirtualValueExpr &expr,
                                      const VirtualValueExpr &base,
                                      unsigned low_bits) {
  if (exprEquals(expr, base))
    return true;

  if (expr.constant.has_value() && base.constant.has_value()) {
    return (*expr.constant & bitMask(low_bits)) ==
           (*base.constant & bitMask(low_bits));
  }

  if (expr.kind == VirtualExprKind::kPhi && base.kind == VirtualExprKind::kPhi &&
      expr.operands.size() == base.operands.size() && !expr.operands.empty()) {
    for (size_t i = 0; i < expr.operands.size(); ++i) {
      if (!isLowBitsProjectionOfExpr(expr.operands[i], base.operands[i],
                                     low_bits)) {
        return false;
      }
    }
    return true;
  }

  if (expr.kind == VirtualExprKind::kTrunc && expr.operands.size() == 1 &&
      expr.bit_width == low_bits && exprEquals(expr.operands[0], base)) {
    return true;
  }

  if ((expr.kind == VirtualExprKind::kZExt ||
       expr.kind == VirtualExprKind::kSExt) &&
      expr.operands.size() == 1 && expr.bit_width == base.bit_width) {
    return isLowBitsProjectionOfExpr(expr.operands[0], base, low_bits);
  }

  return false;
}

std::optional<VirtualValueExpr> simplifyMaskedLowBitReconstruction(
    const VirtualValueExpr &preserved_high_bits,
    const VirtualValueExpr &inserted_low_bits, unsigned result_bits) {
  const VirtualValueExpr *base = nullptr;
  const VirtualValueExpr *low_projection = nullptr;
  uint64_t high_mask = 0;
  uint64_t low_mask = 0;
  if (!matchAndConstantMask(preserved_high_bits, base, high_mask) ||
      !matchAndConstantMask(inserted_low_bits, low_projection, low_mask)) {
    return std::nullopt;
  }

  if (!isContiguousLowBitMask(low_mask))
    return std::nullopt;

  uint64_t full_mask = bitMask(result_bits);
  if ((high_mask & low_mask) != 0 || (high_mask | low_mask) != full_mask)
    return std::nullopt;

  unsigned low_bits = contiguousLowBitMaskWidth(low_mask);
  if (!low_bits || low_bits > result_bits)
    return std::nullopt;

  if (!isLowBitsProjectionOfExpr(*low_projection, *base, low_bits))
    return std::nullopt;

  auto rebuilt = castExprToBitWidth(*base, result_bits);
  rebuilt.complete =
      preserved_high_bits.complete && inserted_low_bits.complete;
  return rebuilt;
}

std::optional<VirtualValueExpr> mergeLowBitsIntoWiderStateExpr(
    const VirtualValueExpr &existing_wide, unsigned wide_bits,
    const VirtualValueExpr &written_value, unsigned written_bits,
    std::optional<unsigned> self_slot_id) {
  if (written_bits == 0 || written_bits > 64 || wide_bits == 0 ||
      wide_bits > 64 || wide_bits <= written_bits) {
    return std::nullopt;
  }

  auto normalized_existing = castExprToBitWidth(existing_wide, wide_bits);
  if (self_slot_id && exprReferencesSlotId(normalized_existing, *self_slot_id))
    return std::nullopt;

  uint64_t low_mask = bitMask(written_bits);
  uint64_t high_mask = bitMask(wide_bits) & ~low_mask;

  auto inserted = castExprToBitWidth(written_value, wide_bits);
  if (low_mask != bitMask(wide_bits)) {
    inserted = binaryExpr(VirtualExprKind::kAnd, std::move(inserted),
                          constantExpr(low_mask, wide_bits), wide_bits);
  }

  if (high_mask == 0)
    return inserted;

  auto preserved =
      binaryExpr(VirtualExprKind::kAnd, std::move(normalized_existing),
                 constantExpr(high_mask, wide_bits), wide_bits);
  return binaryExpr(VirtualExprKind::kOr, std::move(preserved),
                    std::move(inserted), wide_bits);
}

void propagateAliasedStateSlotWrite(
    std::map<unsigned, VirtualValueExpr> &slot_facts, unsigned written_slot_id,
    const VirtualValueExpr &written_value,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info) {
  auto written_it = slot_info.find(written_slot_id);
  if (written_it == slot_info.end())
    return;

  const auto &written_slot = *written_it->second;
  unsigned written_bits = written_slot.width ? (written_slot.width * 8u) : 0u;
  if (written_bits == 0 || written_bits > 64)
    return;

  auto normalized_written = castExprToBitWidth(written_value, written_bits);

  for (const auto &[alias_slot_id, alias_slot_ptr] : slot_info) {
    if (alias_slot_id == written_slot_id)
      continue;

    const auto &alias_slot = *alias_slot_ptr;
    if (alias_slot.base_name != written_slot.base_name ||
        alias_slot.offset != written_slot.offset ||
        alias_slot.from_argument != written_slot.from_argument ||
        alias_slot.from_alloca != written_slot.from_alloca) {
      continue;
    }

    unsigned alias_bits = alias_slot.width ? (alias_slot.width * 8u) : 0u;
    if (alias_bits == 0 || alias_bits > 64)
      continue;

    if (alias_bits < written_bits) {
      slot_facts[alias_slot_id] =
          castExprToBitWidth(normalized_written, alias_bits);
      continue;
    }

    if (alias_bits == written_bits) {
      slot_facts[alias_slot_id] = normalized_written;
      continue;
    }

    auto existing_it = slot_facts.find(alias_slot_id);
    if (existing_it == slot_facts.end())
      continue;

    auto merged = mergeLowBitsIntoWiderStateExpr(
        existing_it->second, alias_bits, normalized_written, written_bits,
        alias_slot_id);
    if (!merged)
      continue;
    slot_facts[alias_slot_id] = std::move(*merged);
  }
}

static bool isBoundedFactExpr(const VirtualValueExpr &expr,
                              bool allow_arguments, unsigned depth = 0) {
  if (depth > 4)
    return false;

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
    case VirtualExprKind::kStateSlot:
    case VirtualExprKind::kStackCell:
      return true;
    case VirtualExprKind::kMemoryRead:
    case VirtualExprKind::kZExt:
    case VirtualExprKind::kSExt:
    case VirtualExprKind::kTrunc:
      return expr.operands.size() == 1 &&
             isBoundedFactExpr(expr.operands.front(), allow_arguments,
                               depth + 1);
    case VirtualExprKind::kArgument:
      return allow_arguments;
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
      if (expr.operands.size() != 2)
        return false;
      return (expr.operands[0].constant.has_value() &&
              isBoundedFactExpr(expr.operands[1], allow_arguments, depth + 1)) ||
             (expr.operands[1].constant.has_value() &&
              isBoundedFactExpr(expr.operands[0], allow_arguments, depth + 1));
    case VirtualExprKind::kPhi:
      return !expr.operands.empty() && expr.operands.size() <= 4 &&
             std::all_of(expr.operands.begin(), expr.operands.end(),
                         [&](const VirtualValueExpr &operand) {
                           return isBoundedFactExpr(operand, allow_arguments,
                                                    depth + 1);
                         });
    default:
      return false;
  }
}

bool isBoundedArgumentFactExpr(const VirtualValueExpr &expr, unsigned depth) {
  return isBoundedFactExpr(expr, /*allow_arguments=*/true, depth);
}

bool isIdentitySlotExpr(const VirtualValueExpr &expr, unsigned slot_id) {
  return expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value() &&
         *expr.slot_id == slot_id;
}

bool isIdentityStackCellExpr(const VirtualValueExpr &expr, unsigned cell_id) {
  return expr.kind == VirtualExprKind::kStackCell &&
         expr.stack_cell_id.has_value() && *expr.stack_cell_id == cell_id;
}

bool isSimpleRemappableFactExpr(const VirtualValueExpr &expr, unsigned depth) {
  return isBoundedFactExpr(expr, /*allow_arguments=*/false, depth);
}

bool containsCallerLocalAllocaStateExpr(const VirtualValueExpr &expr) {
  if ((expr.kind == VirtualExprKind::kStateSlot ||
       expr.kind == VirtualExprKind::kStackCell) &&
      expr.state_base_name.has_value() &&
      !llvm::StringRef(*expr.state_base_name).starts_with("arg")) {
    return true;
  }

  return llvm::any_of(expr.operands, [](const VirtualValueExpr &operand) {
    return containsCallerLocalAllocaStateExpr(operand);
  });
}

bool isGloballyMergeableStateFactExpr(const VirtualValueExpr &expr,
                                      bool allow_arguments) {
  return isBoundedFactExpr(expr, allow_arguments) &&
         !containsCallerLocalAllocaStateExpr(expr);
}

}  // namespace omill::virtual_model::detail

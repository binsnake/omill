#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/bit.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <cstring>
#include <map>
#include <set>

#include "omill/Utils/StateFieldMap.h"

namespace omill::virtual_model::detail {

namespace {

static std::optional<std::pair<VirtualValueExpr, int64_t>>
stripConstantAddSubChain(const VirtualValueExpr &expr) {
  if ((expr.kind != VirtualExprKind::kAdd &&
       expr.kind != VirtualExprKind::kSub) ||
      expr.operands.size() != 2) {
    return std::make_pair(expr, int64_t{0});
  }

  auto accumulate = [&](const VirtualValueExpr &base,
                        uint64_t raw_delta) -> std::optional<
      std::pair<VirtualValueExpr, int64_t>> {
    auto nested = stripConstantAddSubChain(base);
    if (!nested)
      return std::nullopt;
    int64_t delta = static_cast<int64_t>(raw_delta);
    if (expr.kind == VirtualExprKind::kSub)
      delta = -delta;
    nested->second += delta;
    return nested;
  };

  if (expr.operands[1].constant.has_value())
    return accumulate(expr.operands[0], *expr.operands[1].constant);
  if (expr.kind == VirtualExprKind::kAdd &&
      expr.operands[0].constant.has_value())
    return accumulate(expr.operands[1], *expr.operands[0].constant);

  return std::make_pair(expr, int64_t{0});
}

static VirtualValueExpr rebuildAddSubChain(const VirtualValueExpr &base,
                                           int64_t delta,
                                           unsigned result_bits) {
  VirtualValueExpr rebuilt = base;
  rebuilt.bit_width = result_bits;
  if (delta == 0)
    return rebuilt;

  VirtualValueExpr expr;
  expr.kind = delta >= 0 ? VirtualExprKind::kAdd : VirtualExprKind::kSub;
  expr.bit_width = result_bits;
  expr.complete = rebuilt.complete;
  expr.operands.push_back(rebuilt);
  expr.operands.push_back(
      constantExpr(static_cast<uint64_t>(delta >= 0 ? delta : -delta),
                   result_bits));
  return expr;
}

}  // namespace

static std::optional<BooleanSlotExprKey> booleanSlotExprKeyForExpr(
    const VirtualValueExpr &expr) {
  if (expr.kind != VirtualExprKind::kStateSlot || !expr.state_base_name ||
      !expr.state_offset) {
    return std::nullopt;
  }
  bool from_argument = expr.state_base_name->rfind("arg", 0) == 0;
  return BooleanSlotExprKey{*expr.state_base_name, *expr.state_offset,
                            from_argument, !from_argument};
}

static bool collectEvaluatedTargetChoicesImpl(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    const llvm::DenseSet<unsigned> *boolean_slot_ids,
    const std::set<BooleanSlotExprKey> *boolean_slot_expr_keys,
    llvm::SmallDenseSet<unsigned, 8> &visiting_slots,
    llvm::SmallDenseSet<unsigned, 8> &visiting_cells,
    llvm::SmallVectorImpl<uint64_t> &pcs, unsigned depth,
    const BinaryMemoryMap *binary_memory = nullptr) {
  auto &cfg = vmModelConfig();
  if (depth > cfg.max_target_depth || pcs.size() > cfg.max_target_count)
    return false;

  auto append_pc = [&](uint64_t pc) {
    if (!llvm::is_contained(pcs, pc))
      pcs.push_back(pc);
    return pcs.size() <= 4;
  };

  auto lookup_slot = [&](unsigned slot_id) {
    auto it = std::find_if(facts.begin(), facts.end(),
                           [&](const VirtualSlotFact &fact) {
                             return fact.slot_id == slot_id;
                           });
    if (it == facts.end()) {
      if (boolean_slot_ids && boolean_slot_ids->contains(slot_id))
        return append_pc(0) && append_pc(1);
      return false;
    }
    if (!visiting_slots.insert(slot_id).second)
      return false;
    bool ok = collectEvaluatedTargetChoicesImpl(
        it->value, facts, stack_facts, boolean_slot_ids,
        boolean_slot_expr_keys, visiting_slots, visiting_cells, pcs,
        depth + 1, binary_memory);
    visiting_slots.erase(slot_id);
    if (!ok && boolean_slot_ids && boolean_slot_ids->contains(slot_id) &&
        isUnknownLikeExpr(it->value)) {
      return append_pc(0) && append_pc(1);
    }
    return ok;
  };

  auto lookup_stack = [&](unsigned cell_id) {
    auto it = std::find_if(stack_facts.begin(), stack_facts.end(),
                           [&](const VirtualStackFact &fact) {
                             return fact.cell_id == cell_id;
                           });
    if (it == stack_facts.end() || !visiting_cells.insert(cell_id).second)
      return false;
    bool ok = collectEvaluatedTargetChoicesImpl(
        it->value, facts, stack_facts, boolean_slot_ids,
        boolean_slot_expr_keys, visiting_slots, visiting_cells, pcs,
        depth + 1, binary_memory);
    visiting_cells.erase(cell_id);
    return ok;
  };

  auto collect_offset_choices =
      [&](const VirtualValueExpr &base_expr, uint64_t constant,
          bool is_sub) -> bool {
    llvm::SmallVector<uint64_t, 4> base_pcs;
    if (!collectEvaluatedTargetChoicesImpl(base_expr, facts, stack_facts,
                                           boolean_slot_ids,
                                           boolean_slot_expr_keys,
                                           visiting_slots, visiting_cells,
                                           base_pcs, depth + 1,
                                           binary_memory)) {
      return false;
    }
    for (uint64_t base_pc : base_pcs) {
      uint64_t resolved = is_sub ? (base_pc - constant) : (base_pc + constant);
      if (!append_pc(resolved))
        return false;
    }
    return true;
  };

  if (auto resolved = evaluateVirtualExpr(expr, facts, stack_facts,
                                          binary_memory)) {
    return append_pc(*resolved);
  }

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
      return expr.constant.has_value() && append_pc(*expr.constant);
    case VirtualExprKind::kStateSlot:
      if (expr.slot_id.has_value())
        return lookup_slot(*expr.slot_id);
      if (boolean_slot_expr_keys) {
        auto key = booleanSlotExprKeyForExpr(expr);
        if (key && boolean_slot_expr_keys->find(*key) !=
                       boolean_slot_expr_keys->end())
          return append_pc(0) && append_pc(1);
      }
      return false;
    case VirtualExprKind::kStackCell:
      return expr.stack_cell_id.has_value() && lookup_stack(*expr.stack_cell_id);
    case VirtualExprKind::kZExt:
    case VirtualExprKind::kSExt:
    case VirtualExprKind::kTrunc: {
      if (expr.operands.size() != 1)
        return false;
      llvm::SmallVector<uint64_t, 4> values;
      if (!collectEvaluatedTargetChoicesImpl(expr.operands.front(), facts,
                                             stack_facts, boolean_slot_ids,
                                             boolean_slot_expr_keys,
                                             visiting_slots, visiting_cells,
                                             values, depth + 1,
                                             binary_memory)) {
        return false;
      }
      unsigned source_bits = expr.operands.front().bit_width
                                 ? expr.operands.front().bit_width
                                 : expr.bit_width;
      for (uint64_t value : values) {
        uint64_t casted = value;
        switch (expr.kind) {
          case VirtualExprKind::kZExt:
            casted = value & bitMask(std::min(source_bits, expr.bit_width));
            break;
          case VirtualExprKind::kSExt:
            casted = signExtendBits(value, source_bits) & bitMask(expr.bit_width);
            break;
          case VirtualExprKind::kTrunc:
            casted = value & bitMask(expr.bit_width);
            break;
          default:
            break;
        }
        if (!append_pc(casted))
          return false;
      }
      return !pcs.empty() && pcs.size() <= 4;
    }
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
      if (expr.operands.size() != 2)
        return false;
      if (expr.kind == VirtualExprKind::kAdd &&
          expr.operands[0].constant.has_value()) {
        return collect_offset_choices(expr.operands[1],
                                      *expr.operands[0].constant,
                                      /*is_sub=*/false);
      }
      if (expr.operands[1].constant.has_value())
        return collect_offset_choices(expr.operands[0],
                                      *expr.operands[1].constant,
                                      /*is_sub=*/expr.kind ==
                                          VirtualExprKind::kSub);
      return false;
    case VirtualExprKind::kPhi:
      if (expr.operands.empty() || expr.operands.size() > 4)
        return false;
      for (const auto &operand : expr.operands) {
        if (!collectEvaluatedTargetChoicesImpl(operand, facts, stack_facts,
                                               boolean_slot_ids,
                                               boolean_slot_expr_keys,
                                               visiting_slots, visiting_cells,
                                               pcs, depth + 1,
                                               binary_memory)) {
          return false;
        }
      }
      return !pcs.empty() && pcs.size() <= 4;
    default:
      return false;
  }
}

bool collectEvaluatedTargetChoices(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    const llvm::DenseSet<unsigned> *boolean_slot_ids,
    const std::set<BooleanSlotExprKey> *boolean_slot_expr_keys,
    llvm::SmallVectorImpl<uint64_t> &pcs,
    const BinaryMemoryMap *binary_memory) {
  llvm::SmallDenseSet<unsigned, 8> visiting_slots;
  llvm::SmallDenseSet<unsigned, 8> visiting_cells;
  return collectEvaluatedTargetChoicesImpl(expr, facts, stack_facts,
                                           boolean_slot_ids,
                                           boolean_slot_expr_keys,
                                           visiting_slots, visiting_cells, pcs,
                                           /*depth=*/0, binary_memory) &&
         !pcs.empty();
}

static bool collectEvaluatedValueChoicesImpl(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    llvm::SmallDenseSet<unsigned, 8> &visiting_slots,
    llvm::SmallDenseSet<unsigned, 8> &visiting_cells,
    llvm::SmallVectorImpl<uint64_t> &values, unsigned depth = 0,
    const BinaryMemoryMap *binary_memory = nullptr) {
  if (depth > 4 || expr.kind == VirtualExprKind::kUnknown)
    return false;

  llvm::SmallVector<uint64_t, 8> unique_values;
  auto append_value = [&](uint64_t value) {
    value &= bitMask(expr.bit_width);
    if (llvm::is_contained(unique_values, value))
      return true;
    unique_values.push_back(value);
    values.push_back(value);
    return values.size() <= 4;
  };

  auto lookup_slot =
      [&](unsigned slot_id, llvm::SmallVectorImpl<uint64_t> &slot_values) {
        if (!visiting_slots.insert(slot_id).second)
          return false;
        auto pop_visit =
            llvm::make_scope_exit([&] { visiting_slots.erase(slot_id); });
        auto it = llvm::find_if(facts, [&](const VirtualSlotFact &fact) {
          return fact.slot_id == slot_id;
        });
        if (it == facts.end())
          return false;
        return collectEvaluatedValueChoicesImpl(it->value, facts, stack_facts,
                                                visiting_slots, visiting_cells,
                                                slot_values, depth + 1,
                                                binary_memory);
      };

  auto lookup_stack =
      [&](unsigned cell_id, llvm::SmallVectorImpl<uint64_t> &cell_values) {
        if (!visiting_cells.insert(cell_id).second)
          return false;
        auto pop_visit =
            llvm::make_scope_exit([&] { visiting_cells.erase(cell_id); });
        auto it = llvm::find_if(stack_facts, [&](const VirtualStackFact &fact) {
          return fact.cell_id == cell_id;
        });
        if (it == stack_facts.end())
          return false;
        return collectEvaluatedValueChoicesImpl(it->value, facts, stack_facts,
                                                visiting_slots, visiting_cells,
                                                cell_values, depth + 1,
                                                binary_memory);
      };

  auto collect_operand_choices =
      [&](const VirtualValueExpr &operand,
          llvm::SmallVectorImpl<uint64_t> &operand_values) {
        llvm::SmallDenseSet<unsigned, 8> nested_slots = visiting_slots;
        llvm::SmallDenseSet<unsigned, 8> nested_cells = visiting_cells;
        return collectEvaluatedValueChoicesImpl(operand, facts, stack_facts,
                                                nested_slots, nested_cells,
                                                operand_values, depth + 1,
                                                binary_memory);
      };

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
      return expr.constant.has_value() && append_value(*expr.constant);
    case VirtualExprKind::kStateSlot: {
      if (!expr.slot_id.has_value())
        return false;
      return lookup_slot(*expr.slot_id, values);
    }
    case VirtualExprKind::kStackCell: {
      if (!expr.stack_cell_id.has_value())
        return false;
      return lookup_stack(*expr.stack_cell_id, values);
    }
    case VirtualExprKind::kMemoryRead: {
      if (!binary_memory || expr.operands.size() != 1)
        return false;
      llvm::SmallVector<uint64_t, 4> address_values;
      if (!collect_operand_choices(expr.operands[0], address_values) ||
          address_values.empty()) {
        return false;
      }
      for (uint64_t address : address_values) {
        auto loaded = readBinaryConstantExpr(*binary_memory, address,
                                             expr.bit_width);
        if (!loaded || !loaded->constant.has_value())
          return false;
        if (!append_value(*loaded->constant))
          return false;
      }
      return !values.empty();
    }
    case VirtualExprKind::kZExt:
    case VirtualExprKind::kSExt:
    case VirtualExprKind::kTrunc: {
      if (expr.operands.size() != 1)
        return false;
      llvm::SmallVector<uint64_t, 4> operand_values;
      if (!collect_operand_choices(expr.operands[0], operand_values) ||
          operand_values.empty()) {
        return false;
      }
      unsigned source_bits = expr.operands.front().bit_width
                                 ? expr.operands.front().bit_width
                                 : expr.bit_width;
      for (uint64_t value : operand_values) {
        uint64_t casted = value;
        switch (expr.kind) {
          case VirtualExprKind::kZExt:
            casted = value & bitMask(std::min(source_bits, expr.bit_width));
            break;
          case VirtualExprKind::kSExt:
            casted = signExtendBits(value, source_bits) & bitMask(expr.bit_width);
            break;
          case VirtualExprKind::kTrunc:
            casted = value & bitMask(expr.bit_width);
            break;
          default:
            break;
        }
        if (!append_value(casted))
          return false;
      }
      return !values.empty();
    }
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
    case VirtualExprKind::kMul:
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
    case VirtualExprKind::kSge: {
      if (expr.operands.size() != 2)
        return false;

      // Bounded fallback: a single-bit mask always collapses to a finite
      // two-value set even if the masked operand itself is not otherwise
      // enumerable. This is enough to recover patterns like
      // `base + zext((slot >> k) & 1)` as a 2-way dispatch choice.
      if (expr.kind == VirtualExprKind::kAnd) {
        const auto &lhs = expr.operands[0];
        const auto &rhs = expr.operands[1];
        auto append_mask_choices = [&](uint64_t mask) {
          mask &= bitMask(expr.bit_width);
          if (llvm::popcount(mask) != 1)
            return false;
          return append_value(0) && append_value(mask);
        };
        if (rhs.constant.has_value() && append_mask_choices(*rhs.constant))
          return true;
        if (lhs.constant.has_value() && append_mask_choices(*lhs.constant))
          return true;
      }

      llvm::SmallVector<uint64_t, 4> lhs_values;
      llvm::SmallVector<uint64_t, 4> rhs_values;
      if (!collect_operand_choices(expr.operands[0], lhs_values) ||
          !collect_operand_choices(expr.operands[1], rhs_values) ||
          lhs_values.empty() || rhs_values.empty() ||
          (lhs_values.size() * rhs_values.size()) > 4) {
        return false;
      }

      auto apply_binary = [&](uint64_t lhs, uint64_t rhs) -> uint64_t {
        switch (expr.kind) {
          case VirtualExprKind::kAdd:
            return lhs + rhs;
          case VirtualExprKind::kSub:
            return lhs - rhs;
          case VirtualExprKind::kMul:
            return lhs * rhs;
          case VirtualExprKind::kXor:
            return lhs ^ rhs;
          case VirtualExprKind::kAnd:
            return lhs & rhs;
          case VirtualExprKind::kOr:
            return lhs | rhs;
          case VirtualExprKind::kShl:
            return rhs < 64 ? (lhs << rhs) : 0ULL;
          case VirtualExprKind::kLShr:
            return rhs < 64 ? (lhs >> rhs) : 0ULL;
          case VirtualExprKind::kAShr:
            if (rhs >= 64)
              return (lhs & (1ULL << 63)) ? ~0ULL : 0ULL;
            return static_cast<uint64_t>(static_cast<int64_t>(lhs) >>
                                         static_cast<int64_t>(rhs));
          case VirtualExprKind::kEq:
            return static_cast<uint64_t>(lhs == rhs);
          case VirtualExprKind::kNe:
            return static_cast<uint64_t>(lhs != rhs);
          case VirtualExprKind::kUlt:
            return static_cast<uint64_t>(lhs < rhs);
          case VirtualExprKind::kUle:
            return static_cast<uint64_t>(lhs <= rhs);
          case VirtualExprKind::kUgt:
            return static_cast<uint64_t>(lhs > rhs);
          case VirtualExprKind::kUge:
            return static_cast<uint64_t>(lhs >= rhs);
          case VirtualExprKind::kSlt:
            return static_cast<uint64_t>(static_cast<int64_t>(lhs) <
                                         static_cast<int64_t>(rhs));
          case VirtualExprKind::kSle:
            return static_cast<uint64_t>(static_cast<int64_t>(lhs) <=
                                         static_cast<int64_t>(rhs));
          case VirtualExprKind::kSgt:
            return static_cast<uint64_t>(static_cast<int64_t>(lhs) >
                                         static_cast<int64_t>(rhs));
          case VirtualExprKind::kSge:
            return static_cast<uint64_t>(static_cast<int64_t>(lhs) >=
                                         static_cast<int64_t>(rhs));
          default:
            return 0;
        }
      };

      for (uint64_t lhs : lhs_values) {
        for (uint64_t rhs : rhs_values) {
          if (!append_value(apply_binary(lhs, rhs)))
            return false;
        }
      }
      return !values.empty();
    }
    case VirtualExprKind::kSelect: {
      if (expr.operands.size() != 3)
        return false;
      llvm::SmallVector<uint64_t, 4> cond_values;
      llvm::SmallVector<uint64_t, 4> true_values;
      llvm::SmallVector<uint64_t, 4> false_values;
      if (!collect_operand_choices(expr.operands[0], cond_values) ||
          !collect_operand_choices(expr.operands[1], true_values) ||
          !collect_operand_choices(expr.operands[2], false_values) ||
          cond_values.empty()) {
        return false;
      }
      for (uint64_t cond : cond_values) {
        auto &branch_values = cond ? true_values : false_values;
        for (uint64_t value : branch_values) {
          if (!append_value(value))
            return false;
        }
      }
      return !values.empty();
    }
    case VirtualExprKind::kPhi: {
      if (expr.operands.empty() || expr.operands.size() > 4)
        return false;
      for (const auto &operand : expr.operands) {
        llvm::SmallVector<uint64_t, 4> operand_values;
        if (!collect_operand_choices(operand, operand_values))
          return false;
        for (uint64_t value : operand_values) {
          if (!append_value(value))
            return false;
        }
      }
      return !values.empty();
    }
    default:
      return false;
  }
}

bool collectEvaluatedValueChoices(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    llvm::SmallVectorImpl<uint64_t> &values,
    const BinaryMemoryMap *binary_memory) {
  llvm::SmallDenseSet<unsigned, 8> visiting_slots;
  llvm::SmallDenseSet<unsigned, 8> visiting_cells;
  return collectEvaluatedValueChoicesImpl(expr, facts, stack_facts,
                                          visiting_slots, visiting_cells,
                                          values, /*depth=*/0, binary_memory);
}

VirtualValueExpr specializeExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> *incoming_stack,
    const std::map<unsigned, VirtualValueExpr> *incoming_args) {
  if (expr.kind == VirtualExprKind::kArgument &&
      expr.argument_index.has_value() && incoming_args) {
    auto it = incoming_args->find(*expr.argument_index);
    if (it != incoming_args->end()) {
      if (isUnknownLikeExpr(it->second))
        return expr;
      return it->second;
    }
    return expr;
  }
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value()) {
    auto it = incoming.find(*expr.slot_id);
    if (it != incoming.end()) {
      if (isUnknownLikeExpr(it->second))
        return expr;
      return it->second;
    }
    return expr;
  }
  if (expr.kind == VirtualExprKind::kStackCell && expr.stack_cell_id.has_value() &&
      incoming_stack) {
    auto it = incoming_stack->find(*expr.stack_cell_id);
    if (it != incoming_stack->end()) {
      if (isUnknownLikeExpr(it->second))
        return expr;
      return it->second;
    }
    return expr;
  }

  VirtualValueExpr result = expr;
  result.operands.clear();
  for (const auto &operand : expr.operands)
    result.operands.push_back(
        specializeExpr(operand, incoming, incoming_stack, incoming_args));

  auto fold_binary = [&](auto fn) -> std::optional<VirtualValueExpr> {
    if (result.operands.size() != 2)
      return std::nullopt;
    const auto &lhs = result.operands[0];
    const auto &rhs = result.operands[1];
    if (!lhs.constant.has_value() || !rhs.constant.has_value())
      return std::nullopt;
    return constantExpr(
        fn(*lhs.constant, *rhs.constant) & bitMask(result.bit_width),
        result.bit_width);
  };

  auto fold_unary = [&](auto fn) -> std::optional<VirtualValueExpr> {
    if (result.operands.size() != 1 || !result.operands[0].constant.has_value())
      return std::nullopt;
    return constantExpr(fn(*result.operands[0].constant) &
                            bitMask(result.bit_width),
                        result.bit_width);
  };

  switch (result.kind) {
    case VirtualExprKind::kZExt:
      if (auto folded = fold_unary([&](uint64_t value) {
            unsigned source_bits = result.operands.front().bit_width
                                       ? result.operands.front().bit_width
                                       : result.bit_width;
            return value & bitMask(std::min(source_bits, result.bit_width));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSExt:
      if (auto folded = fold_unary([&](uint64_t value) {
            unsigned source_bits = result.operands.front().bit_width
                                       ? result.operands.front().bit_width
                                       : result.bit_width;
            return signExtendBits(value, source_bits);
          }))
        return *folded;
      break;
    case VirtualExprKind::kTrunc:
      if (auto folded =
              fold_unary([&](uint64_t value) { return value & bitMask(result.bit_width); }))
        return *folded;
      break;
    case VirtualExprKind::kAdd:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a + b; }))
        return *folded;
      if (auto stripped = stripConstantAddSubChain(result)) {
        if (stripped->second != 0 || !exprEquals(stripped->first, result))
          return rebuildAddSubChain(stripped->first, stripped->second,
                                    result.bit_width);
      }
      break;
    case VirtualExprKind::kSub:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a - b; }))
        return *folded;
      if (auto stripped = stripConstantAddSubChain(result)) {
        if (stripped->second != 0 || !exprEquals(stripped->first, result))
          return rebuildAddSubChain(stripped->first, stripped->second,
                                    result.bit_width);
      }
      break;
    case VirtualExprKind::kMul:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a * b; }))
        return *folded;
      break;
    case VirtualExprKind::kXor:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a ^ b; }))
        return *folded;
      break;
    case VirtualExprKind::kAnd:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a & b; }))
        return *folded;
      break;
    case VirtualExprKind::kOr:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a | b; }))
        return *folded;
      if (auto rebuilt = simplifyMaskedLowBitReconstruction(
              result.operands[0], result.operands[1], result.bit_width)) {
        return *rebuilt;
      }
      if (auto rebuilt = simplifyMaskedLowBitReconstruction(
              result.operands[1], result.operands[0], result.bit_width)) {
        return *rebuilt;
      }
      break;
    case VirtualExprKind::kShl:
      if (auto folded =
              fold_binary([](uint64_t a, uint64_t b) { return (b < 64) ? (a << b) : 0ULL; }))
        return *folded;
      break;
    case VirtualExprKind::kLShr:
      if (auto folded =
              fold_binary([](uint64_t a, uint64_t b) { return (b < 64) ? (a >> b) : 0ULL; }))
        return *folded;
      break;
    case VirtualExprKind::kAShr:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            if (b >= 64)
              return (a & (1ULL << 63)) ? ~0ULL : 0ULL;
            return static_cast<uint64_t>(static_cast<int64_t>(a) >>
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSelect:
      if (result.operands.size() == 3 &&
          result.operands[0].constant.has_value()) {
        return result.operands[*result.operands[0].constant ? 1 : 2];
      }
      break;
    case VirtualExprKind::kEq:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a == b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kNe:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a != b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUlt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a < b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUle:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a <= b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUgt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a > b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUge:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a >= b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kSlt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) <
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSle:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) <=
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSgt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) >
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSge:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) >=
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kPhi:
      if (!result.operands.empty()) {
        bool same = std::all_of(result.operands.begin() + 1,
                                result.operands.end(),
                                [&](const VirtualValueExpr &other) {
                                  return exprEquals(result.operands.front(),
                                                    other);
                                });
        if (same)
          return result.operands.front();
      }
      break;
    default:
      break;
  }

  result.complete = std::all_of(
      result.operands.begin(), result.operands.end(),
      [](const VirtualValueExpr &operand) { return operand.complete; });
  return result;
}

/// Count total nodes in an expression tree (for growth detection).
static unsigned countExprNodes(const VirtualValueExpr &expr) {
  unsigned count = 1;
  for (auto &child : expr.operands)
    count += countExprNodes(child);
  return count;
}

VirtualValueExpr specializeExprToFixpoint(
    VirtualValueExpr expr,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> *incoming_stack,
    const std::map<unsigned, VirtualValueExpr> *incoming_args,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    unsigned max_rounds) {
  for (unsigned round = 0; round < max_rounds; ++round) {
    annotateExprSlots(expr, slot_ids);
    annotateExprStackCells(expr, stack_cell_ids, slot_ids);
    auto specialized =
        specializeExpr(expr, incoming, incoming_stack, incoming_args);
    annotateExprSlots(specialized, slot_ids);
    annotateExprStackCells(specialized, stack_cell_ids, slot_ids);
    canonicalizeMemoryReadsToStackCells(specialized, stack_cell_ids, slot_ids);
    annotateExprSlots(specialized, slot_ids);
    annotateExprStackCells(specialized, stack_cell_ids, slot_ids);

    // Fixpoint: no further substitution possible.
    if (exprEquals(specialized, expr))
      break;
    // Safety: bail if expression is growing rather than simplifying.
    if (countExprNodes(specialized) > countExprNodes(expr) * 2)
      break;

    expr = std::move(specialized);
  }
  return expr;
}

void specializeFactStateToFixpoint(
    std::map<unsigned, VirtualValueExpr> &slot_facts,
    std::map<unsigned, VirtualValueExpr> &stack_facts,
    const std::map<unsigned, VirtualValueExpr> *argument_facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    unsigned max_rounds) {
  for (unsigned round = 0; round < max_rounds; ++round) {
    auto snapshot_slots = slot_facts;
    auto snapshot_stack = stack_facts;

    for (auto &[slot_id, value] : snapshot_slots) {
      (void) slot_id;
      annotateExprSlots(value, slot_ids);
      annotateExprStackCells(value, stack_cell_ids, slot_ids);
    }
    for (auto &[cell_id, value] : snapshot_stack) {
      (void) cell_id;
      annotateExprSlots(value, slot_ids);
      annotateExprStackCells(value, stack_cell_ids, slot_ids);
    }

    bool changed = false;
    for (auto &[slot_id, value] : slot_facts) {
      auto specialized = specializeExprToFixpoint(
          value, snapshot_slots, &snapshot_stack, argument_facts, slot_ids,
          stack_cell_ids, /*max_rounds=*/1);
      if (!exprEquals(specialized, value)) {
        value = std::move(specialized);
        changed = true;
      }
    }
    for (auto &[cell_id, value] : stack_facts) {
      auto specialized = specializeExprToFixpoint(
          value, snapshot_slots, &snapshot_stack, argument_facts, slot_ids,
          stack_cell_ids, /*max_rounds=*/1);
      if (!exprEquals(specialized, value)) {
        value = std::move(specialized);
        changed = true;
      }
    }
    if (!changed)
      break;
  }
}

void computeOutgoingFactMaps(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_arg_map,
    std::map<unsigned, VirtualValueExpr> &outgoing,
    std::map<unsigned, VirtualValueExpr> &outgoing_stack) {
  outgoing = incoming_map;
  for (const auto &transfer : summary.state_transfers) {
    if (!transfer.target_slot.canonical_id.has_value())
      continue;
    outgoing[*transfer.target_slot.canonical_id] =
        specializeExpr(transfer.value, incoming_map, &incoming_stack_map,
                       &incoming_arg_map);
  }

  outgoing_stack = incoming_stack_map;
  for (const auto &transfer : summary.stack_transfers) {
    if (!transfer.target_cell.canonical_id.has_value())
      continue;
    outgoing_stack[*transfer.target_cell.canonical_id] =
        specializeExpr(transfer.value, incoming_map, &incoming_stack_map,
                       &incoming_arg_map);
  }
}

std::vector<VirtualSlotFact> computeOutgoingFacts(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_arg_map) {
  std::map<unsigned, VirtualValueExpr> outgoing;
  std::map<unsigned, VirtualValueExpr> outgoing_stack;
  computeOutgoingFactMaps(summary, incoming_map, incoming_stack_map,
                          incoming_arg_map, outgoing, outgoing_stack);

  std::vector<VirtualSlotFact> facts;
  for (const auto &[slot_id, value] : outgoing)
    facts.push_back(VirtualSlotFact{slot_id, value});
  return facts;
}

std::vector<VirtualStackFact> computeOutgoingStackFacts(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_arg_map) {
  std::map<unsigned, VirtualValueExpr> outgoing;
  std::map<unsigned, VirtualValueExpr> outgoing_stack;
  computeOutgoingFactMaps(summary, incoming_map, incoming_stack_map,
                          incoming_arg_map, outgoing, outgoing_stack);

  std::vector<VirtualStackFact> facts;
  for (const auto &[cell_id, value] : outgoing_stack)
    facts.push_back(VirtualStackFact{cell_id, value});
  return facts;
}

std::map<SlotKey, unsigned> buildSlotIdMap(
    const VirtualMachineModel &model) {
  std::map<SlotKey, unsigned> slot_ids;
  for (const auto &slot : model.slots()) {
    slot_ids.emplace(SlotKey{slot.base_name, slot.offset, slot.width,
                             slot.from_argument, slot.from_alloca},
                     slot.id);
  }
  return slot_ids;
}

std::map<StackCellKey, unsigned> buildStackCellIdMap(
    const VirtualMachineModel &model) {
  std::map<StackCellKey, unsigned> stack_cell_ids;
  for (const auto &cell : model.stackCells()) {
    stack_cell_ids.emplace(
        StackCellKey{SlotKey{cell.base_name, cell.base_offset, cell.base_width,
                             cell.base_from_argument, cell.base_from_alloca},
                     cell.cell_offset, cell.width},
        cell.id);
  }
  return stack_cell_ids;
}

llvm::DenseSet<unsigned> buildBooleanFlagSlotIds(
    llvm::Module &M, const VirtualMachineModel &model) {
  llvm::DenseSet<unsigned> boolean_slot_ids;
  StateFieldMap field_map(M);
  for (const auto &slot : model.slots()) {
    if (!slot.from_argument)
      continue;
    auto field = field_map.fieldAtOffset(static_cast<unsigned>(slot.offset));
    if (!field || field->category != StateFieldCategory::kFlag ||
        field->size != 1) {
      continue;
    }
    boolean_slot_ids.insert(slot.id);
  }
  return boolean_slot_ids;
}

std::set<BooleanSlotExprKey> buildBooleanFlagExprKeys(
    llvm::Module &M, const VirtualMachineModel &model) {
  std::set<BooleanSlotExprKey> keys;
  StateFieldMap field_map(M);
  for (const auto &slot : model.slots()) {
    if (!slot.from_argument)
      continue;
    auto field = field_map.fieldAtOffset(static_cast<unsigned>(slot.offset));
    if (!field || field->category != StateFieldCategory::kFlag ||
        field->size != 1) {
      continue;
    }
    keys.emplace(slot.base_name, slot.offset, slot.from_argument,
                 slot.from_alloca);
  }
  return keys;
}

}  // namespace omill::virtual_model::detail

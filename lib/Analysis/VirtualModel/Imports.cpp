#include "Analysis/VirtualModel/Internal.h"

#include <algorithm>

namespace omill::virtual_model::detail {

namespace {

static bool functionHasAllocaNamed(const llvm::Function &F,
                                   llvm::StringRef base_name) {
  for (const auto &BB : F) {
    for (const auto &I : BB) {
      const auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I);
      if (!alloca)
        continue;
      if (alloca->getName() == base_name)
        return true;
    }
  }
  return false;
}

static std::optional<unsigned> lookupMappedCallerSlotIdByPointerArgs(
    llvm::CallBase &call, llvm::StringRef callee_base_name,
    int64_t callee_offset, unsigned width,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl) {
  std::optional<unsigned> mapped_slot_id;
  for (unsigned arg_index = 0; arg_index < call.arg_size(); ++arg_index) {
    auto *actual_arg = call.getArgOperand(arg_index);
    if (!actual_arg->getType()->isPointerTy())
      continue;
    auto actual_slot = extractStateSlotSummary(actual_arg, width, dl);
    if (!actual_slot || !actual_slot->from_alloca ||
        actual_slot->base_name != callee_base_name) {
      continue;
    }

    VirtualStateSlotSummary mapped_slot = *actual_slot;
    mapped_slot.offset += callee_offset;
    mapped_slot.width = width;

    auto slot_id = lookupSlotIdForSummary(mapped_slot, slot_ids);
    if (!slot_id)
      continue;
    if (mapped_slot_id && *mapped_slot_id != *slot_id)
      return std::nullopt;
    mapped_slot_id = *slot_id;
  }
  return mapped_slot_id;
}

static std::optional<unsigned> lookupMappedCallerStackCellIdByPointerArgs(
    llvm::CallBase &call, llvm::StringRef callee_base_name,
    int64_t callee_base_offset, unsigned callee_base_width,
    int64_t callee_cell_offset, unsigned width,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  std::optional<unsigned> mapped_cell_id;
  for (unsigned arg_index = 0; arg_index < call.arg_size(); ++arg_index) {
    auto *actual_arg = call.getArgOperand(arg_index);
    if (!actual_arg->getType()->isPointerTy())
      continue;

    VirtualStackCellSummary mapped_cell;
    if (auto actual_slot =
            extractStateSlotSummary(actual_arg, callee_base_width, dl)) {
      if (!actual_slot->from_alloca ||
          actual_slot->base_name != callee_base_name) {
        continue;
      }
      mapped_cell.base_name = actual_slot->base_name;
      mapped_cell.base_offset = actual_slot->offset + callee_base_offset;
      mapped_cell.base_width = actual_slot->width;
      mapped_cell.base_from_argument = actual_slot->from_argument;
      mapped_cell.base_from_alloca = actual_slot->from_alloca;
      mapped_cell.offset = callee_cell_offset;
      mapped_cell.width = width;
    } else if (auto actual_cell = extractStackCellSummaryFromExpr(
                   summarizeValueExpr(actual_arg, dl), width)) {
      if (!actual_cell->base_from_alloca ||
          actual_cell->base_name != callee_base_name ||
          actual_cell->base_offset != callee_base_offset) {
        continue;
      }
      mapped_cell = *actual_cell;
      mapped_cell.offset += callee_cell_offset;
      mapped_cell.width = width;
    } else {
      continue;
    }

    auto cell_id = lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
    if (!cell_id)
      continue;
    if (mapped_cell_id && *mapped_cell_id != *cell_id)
      return std::nullopt;
    mapped_cell_id = *cell_id;
  }
  return mapped_cell_id;
}

static std::optional<VirtualValueExpr> remapStateSlotExprByShape(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl) {
  if (expr.kind != VirtualExprKind::kStateSlot || !expr.state_base_name ||
      !expr.state_offset) {
    return std::nullopt;
  }

  auto arg_index = parseArgumentBaseName(*expr.state_base_name);
  VirtualStateSlotSummary remapped_slot;
  if (arg_index && *arg_index < call.arg_size()) {
    if (auto actual_slot = extractStateSlotSummary(
            call.getArgOperand(*arg_index), exprByteWidth(expr), dl)) {
      remapped_slot = *actual_slot;
    } else {
      return std::nullopt;
    }
  } else {
    auto mapped_slot_id = lookupMappedCallerSlotIdByPointerArgs(
        call, *expr.state_base_name, *expr.state_offset, exprByteWidth(expr),
        slot_ids, dl);
    if (!mapped_slot_id)
      return std::nullopt;
    const auto &mapped_info = *slot_info.at(*mapped_slot_id);
    VirtualValueExpr mapped = expr;
    mapped.slot_id = mapped_slot_id;
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.offset;
    mapped.bit_width = mapped_info.width * 8;
    return mapped;
  }

  remapped_slot.offset += *expr.state_offset;
  remapped_slot.width = exprByteWidth(expr);

  auto mapped_slot_id = lookupSlotIdForSummary(remapped_slot, slot_ids);
  VirtualValueExpr mapped = expr;
  mapped.slot_id = mapped_slot_id;
  if (mapped_slot_id) {
    const auto &mapped_info = *slot_info.at(*mapped_slot_id);
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.offset;
    mapped.bit_width = mapped_info.width * 8;
  } else {
    mapped.state_base_name = remapped_slot.base_name;
    mapped.state_offset = remapped_slot.offset;
    mapped.bit_width = remapped_slot.width * 8;
  }
  return mapped;
}

static std::optional<VirtualValueExpr> remapStackCellExprByShape(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  if (expr.kind != VirtualExprKind::kStackCell || !expr.state_base_name ||
      !expr.state_offset || !expr.stack_offset) {
    return std::nullopt;
  }

  VirtualStackCellSummary remapped_cell;
  if (auto arg_index = parseArgumentBaseName(*expr.state_base_name);
      arg_index && *arg_index < call.arg_size()) {
    auto *actual_arg = call.getArgOperand(*arg_index);
    unsigned base_width = std::max(1u, getValueBitWidth(actual_arg, dl) / 8u);
    if (auto actual_slot = extractStateSlotSummary(actual_arg, base_width, dl)) {
      remapped_cell.base_name = actual_slot->base_name;
      remapped_cell.base_offset = actual_slot->offset + *expr.state_offset;
      remapped_cell.base_width = actual_slot->width;
      remapped_cell.base_from_argument = actual_slot->from_argument;
      remapped_cell.base_from_alloca = actual_slot->from_alloca;
      remapped_cell.offset = *expr.stack_offset;
      remapped_cell.width = exprByteWidth(expr);
    } else {
      auto actual_expr = summarizeValueExpr(actual_arg, dl);
      annotateExprSlots(actual_expr, slot_ids);
      annotateExprStackCells(actual_expr, stack_cell_ids, slot_ids);
      if (auto actual_cell =
              extractStackCellSummaryFromExpr(actual_expr, exprByteWidth(expr))) {
        remapped_cell.base_name = actual_cell->base_name;
        remapped_cell.base_offset = actual_cell->base_offset + *expr.state_offset;
        remapped_cell.base_width = actual_cell->base_width;
        remapped_cell.base_from_argument = actual_cell->base_from_argument;
        remapped_cell.base_from_alloca = actual_cell->base_from_alloca;
        remapped_cell.offset = actual_cell->offset + *expr.stack_offset;
        remapped_cell.width = exprByteWidth(expr);
      } else {
        return std::nullopt;
      }
    }
  } else {
    auto mapped_cell_id = lookupMappedCallerStackCellIdByPointerArgs(
        call, *expr.state_base_name, *expr.state_offset,
        std::max(1u, expr.bit_width / 8u), *expr.stack_offset,
        exprByteWidth(expr), slot_ids, stack_cell_ids, dl);
    if (!mapped_cell_id)
      return std::nullopt;
    const auto &mapped_info = *stack_cell_info.at(*mapped_cell_id);
    VirtualValueExpr mapped = expr;
    mapped.stack_cell_id = mapped_cell_id;
    mapped.slot_id = mapped_info.base_slot_id;
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.base_offset;
    mapped.stack_offset = mapped_info.cell_offset;
    mapped.bit_width = mapped_info.width * 8;
    return mapped;
  }

  auto mapped_cell_id = lookupStackCellIdForSummary(remapped_cell, stack_cell_ids);
  VirtualValueExpr mapped = expr;
  mapped.stack_cell_id = mapped_cell_id;
  if (mapped_cell_id) {
    const auto &mapped_info = *stack_cell_info.at(*mapped_cell_id);
    mapped.slot_id = mapped_info.base_slot_id;
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.base_offset;
    mapped.stack_offset = mapped_info.cell_offset;
    mapped.bit_width = mapped_info.width * 8;
  } else {
    VirtualStateSlotSummary base_slot;
    base_slot.base_name = remapped_cell.base_name;
    base_slot.offset = remapped_cell.base_offset;
    base_slot.width = remapped_cell.base_width;
    base_slot.from_argument = remapped_cell.base_from_argument;
    base_slot.from_alloca = remapped_cell.base_from_alloca;
    mapped.slot_id = lookupSlotIdForSummary(base_slot, slot_ids);
    mapped.state_base_name = remapped_cell.base_name;
    mapped.state_offset = remapped_cell.base_offset;
    mapped.stack_offset = remapped_cell.offset;
    mapped.bit_width = remapped_cell.width * 8;
  }
  return mapped;
}

static bool containsInvalidCallerArgumentRelativeState(
    const VirtualValueExpr &expr, const llvm::Function &caller_fn) {
  if ((expr.kind == VirtualExprKind::kStateSlot ||
       expr.kind == VirtualExprKind::kStackCell) &&
      expr.state_base_name.has_value()) {
    if (auto arg_index = parseArgumentBaseName(*expr.state_base_name);
        !arg_index || *arg_index >= caller_fn.arg_size() ||
        !caller_fn.getArg(*arg_index)->getType()->isPointerTy()) {
      if (!functionHasAllocaNamed(caller_fn, *expr.state_base_name))
        return true;
    }
  }

  return llvm::any_of(expr.operands, [&](const VirtualValueExpr &operand) {
    return containsInvalidCallerArgumentRelativeState(operand, caller_fn);
  });
}

static std::optional<StackCellKey> extractStackCellKeyFromExpr(
    const VirtualValueExpr &expr) {
  auto summary = extractStackCellSummaryFromExpr(expr, exprByteWidth(expr));
  if (!summary)
    return std::nullopt;
  return stackCellKeyForSummary(*summary);
}

static VirtualValueExpr substituteStructuralStackFacts(
    const VirtualValueExpr &expr,
    const std::map<StackCellKey, VirtualValueExpr> *structural_stack_facts,
    unsigned depth = 0) {
  if (!structural_stack_facts || depth >= 4)
    return expr;

  if (expr.kind == VirtualExprKind::kStackCell) {
    if (auto key = extractStackCellKeyFromExpr(expr)) {
      if (auto it = structural_stack_facts->find(*key);
          it != structural_stack_facts->end() &&
          !exprEquals(it->second, expr)) {
        return substituteStructuralStackFacts(it->second, structural_stack_facts,
                                             depth + 1);
      }
    }
  }

  if (expr.operands.empty())
    return expr;

  VirtualValueExpr substituted = expr;
  substituted.operands.clear();
  substituted.operands.reserve(expr.operands.size());
  for (const auto &operand : expr.operands) {
    substituted.operands.push_back(
        substituteStructuralStackFacts(operand, structural_stack_facts,
                                       depth + 1));
  }
  return substituted;
}

}  // namespace

std::optional<unsigned> lookupMappedCallerSlotId(
    llvm::CallBase &call, const VirtualStateSlotInfo &callee_slot,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl) {
  if (auto arg_index = parseArgumentBaseName(callee_slot.base_name);
      arg_index && *arg_index < call.arg_size()) {
    auto actual_slot = extractStateSlotSummary(call.getArgOperand(*arg_index),
                                               callee_slot.width, dl);
    if (!actual_slot)
      return std::nullopt;

    VirtualStateSlotSummary mapped_slot = *actual_slot;
    mapped_slot.offset += callee_slot.offset;
    mapped_slot.width = callee_slot.width;

    auto it = slot_ids.find(slotKeyForSummary(mapped_slot));
    if (it == slot_ids.end())
      return std::nullopt;
    return it->second;
  }

  if (callee_slot.from_alloca) {
    return lookupMappedCallerSlotIdByPointerArgs(
        call, callee_slot.base_name, callee_slot.offset, callee_slot.width,
        slot_ids, dl);
  }

  return std::nullopt;
}

std::optional<unsigned> lookupMappedCallerStackCellId(
    llvm::CallBase &call, const VirtualStackCellInfo &callee_cell,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  if (callee_cell.base_from_argument) {
    if (auto arg_index = parseArgumentBaseName(callee_cell.base_name);
        arg_index && *arg_index < call.arg_size()) {
      auto actual_expr = summarizeValueExpr(call.getArgOperand(*arg_index), dl);
      if (auto actual_cell =
              extractStackCellSummaryFromExpr(actual_expr, callee_cell.width)) {
        VirtualStackCellSummary mapped_cell = *actual_cell;
        mapped_cell.base_offset += callee_cell.base_offset;
        mapped_cell.offset += callee_cell.cell_offset;
        mapped_cell.width = callee_cell.width;
        if (auto mapped_cell_id =
                lookupStackCellIdForSummary(mapped_cell, stack_cell_ids)) {
          return mapped_cell_id;
        }
      }
    }
  }

  if (callee_cell.base_from_alloca) {
    if (auto mapped = lookupMappedCallerStackCellIdByPointerArgs(
            call, callee_cell.base_name, callee_cell.base_offset,
            callee_cell.base_width, callee_cell.cell_offset, callee_cell.width,
            slot_ids, stack_cell_ids, dl)) {
      return mapped;
    }
  }

  VirtualStateSlotInfo base_slot_info{callee_cell.base_slot_id,
                                      callee_cell.base_name,
                                      callee_cell.base_offset,
                                      callee_cell.base_width,
                                      callee_cell.base_from_argument,
                                      callee_cell.base_from_alloca,
                                      {}};
  auto mapped_base_slot =
      lookupMappedCallerSlotId(call, base_slot_info, slot_ids, dl);
  if (!mapped_base_slot)
    return std::nullopt;

  auto base_slot_it =
      std::find_if(slot_ids.begin(), slot_ids.end(), [&](const auto &entry) {
        return entry.second == *mapped_base_slot;
      });
  if (base_slot_it == slot_ids.end())
    return std::nullopt;

  auto it = stack_cell_ids.find(
      StackCellKey{base_slot_it->first, callee_cell.cell_offset, callee_cell.width});
  if (it != stack_cell_ids.end())
    return it->second;

  it = llvm::find_if(stack_cell_ids, [&](const auto &entry) {
    return entry.first.base_slot.tie() == base_slot_it->first.tie() &&
           entry.first.cell_offset == callee_cell.cell_offset;
  });
  if (it != stack_cell_ids.end())
    return it->second;

  return findEquivalentArgumentStackCellId(
      base_slot_it->first.offset, base_slot_it->first.width,
      base_slot_it->first.from_argument, base_slot_it->first.from_alloca,
      callee_cell.cell_offset, callee_cell.width, stack_cell_ids);
}

VirtualValueExpr remapCalleeExprToCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  if (expr.kind == VirtualExprKind::kArgument && expr.argument_index.has_value() &&
      *expr.argument_index < call.arg_size()) {
    auto actual_expr = summarizeValueExpr(call.getArgOperand(*expr.argument_index),
                                          dl);
    annotateExprSlots(actual_expr, slot_ids);
    annotateExprStackCells(actual_expr, stack_cell_ids, slot_ids);
    return actual_expr;
  }

  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value()) {
    auto info_it = slot_info.find(*expr.slot_id);
    if (info_it != slot_info.end()) {
      if (auto mapped_slot =
              lookupMappedCallerSlotId(call, *info_it->second, slot_ids, dl)) {
        VirtualValueExpr mapped = expr;
        mapped.slot_id = *mapped_slot;
        const auto &mapped_info = *slot_info.at(*mapped_slot);
        mapped.state_base_name = mapped_info.base_name;
        mapped.state_offset = mapped_info.offset;
        mapped.bit_width = mapped_info.width * 8;
        return mapped;
      }
    }
  }
  if (expr.kind == VirtualExprKind::kStateSlot) {
    if (auto mapped =
            remapStateSlotExprByShape(expr, call, slot_info, slot_ids, dl)) {
      return *mapped;
    }
  }

  if (expr.kind == VirtualExprKind::kStackCell && expr.stack_cell_id.has_value()) {
    auto info_it = stack_cell_info.find(*expr.stack_cell_id);
    if (info_it != stack_cell_info.end()) {
      if (auto mapped_cell = lookupMappedCallerStackCellId(
              call, *info_it->second, slot_ids, stack_cell_ids, dl)) {
        VirtualValueExpr mapped = expr;
        mapped.stack_cell_id = *mapped_cell;
        const auto &mapped_info = *stack_cell_info.at(*mapped_cell);
        mapped.slot_id = mapped_info.base_slot_id;
        mapped.state_base_name = mapped_info.base_name;
        mapped.state_offset = mapped_info.base_offset;
        mapped.stack_offset = mapped_info.cell_offset;
        mapped.bit_width = mapped_info.width * 8;
        return mapped;
      }
    }
  }
  if (expr.kind == VirtualExprKind::kStackCell) {
    if (auto mapped =
            remapStackCellExprByShape(expr, call, slot_info, stack_cell_info,
                                      slot_ids, stack_cell_ids, dl)) {
      return *mapped;
    }
  }

  VirtualValueExpr remapped = expr;
  remapped.operands.clear();
  for (const auto &operand : expr.operands) {
    remapped.operands.push_back(remapCalleeExprToCaller(
        operand, call, slot_info, stack_cell_info, slot_ids, stack_cell_ids,
        dl));
  }
  return remapped;
}

std::optional<StackCellKey> remapCalleeStructuralStackKeyToCaller(
    const StackCellKey &key, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  VirtualStackCellSummary cell;
  cell.base_name = key.base_slot.base_name;
  cell.base_offset = key.base_slot.offset;
  cell.base_width = key.base_slot.width;
  cell.base_from_argument = key.base_slot.from_argument;
  cell.base_from_alloca = key.base_slot.from_alloca;
  cell.offset = key.cell_offset;
  cell.width = key.width;

  auto remapped = remapCalleeExprToCaller(stackCellExpr(cell), call, slot_info,
                                          stack_cell_info, slot_ids,
                                          stack_cell_ids, dl);
  annotateExprSlots(remapped, slot_ids);
  annotateExprStackCells(remapped, stack_cell_ids, slot_ids);
  return extractStackCellKeyFromExpr(remapped);
}

std::optional<VirtualValueExpr> normalizeImportedExprForCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  auto remapped = remapCalleeExprToCaller(expr, call, slot_info, stack_cell_info,
                                          slot_ids, stack_cell_ids, dl);
  annotateExprSlots(remapped, slot_ids);
  annotateExprStackCells(remapped, stack_cell_ids, slot_ids);
  remapped = substituteStructuralStackFacts(remapped,
                                            caller_structural_outgoing_stack);
  annotateExprSlots(remapped, slot_ids);
  annotateExprStackCells(remapped, stack_cell_ids, slot_ids);

  auto specialized = specializeExpr(remapped, caller_outgoing,
                                    &caller_outgoing_stack,
                                    &caller_argument_map);
  specialized = substituteStructuralStackFacts(
      specialized, caller_structural_outgoing_stack);
  annotateExprSlots(specialized, slot_ids);
  annotateExprStackCells(specialized, stack_cell_ids, slot_ids);
  specialized = specializeExpr(specialized, caller_outgoing,
                               &caller_outgoing_stack,
                               &caller_argument_map);
  annotateExprSlots(specialized, slot_ids);
  annotateExprStackCells(specialized, stack_cell_ids, slot_ids);

  if (containsInvalidCallerArgumentRelativeState(specialized,
                                                 *call.getFunction())) {
    vmModelImportDebugLog("unmapped-import call=" +
                          call.getCalledFunction()->getName().str() +
                          " expr=" + renderVirtualValueExpr(expr) +
                          " remapped=" + renderVirtualValueExpr(remapped) +
                          " specialized=" +
                          renderVirtualValueExpr(specialized));
    return std::nullopt;
  }

  if ((isUnknownLikeExpr(specialized) ||
       !isBoundedStateProvenanceExpr(specialized)) &&
      isBoundedStateProvenanceExpr(remapped)) {
    return remapped;
  }

  return specialized;
}

std::optional<VirtualValueExpr> normalizeLocalizedExprForCaller(
    const VirtualValueExpr &expr, const llvm::Function &caller_fn,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  VirtualValueExpr normalized = expr;
  annotateExprSlots(normalized, slot_ids);
  annotateExprStackCells(normalized, stack_cell_ids, slot_ids);
  normalized = substituteStructuralStackFacts(normalized,
                                              caller_structural_outgoing_stack);
  annotateExprSlots(normalized, slot_ids);
  annotateExprStackCells(normalized, stack_cell_ids, slot_ids);
  normalized = specializeExpr(normalized, caller_outgoing,
                              &caller_outgoing_stack, &caller_argument_map);
  normalized = substituteStructuralStackFacts(normalized,
                                              caller_structural_outgoing_stack);
  annotateExprSlots(normalized, slot_ids);
  annotateExprStackCells(normalized, stack_cell_ids, slot_ids);
  if (containsInvalidCallerArgumentRelativeState(normalized, caller_fn))
    return std::nullopt;
  return normalized;
}

}  // namespace omill::virtual_model::detail

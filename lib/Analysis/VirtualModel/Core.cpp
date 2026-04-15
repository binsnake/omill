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

static unsigned parseEnvUnsigned(const char *name, unsigned default_val) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return default_val;
  char *end = nullptr;
  unsigned long parsed = std::strtoul(v, &end, 10);
  return (end && *end == '\0') ? static_cast<unsigned>(parsed) : default_val;
}

VirtualModelConfig VirtualModelConfig::fromEnvironment() {
  VirtualModelConfig c;
  c.max_transfer_depth = parseEnvUnsigned("OMILL_VM_TRANSFER_DEPTH", 6);
  c.max_symbolic_refs = parseEnvUnsigned("OMILL_VM_SYMBOLIC_REFS", 4);
  c.max_stack_cells = parseEnvUnsigned("OMILL_VM_STACK_CELLS", 32);
  c.max_target_depth = parseEnvUnsigned("OMILL_VM_TARGET_DEPTH", 4);
  c.max_target_count = parseEnvUnsigned("OMILL_VM_TARGET_COUNT", 4);
  c.max_total_expr_nodes = parseEnvUnsigned("OMILL_VM_MAX_EXPR_NODES", 128);
  return c;
}

const VirtualModelConfig &vmModelConfig() {
  static const VirtualModelConfig config = VirtualModelConfig::fromEnvironment();
  return config;
}

bool isCallSiteHelper(const llvm::Function &F) {
  return F.getName().contains("CALLI");
}

static std::optional<uint64_t> evaluateVirtualExprImpl(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    llvm::SmallDenseSet<unsigned, 8> &visiting_slots,
    llvm::SmallDenseSet<unsigned, 8> &visiting_cells,
    const BinaryMemoryMap *binary_memory = nullptr) {
  auto lookup_slot = [&](unsigned slot_id) -> std::optional<uint64_t> {
    auto it = std::find_if(facts.begin(), facts.end(),
                           [&](const VirtualSlotFact &fact) {
                             return fact.slot_id == slot_id;
                           });
    if (it == facts.end())
      return std::nullopt;
    if (!visiting_slots.insert(slot_id).second)
      return std::nullopt;
    auto value = evaluateVirtualExprImpl(it->value, facts, stack_facts,
                                         visiting_slots, visiting_cells,
                                         binary_memory);
    visiting_slots.erase(slot_id);
    return value;
  };

  auto lookup_stack = [&](unsigned cell_id) -> std::optional<uint64_t> {
    auto it = std::find_if(stack_facts.begin(), stack_facts.end(),
                           [&](const VirtualStackFact &fact) {
                             return fact.cell_id == cell_id;
                           });
    if (it == stack_facts.end())
      return std::nullopt;
    if (!visiting_cells.insert(cell_id).second)
      return std::nullopt;
    auto value = evaluateVirtualExprImpl(it->value, facts, stack_facts,
                                         visiting_slots, visiting_cells,
                                         binary_memory);
    visiting_cells.erase(cell_id);
    return value;
  };

  auto fold_binary = [&](auto fn) -> std::optional<uint64_t> {
    if (expr.operands.size() != 2)
      return std::nullopt;
    auto lhs = evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                       visiting_slots, visiting_cells,
                                       binary_memory);
    auto rhs = evaluateVirtualExprImpl(expr.operands[1], facts, stack_facts,
                                       visiting_slots, visiting_cells,
                                       binary_memory);
    if (!lhs || !rhs)
      return std::nullopt;
    return fn(*lhs, *rhs);
  };

  auto fold_unary = [&](auto fn) -> std::optional<uint64_t> {
    if (expr.operands.size() != 1)
      return std::nullopt;
    auto value = evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                         visiting_slots, visiting_cells,
                                         binary_memory);
    if (!value)
      return std::nullopt;
    return fn(*value);
  };

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
      return expr.constant;
    case VirtualExprKind::kStateSlot:
      if (expr.slot_id.has_value())
        return lookup_slot(*expr.slot_id);
      return std::nullopt;
    case VirtualExprKind::kStackCell:
      if (expr.stack_cell_id.has_value())
        return lookup_stack(*expr.stack_cell_id);
      return std::nullopt;
    case VirtualExprKind::kMemoryRead:
      if (!binary_memory || expr.operands.size() != 1)
        return std::nullopt;
      if (auto addr = evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                              visiting_slots, visiting_cells,
                                              binary_memory)) {
        if (auto value = readBinaryConstantExpr(*binary_memory, *addr,
                                                expr.bit_width)) {
          return value->constant;
        }
      }
      return std::nullopt;
    case VirtualExprKind::kZExt:
      return fold_unary([&](uint64_t value) {
        unsigned source_bits = expr.operands.front().bit_width
                                   ? expr.operands.front().bit_width
                                   : expr.bit_width;
        return value & bitMask(std::min(source_bits, expr.bit_width));
      });
    case VirtualExprKind::kSExt:
      return fold_unary([&](uint64_t value) {
        unsigned source_bits = expr.operands.front().bit_width
                                   ? expr.operands.front().bit_width
                                   : expr.bit_width;
        return signExtendBits(value, source_bits) & bitMask(expr.bit_width);
      });
    case VirtualExprKind::kTrunc:
      return fold_unary([&](uint64_t value) {
        return value & bitMask(expr.bit_width);
      });
    case VirtualExprKind::kAdd:
      return fold_binary([](uint64_t a, uint64_t b) { return a + b; });
    case VirtualExprKind::kSub:
      return fold_binary([](uint64_t a, uint64_t b) { return a - b; });
    case VirtualExprKind::kMul:
      return fold_binary([](uint64_t a, uint64_t b) { return a * b; });
    case VirtualExprKind::kXor:
      return fold_binary([](uint64_t a, uint64_t b) { return a ^ b; });
    case VirtualExprKind::kAnd:
      return fold_binary([](uint64_t a, uint64_t b) { return a & b; });
    case VirtualExprKind::kOr:
      return fold_binary([](uint64_t a, uint64_t b) { return a | b; });
    case VirtualExprKind::kShl:
      return fold_binary([](uint64_t a, uint64_t b) {
        return b < 64 ? (a << b) : 0ULL;
      });
    case VirtualExprKind::kLShr:
      return fold_binary([](uint64_t a, uint64_t b) {
        return b < 64 ? (a >> b) : 0ULL;
      });
    case VirtualExprKind::kAShr:
      return fold_binary([](uint64_t a, uint64_t b) {
        if (b >= 64)
          return (a & (1ULL << 63)) ? ~0ULL : 0ULL;
        return static_cast<uint64_t>(static_cast<int64_t>(a) >>
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kEq:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a == b);
      });
    case VirtualExprKind::kNe:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a != b);
      });
    case VirtualExprKind::kUlt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a < b);
      });
    case VirtualExprKind::kUle:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a <= b);
      });
    case VirtualExprKind::kUgt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a > b);
      });
    case VirtualExprKind::kUge:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a >= b);
      });
    case VirtualExprKind::kSlt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) <
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSle:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) <=
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSgt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) >
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSge:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) >=
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSelect:
      if (expr.operands.size() != 3)
        return std::nullopt;
      if (auto cond =
              evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                      visiting_slots, visiting_cells,
                                      binary_memory)) {
        return evaluateVirtualExprImpl(expr.operands[*cond ? 1 : 2], facts,
                                       stack_facts, visiting_slots,
                                       visiting_cells, binary_memory);
      }
      return std::nullopt;
    case VirtualExprKind::kPhi:
      if (expr.operands.empty())
        return std::nullopt;
      {
        auto first =
            evaluateVirtualExprImpl(expr.operands.front(), facts, stack_facts,
                                    visiting_slots, visiting_cells,
                                    binary_memory);
        if (!first)
          return std::nullopt;
        for (size_t i = 1; i < expr.operands.size(); ++i) {
          auto other = evaluateVirtualExprImpl(expr.operands[i], facts,
                                               stack_facts, visiting_slots,
                                               visiting_cells, binary_memory);
          if (!other || *other != *first)
            return std::nullopt;
        }
        return first;
      }
    case VirtualExprKind::kUnknown:
    case VirtualExprKind::kArgument:
      return std::nullopt;
  }

  return std::nullopt;
}

std::optional<uint64_t> evaluateVirtualExpr(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    const BinaryMemoryMap *binary_memory) {
  llvm::SmallDenseSet<unsigned, 8> visiting_slots;
  llvm::SmallDenseSet<unsigned, 8> visiting_cells;
  return evaluateVirtualExprImpl(expr, facts, stack_facts, visiting_slots,
                                 visiting_cells, binary_memory);
}



static SlotKey slotKeyForExpr(const VirtualValueExpr &expr) {
  auto base_name = expr.state_base_name.value_or("state");
  bool from_argument = base_name.rfind("arg", 0) == 0;
  unsigned width_bytes = expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 0u;
  return SlotKey{expr.state_base_name.value_or("state"),
                 expr.state_offset.value_or(0), width_bytes,
                 from_argument, !from_argument};
}

void annotateExprSlots(VirtualValueExpr &expr,
                       const std::map<SlotKey, unsigned> &slot_ids) {
  if (expr.kind == VirtualExprKind::kStateSlot) {
    auto it = slot_ids.find(slotKeyForExpr(expr));
    if (it != slot_ids.end())
      expr.slot_id = it->second;
  }
  for (auto &operand : expr.operands)
    annotateExprSlots(operand, slot_ids);
}

void annotateExprStackCells(
    VirtualValueExpr &expr,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<SlotKey, unsigned> &slot_ids) {
  if (expr.kind == VirtualExprKind::kStackCell && expr.state_base_name.has_value() &&
      expr.state_offset.has_value() && expr.stack_offset.has_value()) {
    llvm::StringRef base_name = *expr.state_base_name;
    bool from_argument = base_name.starts_with("arg");
    auto base_slot_key =
        SlotKey{*expr.state_base_name, *expr.state_offset,
                expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u,
                from_argument,
                !from_argument};
    auto cell_key = StackCellKey{base_slot_key, *expr.stack_offset,
                                 expr.bit_width ? std::max(1u, expr.bit_width / 8u)
                                                : 8u};
    auto cell_it = stack_cell_ids.find(cell_key);
    if (cell_it == stack_cell_ids.end()) {
      cell_it = llvm::find_if(stack_cell_ids, [&](const auto &entry) {
        return entry.first.base_slot.base_name == base_slot_key.base_name &&
               entry.first.base_slot.offset == base_slot_key.offset &&
               entry.first.base_slot.from_argument ==
                   base_slot_key.from_argument &&
               entry.first.base_slot.from_alloca ==
                   base_slot_key.from_alloca &&
               entry.first.cell_offset == *expr.stack_offset;
      });
    }
    if (cell_it != stack_cell_ids.end()) {
      expr.stack_cell_id = cell_it->second;
    } else if (auto fallback_cell_id = findEquivalentArgumentStackCellId(
                   base_slot_key.offset, base_slot_key.width,
                   base_slot_key.from_argument, base_slot_key.from_alloca,
                   *expr.stack_offset,
                   expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u,
                   stack_cell_ids)) {
      expr.stack_cell_id = *fallback_cell_id;
    }
    auto slot_it = slot_ids.find(base_slot_key);
    if (slot_it != slot_ids.end())
      expr.slot_id = slot_it->second;
  }
  for (auto &operand : expr.operands)
    annotateExprStackCells(operand, stack_cell_ids, slot_ids);
}

void canonicalizeMemoryReadsToStackCells(
    VirtualValueExpr &expr, const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<SlotKey, unsigned> &slot_ids) {
  for (auto &operand : expr.operands)
    canonicalizeMemoryReadsToStackCells(operand, stack_cell_ids, slot_ids);

  if (expr.kind != VirtualExprKind::kMemoryRead || expr.operands.size() != 1)
    return;

  unsigned width_bytes =
      expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u;
  auto cell =
      extractStackCellSummaryFromExpr(expr.operands.front(), width_bytes);
  if (!cell)
    return;

  VirtualValueExpr replacement;
  replacement.kind = VirtualExprKind::kStackCell;
  replacement.bit_width = cell->width ? cell->width * 8u : 0u;
  replacement.complete = true;
  replacement.state_base_name = cell->base_name;
  replacement.state_offset = cell->base_offset;
  replacement.stack_offset = cell->offset;
  replacement.slot_id = cell->canonical_base_slot_id;
  replacement.stack_cell_id = cell->canonical_id;
  annotateExprSlots(replacement, slot_ids);
  annotateExprStackCells(replacement, stack_cell_ids, slot_ids);
  if (replacement.stack_cell_id.has_value())
    expr = std::move(replacement);
}

bool exprEquals(const VirtualValueExpr &lhs, const VirtualValueExpr &rhs) {
  if (lhs.kind != rhs.kind || lhs.bit_width != rhs.bit_width ||
      lhs.complete != rhs.complete || lhs.constant != rhs.constant ||
      lhs.argument_index != rhs.argument_index || lhs.slot_id != rhs.slot_id ||
      lhs.state_base_name != rhs.state_base_name ||
      lhs.state_offset != rhs.state_offset ||
      lhs.stack_cell_id != rhs.stack_cell_id ||
      lhs.stack_offset != rhs.stack_offset ||
      lhs.operands.size() != rhs.operands.size()) {
    return false;
  }

  for (size_t i = 0; i < lhs.operands.size(); ++i) {
    if (!exprEquals(lhs.operands[i], rhs.operands[i]))
      return false;
  }
  return true;
}


bool isUnknownLikeExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kUnknown)
    return true;
  if (expr.kind != VirtualExprKind::kPhi || expr.operands.empty())
    return false;
  return llvm::all_of(expr.operands, isUnknownLikeExpr);
}

bool containsStateSlotExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kStateSlot)
    return true;
  return llvm::any_of(expr.operands, containsStateSlotExpr);
}

bool containsStackCellExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kStackCell)
    return true;
  return llvm::any_of(expr.operands, containsStackCellExpr);
}

bool containsMemoryReadExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kMemoryRead)
    return true;
  return llvm::any_of(expr.operands, containsMemoryReadExpr);
}

unsigned exprByteWidth(const VirtualValueExpr &expr, unsigned fallback) {
  return expr.bit_width ? std::max(1u, expr.bit_width / 8u) : fallback;
}

unsigned countSymbolicRefs(const VirtualValueExpr &expr) {
  unsigned refs =
      (expr.kind == VirtualExprKind::kStateSlot ||
       expr.kind == VirtualExprKind::kStackCell ||
       expr.kind == VirtualExprKind::kArgument)
          ? 1u
          : 0u;
  for (const auto &operand : expr.operands)
    refs += countSymbolicRefs(operand);
  return refs;
}

bool isBoundedStateProvenanceExpr(const VirtualValueExpr &expr,
                                  unsigned depth) {
  return isSimpleRemappableFactExpr(expr, depth);
}

VirtualValueExpr unknownExpr(unsigned bits) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kUnknown;
  expr.bit_width = bits;
  expr.complete = false;
  return expr;
}

std::optional<EntryPreludeCallInfo> detectEntryPreludeDirectCall(
    const BinaryMemoryMap &binary_memory, uint64_t entry_va) {
  if (entry_va < 5)
    return std::nullopt;

  uint8_t bytes[5] = {};
  auto call_pc = entry_va - 5;
  if (!binary_memory.read(call_pc, bytes, sizeof(bytes)) || bytes[0] != 0xE8)
    return std::nullopt;

  int32_t rel = 0;
  std::memcpy(&rel, bytes + 1, sizeof(rel));

  auto continuation_pc = call_pc + 5;
  auto target_pc = static_cast<uint64_t>(
      static_cast<int64_t>(continuation_pc) + static_cast<int64_t>(rel));
  if (continuation_pc != entry_va || target_pc == 0)
    return std::nullopt;

  return EntryPreludeCallInfo{call_pc, target_pc, continuation_pc};
}

std::optional<VirtualValueExpr> mergeIncomingExpr(
    const VirtualValueExpr &existing, const VirtualValueExpr &incoming) {
  if (exprEquals(existing, incoming))
    return existing;

  if (existing.bit_width != 0 && incoming.bit_width != 0 &&
      existing.bit_width != incoming.bit_width) {
    return std::nullopt;
  }

  llvm::SmallVector<VirtualValueExpr, 4> choices;
  auto append_unique = [&](const VirtualValueExpr &expr) {
    for (const auto &choice : choices) {
      if (exprEquals(choice, expr))
        return;
    }
    choices.push_back(expr);
  };

  if (existing.kind == VirtualExprKind::kPhi) {
    for (const auto &operand : existing.operands)
      append_unique(operand);
  } else {
    append_unique(existing);
  }

  if (incoming.kind == VirtualExprKind::kPhi) {
    for (const auto &operand : incoming.operands)
      append_unique(operand);
  } else {
    append_unique(incoming);
  }

  if (choices.empty() || choices.size() > 4)
    return std::nullopt;

  VirtualValueExpr merged;
  merged.kind = VirtualExprKind::kPhi;
  merged.bit_width = existing.bit_width ? existing.bit_width : incoming.bit_width;
  merged.complete = std::all_of(
      choices.begin(), choices.end(),
      [](const VirtualValueExpr &choice) { return choice.complete; });
  merged.operands.assign(choices.begin(), choices.end());
  return merged;
}

}  // namespace omill::virtual_model::detail

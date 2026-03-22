#include "Analysis/VirtualModel/Internal.h"

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>

namespace omill::virtual_model::detail {

static constexpr unsigned kMaxLocalizedDirectCallees = 8;
static constexpr unsigned kMaxLocalizedLeafHelperInstructions = 64;
static constexpr unsigned kMaxLocalizedSingleBlockHandlerInstructions = 96;

std::optional<VirtualValueExpr> readBinaryConstantExpr(
    const BinaryMemoryMap &binary_memory, uint64_t addr, unsigned width_bits) {
  unsigned width_bytes = std::max(1u, width_bits / 8u);
  if (!binary_memory.isReadOnly(addr, width_bytes))
    return std::nullopt;

  auto value = binary_memory.readInt(addr, width_bytes);
  if (!value)
    return std::nullopt;

  auto reloc_kind =
      binary_memory.classifyRelocatedValue(addr, width_bytes, *value);
  if (reloc_kind == RelocValueKind::Suspicious &&
      binary_memory.isSuspiciousImageBase()) {
    return std::nullopt;
  }

  return constantExpr(*value, width_bits);
}

std::optional<llvm::SmallVector<llvm::BasicBlock *, 4>>
collectLocalizedReplayBlocks(llvm::Function &F,
                             const VirtualHandlerSummary &summary) {
  auto log_skip = [&](llvm::StringRef reason) {
    if (!vmModelLocalReplayDebugEnabled())
      return;
    unsigned total_instrs = 0;
    for (const auto &BB : F)
      total_instrs += static_cast<unsigned>(BB.size());
    vmModelLocalReplayDebugLog("skip-local-replay fn=" + F.getName().str() +
                               " reason=" + reason.str() + " blocks=" +
                               std::to_string(F.size()) + " instrs=" +
                               std::to_string(total_instrs));
  };

  if (F.empty()) {
    log_skip("empty");
    return std::nullopt;
  }
  if (!summary.callsites.empty()) {
    log_skip("callsites");
    return std::nullopt;
  }
  if (!summary.dispatches.empty()) {
    log_skip("dispatches");
    return std::nullopt;
  }
  if (summary.direct_callees.size() > kMaxLocalizedDirectCallees) {
    log_skip("too-many-direct-callees");
    return std::nullopt;
  }

  unsigned instruction_budget = summary.direct_callees.empty()
                                    ? kMaxLocalizedLeafHelperInstructions
                                    : kMaxLocalizedSingleBlockHandlerInstructions;
  unsigned instruction_count = 0;
  llvm::SmallVector<llvm::BasicBlock *, 4> blocks;
  llvm::SmallPtrSet<const llvm::BasicBlock *, 4> seen;
  auto *block = &F.getEntryBlock();

  while (block) {
    if (!seen.insert(block).second) {
      log_skip("cycle");
      return std::nullopt;
    }
    instruction_count += static_cast<unsigned>(block->size());
    if (instruction_count > instruction_budget) {
      log_skip("instruction-budget");
      return std::nullopt;
    }
    blocks.push_back(block);

    auto *term = block->getTerminator();
    if (!term) {
      log_skip("no-terminator");
      return std::nullopt;
    }
    if (llvm::isa<llvm::ReturnInst>(term) ||
        llvm::isa<llvm::UnreachableInst>(term)) {
      break;
    }

    auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
    if (!br || !br->isUnconditional()) {
      log_skip("nonlinear-terminator");
      return std::nullopt;
    }

    auto *next = br->getSuccessor(0);
    if (!next || !next->hasNPredecessors(1)) {
      log_skip("multi-predecessor");
      return std::nullopt;
    }
    block = next;
  }

  if (seen.size() != F.size()) {
    log_skip("unreached-blocks");
    return std::nullopt;
  }
  return blocks;
}

VirtualValueExpr stateSlotExpr(const VirtualStateSlotSummary &slot) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kStateSlot;
  expr.bit_width = slot.width ? slot.width * 8u : 0u;
  expr.complete = true;
  expr.state_base_name = slot.base_name;
  expr.state_offset = slot.offset;
  expr.slot_id = slot.canonical_id;
  return expr;
}

VirtualValueExpr stackCellExpr(const VirtualStackCellSummary &cell) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kStackCell;
  expr.bit_width = cell.width ? cell.width * 8u : 0u;
  expr.complete = true;
  expr.state_base_name = cell.base_name;
  expr.state_offset = cell.base_offset;
  expr.stack_offset = cell.offset;
  expr.slot_id = cell.canonical_base_slot_id;
  expr.stack_cell_id = cell.canonical_id;
  return expr;
}

bool canRecursivelyLocalizeCallsiteSummary(
    const VirtualHandlerSummary &summary, unsigned depth) {
  if (depth > kMaxCallsiteLocalizationDepth)
    return false;
  if (!summary.dispatches.empty())
    return false;
  return summary.direct_callees.size() <= kMaxLocalizedDirectCallees;
}

bool isCallerStateArgumentExpr(const VirtualValueExpr &expr) {
  return expr.kind == VirtualExprKind::kArgument &&
         expr.argument_index.has_value() && *expr.argument_index == 0;
}

bool canComputeLocalizedSingleBlockOutgoingFacts(
    const llvm::Function &F, const VirtualHandlerSummary &summary) {
  auto &mutable_function = const_cast<llvm::Function &>(F);
  return collectLocalizedReplayBlocks(mutable_function, summary).has_value();
}

std::optional<uint64_t> resolveSpecializedExprToConstant(
    const VirtualValueExpr &expr,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack) {
  if (expr.constant.has_value())
    return expr.constant;
  auto slot_facts = slotFactsForMap(caller_outgoing);
  auto stack_facts = stackFactsForMap(caller_outgoing_stack);
  return evaluateVirtualExpr(expr, slot_facts, stack_facts);
}

void seedCallContinuationStackCell(
    llvm::Module &M, uint64_t continuation_pc,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    std::map<unsigned, VirtualValueExpr> &callee_incoming_stack) {
  auto sp_offset = lookupNativeStackPointerOffset(M);
  if (!sp_offset)
    return;

  for (const auto &[cell_id, cell] : stack_cell_info) {
    if (!cell->base_from_argument || cell->base_from_alloca)
      continue;
    auto arg_index = parseArgumentBaseName(cell->base_name);
    if (!arg_index || *arg_index != 0)
      continue;
    if (cell->base_offset != static_cast<int64_t>(*sp_offset) ||
        cell->cell_offset != 0) {
      continue;
    }
    callee_incoming_stack[cell_id] =
        constantExpr(continuation_pc, cell->width * 8);
  }
}

void seedLiftedCallContinuationStackCell(
    llvm::CallBase &call, const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    std::map<unsigned, VirtualValueExpr> &callee_incoming_stack) {
  (void) callee_summary;
  auto continuation_pc = inferLiftedCallContinuationPc(call);
  if (!continuation_pc)
    return;

  auto *module = call.getModule();
  if (!module)
    return;
  seedCallContinuationStackCell(*module, *continuation_pc, stack_cell_info,
                                callee_incoming_stack);
}

}  // namespace omill::virtual_model::detail

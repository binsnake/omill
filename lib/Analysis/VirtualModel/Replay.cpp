#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <functional>
#include <set>
#include <string>

namespace omill::virtual_model::detail {

namespace {

static bool isNestedCodeBearingReplayFunction(const llvm::Function &F,
                                              unsigned depth) {
  if (depth <= 1)
    return false;
  auto name = F.getName();
  return name.starts_with("sub_") || name.starts_with("blk_") ||
         name.starts_with("block_");
}

}  // namespace

std::optional<CallsiteLocalizedOutgoingFacts> computeLocalizedSingleBlockOutgoingFacts(
    llvm::Function &F, const VirtualMachineModel &model,
    const VirtualHandlerSummary &summary,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &incoming_slots,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &incoming_args,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const BinaryMemoryMap &binary_memory,
    unsigned depth, llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    llvm::CallBase *localizing_call,
    const std::map<unsigned, VirtualValueExpr> *caller_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *caller_slot_facts,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts,
    LocalizedReplayCacheState *localized_replay_cache) {
  (void) summary;
  (void) localized_replay_cache;
  auto replay_blocks = collectLocalizedReplayBlocks(F, summary);
  if (!replay_blocks)
    return std::nullopt;

  const auto &dl = F.getParent()->getDataLayout();
  const auto native_sp_offset = lookupNativeStackPointerOffset(*F.getParent());
  const auto slot_info = buildSlotInfoMap(model);
  const auto stack_cell_info = buildStackCellInfoMap(model);
  struct LocalLeafReplayState {
    std::map<unsigned, VirtualValueExpr> slot_facts;
    std::map<unsigned, VirtualValueExpr> stack_facts;
    std::map<StackCellKey, VirtualValueExpr> structural_stack_facts;
    llvm::DenseMap<const llvm::Value *, VirtualValueExpr> value_facts;
  };

  LocalLeafReplayState state;
  state.slot_facts = incoming_slots;
  state.stack_facts = incoming_stack;
  if (caller_slot_facts) {
    for (const auto &[slot_id, value] : *caller_slot_facts) {
      auto info_it = slot_info.find(slot_id);
      if (info_it == slot_info.end() || !info_it->second->from_argument ||
          !isBoundedLocalizedTransferExpr(value)) {
        continue;
      }
      state.slot_facts.try_emplace(slot_id, value);
    }
  }
  if (caller_stack_facts) {
    for (const auto &[cell_id, value] : *caller_stack_facts) {
      auto info_it = stack_cell_info.find(cell_id);
      if (info_it == stack_cell_info.end() ||
          !info_it->second->base_from_argument ||
          !isBoundedLocalizedTransferExpr(value)) {
        continue;
      }
      state.stack_facts.try_emplace(cell_id, value);
    }
  }
  if (fallback_caller_slot_facts) {
    for (const auto &[slot_id, value] : *fallback_caller_slot_facts) {
      auto info_it = slot_info.find(slot_id);
      if (info_it == slot_info.end() || !info_it->second->from_argument ||
          !isBoundedLocalizedTransferExpr(value)) {
        continue;
      }
      state.slot_facts.try_emplace(slot_id, value);
    }
  }
  if (fallback_caller_stack_facts) {
    for (const auto &[cell_id, value] : *fallback_caller_stack_facts) {
      auto info_it = stack_cell_info.find(cell_id);
      if (info_it == stack_cell_info.end() ||
          !info_it->second->base_from_argument ||
          !isBoundedLocalizedTransferExpr(value)) {
        continue;
      }
      state.stack_facts.try_emplace(cell_id, value);
    }
  }
  if (caller_structural_stack_facts) {
    for (const auto &[key, value] : *caller_structural_stack_facts) {
      if (isBoundedLocalizedTransferExpr(value))
        state.structural_stack_facts.try_emplace(key, value);
    }
  }
  if (fallback_caller_structural_stack_facts) {
    for (const auto &[key, value] : *fallback_caller_structural_stack_facts) {
      if (isBoundedLocalizedTransferExpr(value))
        state.structural_stack_facts.try_emplace(key, value);
    }
  }
  std::set<unsigned> localized_written_slot_ids;
  std::set<unsigned> localized_written_stack_cell_ids;
  std::set<StackCellKey> localized_written_structural_stack_keys;
  auto normalize_expr = [&](VirtualValueExpr expr,
                            unsigned fallback_bits = 0u) {
    if (!expr.bit_width)
      expr.bit_width = fallback_bits;
    annotateExprSlots(expr, slot_ids);
    annotateExprStackCells(expr, stack_cell_ids, slot_ids);
    expr = specializeExprToFixpoint(expr, state.slot_facts, &state.stack_facts,
                                    &incoming_args, slot_ids,
                                    stack_cell_ids);
    annotateExprSlots(expr, slot_ids);
    annotateExprStackCells(expr, stack_cell_ids, slot_ids);
    if (!expr.bit_width)
      expr.bit_width = fallback_bits;
    return expr;
  };
  auto canonicalize_slot = [&](VirtualStateSlotSummary slot) {
    slot.canonical_id = lookupSlotIdForSummary(slot, slot_ids);
    return slot;
  };
  auto canonicalize_cell = [&](VirtualStackCellSummary cell) {
    cell.canonical_id = lookupStackCellIdForSummary(cell, stack_cell_ids);
    VirtualStateSlotSummary base_slot;
    base_slot.base_name = cell.base_name;
    base_slot.offset = cell.base_offset;
    base_slot.width = cell.base_width;
    base_slot.from_argument = cell.base_from_argument;
    base_slot.from_alloca = cell.base_from_alloca;
    cell.canonical_base_slot_id = lookupSlotIdForSummary(base_slot, slot_ids);
    return cell;
  };
  auto seed_structural_from_canonical_map =
      [&](const std::map<unsigned, VirtualValueExpr> &stack_facts) {
        for (const auto &[cell_id, value] : stack_facts) {
          auto info_it = stack_cell_info.find(cell_id);
          if (info_it == stack_cell_info.end())
            continue;
          VirtualStackCellSummary summary;
          summary.base_name = info_it->second->base_name;
          summary.base_offset = info_it->second->base_offset;
          summary.base_width = info_it->second->base_width;
          summary.base_from_argument = info_it->second->base_from_argument;
          summary.base_from_alloca = info_it->second->base_from_alloca;
          summary.offset = info_it->second->cell_offset;
          summary.width = info_it->second->width;
          state.structural_stack_facts.try_emplace(stackCellKeyForSummary(summary),
                                                   value);
        }
      };
  seed_structural_from_canonical_map(state.stack_facts);
  auto render_update = [&](llvm::StringRef kind, unsigned id,
                           const VirtualValueExpr &value) {
    std::string rendered;
    llvm::raw_string_ostream os(rendered);
    os << kind << "[" << id << "] = " << renderVirtualValueExpr(value);
    return os.str();
  };
  auto render_structural_update = [&](const VirtualStackCellSummary &cell,
                                      const VirtualValueExpr &value) {
    return renderVirtualValueExpr(stackCellExpr(cell)) + " = " +
           renderVirtualValueExpr(value);
  };
  auto log_stack_lookup = [&](llvm::StringRef source,
                              const VirtualStackCellSummary &cell,
                              std::optional<unsigned> direct_id,
                              std::optional<unsigned> rebased_id,
                              bool local_hit, bool rebased_hit,
                              bool caller_hit) {
    if (!vmModelLocalReplayDebugEnabled())
      return;
    std::string rendered;
    llvm::raw_string_ostream os(rendered);
    os << "helper=" << F.getName() << " " << source << " base=" << cell.base_name
       << "+" << cell.base_offset
       << " cell_off=" << cell.offset << " direct=";
    if (direct_id)
      os << *direct_id;
    else
      os << "none";
    if (direct_id) {
      auto it = llvm::find_if(model.stackCells(), [&](const auto &info) {
        return info.id == *direct_id;
      });
      if (it != model.stackCells().end())
        os << "(" << it->base_name << "+" << it->base_offset << ","
           << it->cell_offset << ")";
    }
    os << " rebased=";
    if (rebased_id)
      os << *rebased_id;
    else
      os << "none";
    if (rebased_id) {
      auto it = llvm::find_if(model.stackCells(), [&](const auto &info) {
        return info.id == *rebased_id;
      });
      if (it != model.stackCells().end())
        os << "(" << it->base_name << "+" << it->base_offset << ","
           << it->cell_offset << ")";
    }
    os << " local_hit=" << local_hit << " rebased_hit=" << rebased_hit
       << " caller_hit=" << caller_hit;
    vmModelLocalReplayDebugLog(os.str());
  };
  auto lookup_caller_stack_fact =
      [&](const VirtualStackCellSummary &cell) -> std::optional<VirtualValueExpr> {
    if (!caller_stack_facts && !fallback_caller_stack_facts &&
        !caller_structural_stack_facts &&
        !fallback_caller_structural_stack_facts)
      return std::nullopt;

    auto lookup_equivalent_caller_fact =
        [&](const std::map<unsigned, VirtualValueExpr> *stack_facts,
            const VirtualStackCellSummary &query)
            -> std::optional<VirtualValueExpr> {
      if (!stack_facts)
        return std::nullopt;
      std::optional<VirtualValueExpr> found;
      for (const auto &candidate : model.stackCells()) {
        if (candidate.base_offset != query.base_offset ||
            candidate.base_width != query.base_width ||
            candidate.cell_offset != query.offset ||
            candidate.width != query.width ||
            candidate.base_from_argument != query.base_from_argument ||
            candidate.base_from_alloca != query.base_from_alloca) {
          continue;
        }
        if (!query.base_from_argument && candidate.base_name != query.base_name)
          continue;
        auto it = stack_facts->find(candidate.id);
        if (it == stack_facts->end())
          continue;
        if (!found) {
          found = it->second;
          continue;
        }
        if (!exprEquals(*found, it->second))
          return std::nullopt;
      }
      return found;
    };
    auto lookup_structural_stack_fact =
        [&](const std::map<StackCellKey, VirtualValueExpr> *stack_facts,
            const VirtualStackCellSummary &query)
            -> std::optional<VirtualValueExpr> {
      if (!stack_facts)
        return std::nullopt;
      auto it = stack_facts->find(stackCellKeyForSummary(query));
      if (it == stack_facts->end())
        return std::nullopt;
      return it->second;
    };
    auto stack_cell_summary_for_id =
        [&](unsigned cell_id) -> std::optional<VirtualStackCellSummary> {
      auto it = llvm::find_if(model.stackCells(), [&](const auto &info) {
        return info.id == cell_id;
      });
      if (it == model.stackCells().end())
        return std::nullopt;
      VirtualStackCellSummary summary;
      summary.base_name = it->base_name;
      summary.base_offset = it->base_offset;
      summary.base_width = it->base_width;
      summary.base_from_argument = it->base_from_argument;
      summary.base_from_alloca = it->base_from_alloca;
      summary.offset = it->cell_offset;
      summary.width = it->width;
      summary.canonical_id = cell_id;
      return summary;
    };
    auto lookup_canonical_or_equivalent_caller_fact =
        [&](const std::map<unsigned, VirtualValueExpr> *stack_facts,
            const VirtualStackCellSummary &query)
            -> std::optional<VirtualValueExpr> {
      if (!stack_facts)
        return std::nullopt;
      auto canonical_query = canonicalize_cell(query);
      if (canonical_query.canonical_id.has_value()) {
        unsigned direct_id = *canonical_query.canonical_id;
        if (auto it = stack_facts->find(direct_id); it != stack_facts->end()) {
          return it->second;
        }
      }
      return lookup_equivalent_caller_fact(stack_facts, canonical_query);
    };
    auto lookup_rebased_caller_fact =
        [&](const std::map<unsigned, VirtualValueExpr> *stack_facts,
            const VirtualStackCellSummary &query,
            const std::map<unsigned, VirtualValueExpr> &slot_facts)
            -> std::optional<VirtualValueExpr> {
      if (!stack_facts)
        return std::nullopt;
      auto canonical_query = canonicalize_cell(query);
      if (!canonical_query.canonical_id.has_value())
        return std::nullopt;
      unsigned direct_id = *canonical_query.canonical_id;
      unsigned rebased_id = rebaseSingleStackCellId(model, slot_facts, direct_id);
      if (rebased_id == direct_id)
        return std::nullopt;
      if (auto it = stack_facts->find(rebased_id); it != stack_facts->end()) {
        return it->second;
      }
      if (auto rebased_cell = stack_cell_summary_for_id(rebased_id))
        return lookup_equivalent_caller_fact(stack_facts, *rebased_cell);
      return std::nullopt;
    };
    auto lookup_from_caller_sources =
        [&](const VirtualStackCellSummary &query)
            -> std::optional<VirtualValueExpr> {
      if (auto direct =
              lookup_canonical_or_equivalent_caller_fact(caller_stack_facts,
                                                         query)) {
        return direct;
      }
      if (auto direct =
              lookup_structural_stack_fact(caller_structural_stack_facts,
                                           query)) {
        return direct;
      }
      if (auto rebased = lookup_rebased_caller_fact(caller_stack_facts, query,
                                                    state.slot_facts)) {
        return rebased;
      }
      if (caller_slot_facts)
        if (auto rebased = lookup_rebased_caller_fact(caller_stack_facts, query,
                                                      *caller_slot_facts)) {
          return rebased;
        }
      if (auto direct =
              lookup_canonical_or_equivalent_caller_fact(
                  fallback_caller_stack_facts, query)) {
        return direct;
      }
      if (auto direct = lookup_structural_stack_fact(
              fallback_caller_structural_stack_facts, query)) {
        return direct;
      }
      if (auto rebased = lookup_rebased_caller_fact(
              fallback_caller_stack_facts, query, state.slot_facts)) {
        return rebased;
      }
      if (fallback_caller_slot_facts)
        if (auto rebased = lookup_rebased_caller_fact(
                fallback_caller_stack_facts, query,
                *fallback_caller_slot_facts)) {
          return rebased;
        }
      return std::nullopt;
    };

    if (auto direct = lookup_from_caller_sources(cell))
      return direct;

    if (!localizing_call || !cell.base_from_argument)
      return std::nullopt;

    auto arg_index = parseArgumentBaseName(cell.base_name);
    if (!arg_index || *arg_index >= localizing_call->arg_size())
      return std::nullopt;

    auto *actual_arg = localizing_call->getArgOperand(*arg_index);
    VirtualStackCellSummary mapped_cell = cell;
    if (auto actual_slot =
            extractStateSlotSummary(actual_arg, cell.base_width, dl)) {
      mapped_cell.base_name = actual_slot->base_name;
      mapped_cell.base_offset += actual_slot->offset;
      mapped_cell.base_width = actual_slot->width;
      mapped_cell.base_from_argument = actual_slot->from_argument;
      mapped_cell.base_from_alloca = actual_slot->from_alloca;
    } else {
      auto actual_expr = summarizeValueExpr(actual_arg, dl);
      annotateExprSlots(actual_expr, slot_ids);
      annotateExprStackCells(actual_expr, stack_cell_ids, slot_ids);
      if (auto actual_cell = extractStackCellSummaryFromExpr(actual_expr,
                                                             cell.width,
                                                             native_sp_offset)) {
        mapped_cell.base_name = actual_cell->base_name;
        mapped_cell.base_offset += actual_cell->base_offset;
        mapped_cell.base_width = actual_cell->base_width;
        mapped_cell.base_from_argument = actual_cell->base_from_argument;
        mapped_cell.base_from_alloca = actual_cell->base_from_alloca;
        mapped_cell.offset += actual_cell->offset;
      } else {
        return std::nullopt;
      }
    }

    if (auto direct = lookup_from_caller_sources(mapped_cell))
      return direct;
    return std::nullopt;
  };
  auto lookup_local_structural_stack_fact =
      [&](const VirtualStackCellSummary &cell) -> std::optional<VirtualValueExpr> {
    auto it = state.structural_stack_facts.find(stackCellKeyForSummary(cell));
    if (it == state.structural_stack_facts.end())
      return std::nullopt;
    return it->second;
  };

  llvm::SmallPtrSet<const llvm::Value *, 16> visiting_values;
  std::function<std::optional<VirtualValueExpr>(llvm::Value *)> eval_value =
      [&](llvm::Value *value) -> std::optional<VirtualValueExpr> {
    if (!value)
      return std::nullopt;
    if (auto it = state.value_facts.find(value); it != state.value_facts.end())
      return it->second;

    if (!visiting_values.insert(value).second)
      return std::nullopt;
    auto pop_visited =
        llvm::make_scope_exit([&] { visiting_values.erase(value); });

    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(value))
      return constantExpr(ci->getZExtValue(), ci->getBitWidth());
    if (llvm::isa<llvm::ConstantPointerNull>(value))
      return constantExpr(0, getValueBitWidth(value, dl));
    if (llvm::isa<llvm::UndefValue>(value) || llvm::isa<llvm::PoisonValue>(value))
      return unknownExpr(getValueBitWidth(value, dl));

    if (auto *arg = llvm::dyn_cast<llvm::Argument>(value)) {
      if (auto it = incoming_args.find(static_cast<unsigned>(arg->getArgNo()));
          it != incoming_args.end()) {
        return normalize_expr(it->second, getValueBitWidth(value, dl));
      }
      return argumentExpr(static_cast<unsigned>(arg->getArgNo()),
                          getValueBitWidth(value, dl));
    }

    auto cache_instruction_expr = [&](const VirtualValueExpr &expr) {
      if (auto *inst = llvm::dyn_cast<llvm::Instruction>(value))
        state.value_facts[inst] = expr;
    };

    if (auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(value)) {
      auto alloc_size = dl.getTypeAllocSize(alloca->getAllocatedType());
      if (alloc_size.isScalable())
        return std::nullopt;
      if (alloca->isArrayAllocation()) {
        auto *array_size =
            llvm::dyn_cast<llvm::ConstantInt>(alloca->getArraySize());
        if (!array_size || !array_size->isOne())
          return std::nullopt;
      }

      VirtualStateSlotSummary slot;
      slot.base_name = alloca->getName().str();
      if (slot.base_name.empty())
        slot.base_name = "alloca";
      slot.offset = 0;
      slot.width = alloc_size.getFixedValue();
      slot.from_argument = false;
      slot.from_alloca = true;

      auto canonical_slot = canonicalize_slot(slot);
      VirtualValueExpr result;
      result.kind = VirtualExprKind::kStateSlot;
      result.complete = true;
      result.state_base_name = slot.base_name;
      result.state_offset = 0;
      result.slot_id = canonical_slot.canonical_id;
      result.bit_width = getValueBitWidth(value, dl);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(value)) {
      unsigned width_bytes =
          std::max(1u, dl.getPointerSize(gep->getType()->getPointerAddressSpace()));
      if (auto slot = extractStateSlotSummary(gep, width_bytes, dl)) {
        auto canonical_slot = canonicalize_slot(*slot);
        auto result =
            normalize_expr(stateSlotExpr(canonical_slot), getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }
      return std::nullopt;
    }

    if (auto *load = llvm::dyn_cast<llvm::LoadInst>(value)) {
      auto width = dl.getTypeStoreSize(load->getType());
      if (width.isScalable())
        return std::nullopt;

      if (auto slot = extractStateSlotSummary(load->getPointerOperand(),
                                              width.getFixedValue(), dl)) {
        auto canonical_slot = canonicalize_slot(*slot);
        VirtualValueExpr result = stateSlotExpr(canonical_slot);
        if (canonical_slot.canonical_id.has_value()) {
          if (auto it = state.slot_facts.find(*canonical_slot.canonical_id);
              it != state.slot_facts.end()) {
            result = normalize_expr(it->second, width.getFixedValue() * 8u);
          } else {
            result = normalize_expr(result, width.getFixedValue() * 8u);
          }
        } else {
          result = normalize_expr(result, width.getFixedValue() * 8u);
        }
        cache_instruction_expr(result);
        return result;
      }

      auto pointer_expr = eval_value(load->getPointerOperand());
      if (!pointer_expr)
        return std::nullopt;
      if (auto pointer_slot =
              extractStateSlotSummaryFromExpr(*pointer_expr, slot_info)) {
        pointer_slot->width = width.getFixedValue();
        auto canonical_slot = canonicalize_slot(*pointer_slot);
        VirtualValueExpr result = stateSlotExpr(canonical_slot);
        if (canonical_slot.canonical_id.has_value()) {
          if (auto it = state.slot_facts.find(*canonical_slot.canonical_id);
              it != state.slot_facts.end()) {
            result = normalize_expr(it->second, width.getFixedValue() * 8u);
          } else {
            result = normalize_expr(result, width.getFixedValue() * 8u);
          }
        } else {
          result = normalize_expr(result, width.getFixedValue() * 8u);
        }
        cache_instruction_expr(result);
        return result;
      }
      if (auto cell =
              extractStackCellSummaryFromExpr(*pointer_expr,
                                             width.getFixedValue(),
                                             native_sp_offset)) {
        auto canonical_cell = canonicalize_cell(*cell);
        VirtualValueExpr result = stackCellExpr(canonical_cell);
        if (auto local_value = lookup_local_structural_stack_fact(canonical_cell)) {
          result = normalize_expr(*local_value, width.getFixedValue() * 8u);
          cache_instruction_expr(result);
          return result;
        }
        if (canonical_cell.canonical_id.has_value()) {
          unsigned cell_id = *canonical_cell.canonical_id;
          std::optional<unsigned> rebased_cell_id;
          bool local_hit = state.stack_facts.count(cell_id);
          bool rebased_hit = false;
          bool caller_hit = false;
          if (auto it = state.stack_facts.find(cell_id);
              it != state.stack_facts.end()) {
            result = normalize_expr(it->second, width.getFixedValue() * 8u);
          } else if ((rebased_cell_id =
                          rebaseSingleStackCellId(model, state.slot_facts,
                                                  cell_id)),
                     rebased_cell_id.has_value() &&
                     *rebased_cell_id != cell_id &&
                     (rebased_hit = state.stack_facts.count(*rebased_cell_id))) {
            result = normalize_expr(state.stack_facts.at(*rebased_cell_id),
                                    width.getFixedValue() * 8u);
          } else if (auto caller_value = lookup_caller_stack_fact(canonical_cell)) {
            caller_hit = true;
            result = normalize_expr(*caller_value, width.getFixedValue() * 8u);
          } else {
            result = normalize_expr(result, width.getFixedValue() * 8u);
          }
          log_stack_lookup("load", canonical_cell, cell_id, rebased_cell_id,
                           local_hit, rebased_hit, caller_hit);
        } else {
          if (auto caller_value = lookup_caller_stack_fact(canonical_cell)) {
            result = normalize_expr(*caller_value, width.getFixedValue() * 8u);
          } else {
            result = normalize_expr(result, width.getFixedValue() * 8u);
          }
        }
        cache_instruction_expr(result);
        return result;
      }

      return std::nullopt;
    }

    if (auto *cast = llvm::dyn_cast<llvm::CastInst>(value)) {
      switch (cast->getOpcode()) {
        case llvm::Instruction::ZExt:
        case llvm::Instruction::SExt:
        case llvm::Instruction::Trunc:
        case llvm::Instruction::BitCast:
        case llvm::Instruction::PtrToInt:
        case llvm::Instruction::IntToPtr: {
          auto inner = eval_value(cast->getOperand(0));
          if (!inner)
            return std::nullopt;
          auto result =
              castExpr(*inner, cast->getOpcode(), getValueBitWidth(value, dl));
          result = normalize_expr(result, result.bit_width);
          cache_instruction_expr(result);
          return result;
        }
        default:
          return std::nullopt;
      }
    }

    if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(value)) {
      auto kind = classifyExprKind(bin->getOpcode());
      switch (kind) {
        case VirtualExprKind::kAdd:
        case VirtualExprKind::kSub:
        case VirtualExprKind::kXor:
        case VirtualExprKind::kAnd:
        case VirtualExprKind::kOr:
        case VirtualExprKind::kShl:
        case VirtualExprKind::kLShr:
        case VirtualExprKind::kAShr:
          break;
        default:
          return std::nullopt;
      }
      auto lhs = eval_value(bin->getOperand(0));
      auto rhs = eval_value(bin->getOperand(1));
      if (!lhs || !rhs)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = kind;
      result.bit_width = getValueBitWidth(value, dl);
      result.complete = lhs->complete && rhs->complete;
      result.operands.push_back(*lhs);
      result.operands.push_back(*rhs);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(value)) {
      auto kind = classifyICmpPredicate(icmp->getPredicate());
      if (kind == VirtualExprKind::kUnknown)
        return std::nullopt;
      auto lhs = eval_value(icmp->getOperand(0));
      auto rhs = eval_value(icmp->getOperand(1));
      if (!lhs || !rhs)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = kind;
      result.bit_width = 1;
      result.complete = lhs->complete && rhs->complete;
      result.operands.push_back(*lhs);
      result.operands.push_back(*rhs);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *select = llvm::dyn_cast<llvm::SelectInst>(value)) {
      auto cond = eval_value(select->getCondition());
      auto true_value = eval_value(select->getTrueValue());
      auto false_value = eval_value(select->getFalseValue());
      if (!cond || !true_value || !false_value)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = VirtualExprKind::kSelect;
      result.bit_width = getValueBitWidth(value, dl);
      result.complete =
          cond->complete && true_value->complete && false_value->complete;
      result.operands.push_back(*cond);
      result.operands.push_back(*true_value);
      result.operands.push_back(*false_value);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *phi = llvm::dyn_cast<llvm::PHINode>(value)) {
      if (phi->getNumIncomingValues() == 0 || phi->getNumIncomingValues() > 4)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = VirtualExprKind::kPhi;
      result.bit_width = getValueBitWidth(value, dl);
      result.complete = true;
      for (llvm::Value *incoming : phi->incoming_values()) {
        auto incoming_expr = eval_value(incoming);
        if (!incoming_expr)
          return std::nullopt;
        result.complete &= incoming_expr->complete;
        result.operands.push_back(*incoming_expr);
      }
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *call = llvm::dyn_cast<llvm::CallBase>(value)) {
      auto *callee = call->getCalledFunction();
      if (!callee)
        return std::nullopt;

      if (isRemillReadMemoryIntrinsic(*callee) && call->arg_size() >= 2) {
        unsigned width_bits =
            remillMemoryBitWidth(callee->getName())
                .value_or(getValueBitWidth(value, dl));
        unsigned width_bytes = std::max(1u, width_bits / 8u);
        auto address_expr = eval_value(call->getArgOperand(1));
        if (!address_expr)
          return std::nullopt;
        if (auto constant_addr = resolveSpecializedExprToConstant(
                *address_expr, state.slot_facts, state.stack_facts)) {
          if (auto folded =
                  readBinaryConstantExpr(binary_memory, *constant_addr,
                                         width_bits)) {
            auto result = normalize_expr(*folded, width_bits);
            cache_instruction_expr(result);
            return result;
          }
        }
        auto slot_fact_values = slotFactsForMap(state.slot_facts);
        auto stack_fact_values = stackFactsForMap(state.stack_facts);
        llvm::SmallVector<uint64_t, 4> address_choices;
        if (collectEvaluatedValueChoices(*address_expr, slot_fact_values,
                                         stack_fact_values, address_choices) &&
            !address_choices.empty() && address_choices.size() <= 4) {
          llvm::SmallVector<VirtualValueExpr, 4> loaded_choices;
          for (uint64_t address_choice : address_choices) {
            auto folded =
                readBinaryConstantExpr(binary_memory, address_choice, width_bits);
            if (!folded.has_value()) {
              loaded_choices.clear();
              break;
            }
            loaded_choices.push_back(*folded);
          }
          if (!loaded_choices.empty()) {
            VirtualValueExpr result;
            if (loaded_choices.size() == 1) {
              result = loaded_choices.front();
            } else {
              result.kind = VirtualExprKind::kPhi;
              result.bit_width = width_bits;
              result.complete = true;
              result.operands.assign(loaded_choices.begin(),
                                     loaded_choices.end());
            }
            result = normalize_expr(result, width_bits);
            cache_instruction_expr(result);
            return result;
          }
        }
        if (auto cell =
                extractStackCellSummaryFromExpr(*address_expr,
                                               width_bytes,
                                               native_sp_offset)) {
          auto canonical_cell = canonicalize_cell(*cell);
          VirtualValueExpr result = stackCellExpr(canonical_cell);
          if (auto local_value =
                  lookup_local_structural_stack_fact(canonical_cell)) {
            result = normalize_expr(*local_value, width_bits);
            cache_instruction_expr(result);
            return result;
          }
          if (canonical_cell.canonical_id.has_value()) {
            unsigned cell_id = *canonical_cell.canonical_id;
            std::optional<unsigned> rebased_cell_id;
            bool local_hit = state.stack_facts.count(cell_id);
            bool rebased_hit = false;
            bool caller_hit = false;
            if (auto it = state.stack_facts.find(cell_id);
                it != state.stack_facts.end()) {
              result = normalize_expr(it->second, width_bits);
            } else if ((rebased_cell_id =
                            rebaseSingleStackCellId(model, state.slot_facts,
                                                    cell_id)),
                       rebased_cell_id.has_value() &&
                       *rebased_cell_id != cell_id &&
                       (rebased_hit = state.stack_facts.count(*rebased_cell_id))) {
              result = normalize_expr(state.stack_facts.at(*rebased_cell_id),
                                      width_bits);
            } else if (auto caller_value =
                           lookup_caller_stack_fact(canonical_cell)) {
              caller_hit = true;
              result = normalize_expr(*caller_value, width_bits);
            } else {
              result = normalize_expr(result, width_bits);
            }
            log_stack_lookup("readmem", canonical_cell, cell_id, rebased_cell_id,
                             local_hit, rebased_hit, caller_hit);
          } else {
            if (auto caller_value = lookup_caller_stack_fact(canonical_cell)) {
              result = normalize_expr(*caller_value, width_bits);
            } else {
              result = normalize_expr(result, width_bits);
            }
          }
          cache_instruction_expr(result);
          return result;
        }
        VirtualValueExpr result;
        result.kind = VirtualExprKind::kMemoryRead;
        result.bit_width = width_bits;
        result.complete = address_expr->complete;
        result.operands.push_back(*address_expr);
        result = normalize_expr(result, width_bits);
        cache_instruction_expr(result);
        return result;
      }

      if (isRemillWriteMemoryIntrinsic(*callee) && call->arg_size() >= 1) {
        auto memory_expr = eval_value(call->getArgOperand(0));
        if (!memory_expr)
          return std::nullopt;
        auto result = normalize_expr(*memory_expr, getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }

      if (handler_index.find(callee->getName().str()) != handler_index.end() &&
          call->arg_size() >= 1) {
        auto memory_expr = eval_value(call->getArgOperand(0));
        if (!memory_expr)
          return std::nullopt;
        auto result = normalize_expr(*memory_expr, getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }

      if (isRemillTerminalControlIntrinsic(*callee) && call->arg_size() >= 1) {
        auto memory_expr = eval_value(call->getArgOperand(0));
        if (!memory_expr)
          return std::nullopt;
        auto result = normalize_expr(*memory_expr, getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }

      return std::nullopt;
    }

    auto fallback = summarizeValueExpr(value, dl);
    if (fallback.kind == VirtualExprKind::kUnknown)
      return std::nullopt;
    fallback = normalize_expr(fallback, getValueBitWidth(value, dl));
    if (auto *inst = llvm::dyn_cast<llvm::Instruction>(value))
      state.value_facts[inst] = fallback;
    return fallback;
  };

  auto cache_instruction_value = [&](llvm::Instruction &I) {
    if (I.getType()->isVoidTy())
      return true;
    if (llvm::isa<llvm::StoreInst>(I))
      return true;
    auto expr = eval_value(&I);
    if (!expr) {
      vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                 " reason=unsupported-value inst=" +
                                 std::string(I.getOpcodeName()));
      return false;
    }
    state.value_facts[&I] = *expr;
    return true;
  };

  for (auto *BB : *replay_blocks) {
    for (auto &I : *BB) {
      if (!cache_instruction_value(I))
        return std::nullopt;

      if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto width = dl.getTypeStoreSize(store->getValueOperand()->getType());
        if (width.isScalable()) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=scalable-store");
          return std::nullopt;
        }

        auto value_expr = eval_value(store->getValueOperand());
        if (!value_expr) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=store-value");
          return std::nullopt;
        }
        auto normalized_value = *value_expr;
        if (!normalized_value.bit_width)
          normalized_value.bit_width = width.getFixedValue() * 8u;
        if (auto slot = extractStateSlotSummary(store->getPointerOperand(),
                                                width.getFixedValue(), dl)) {
          auto canonical_slot = canonicalize_slot(*slot);
          if (!canonical_slot.canonical_id.has_value()) {
            vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                       " reason=unknown-store-slot");
            return std::nullopt;
          }
          state.slot_facts[*canonical_slot.canonical_id] = normalized_value;
          localized_written_slot_ids.insert(*canonical_slot.canonical_id);
          propagateAliasedStateSlotWrite(
              state.slot_facts, *canonical_slot.canonical_id, normalized_value,
              slot_info);
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                     render_update("slot",
                                                   *canonical_slot.canonical_id,
                                                   normalized_value));
          continue;
        }

        auto pointer_expr = eval_value(store->getPointerOperand());
        if (!pointer_expr) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=store-pointer");
          return std::nullopt;
        }
        if (auto pointer_slot =
                extractStateSlotSummaryFromExpr(*pointer_expr, slot_info)) {
          pointer_slot->width = width.getFixedValue();
          auto canonical_slot = canonicalize_slot(*pointer_slot);
          if (!canonical_slot.canonical_id.has_value()) {
            vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                       " reason=unknown-store-slot");
            return std::nullopt;
          }
          state.slot_facts[*canonical_slot.canonical_id] = normalized_value;
          localized_written_slot_ids.insert(*canonical_slot.canonical_id);
          propagateAliasedStateSlotWrite(
              state.slot_facts, *canonical_slot.canonical_id, normalized_value,
              slot_info);
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                     render_update("slot",
                                                   *canonical_slot.canonical_id,
                                                   normalized_value));
          continue;
        }
        auto cell = extractStackCellSummaryFromExpr(*pointer_expr,
                                                    width.getFixedValue(),
                                                    native_sp_offset);
        if (!cell) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=store-target");
          return std::nullopt;
        }
        auto canonical_cell = canonicalize_cell(*cell);
        auto structural_key = stackCellKeyForSummary(canonical_cell);
        state.structural_stack_facts[structural_key] = normalized_value;
        localized_written_structural_stack_keys.insert(structural_key);
        if (canonical_cell.canonical_id.has_value()) {
          state.stack_facts[*canonical_cell.canonical_id] = normalized_value;
          localized_written_stack_cell_ids.insert(*canonical_cell.canonical_id);
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                     render_update("cell",
                                                   *canonical_cell.canonical_id,
                                                   normalized_value));
        } else {
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() +
                                     " structural-cell " +
                                     render_structural_update(canonical_cell,
                                                              normalized_value));
        }
        continue;
      }

      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;

      auto *callee = call->getCalledFunction();
      if (!callee) {
        vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                   " reason=indirect-call");
        return std::nullopt;
      }
      if (isRemillReadMemoryIntrinsic(*callee))
        continue;
      if (isRemillTerminalControlIntrinsic(*callee))
        continue;
      if (isRemillWriteMemoryIntrinsic(*callee)) {
        if (call->arg_size() < 3) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=short-write-memory");
          return std::nullopt;
        }

        unsigned width_bits = remillMemoryBitWidth(callee->getName()).value_or(0);
        unsigned width_bytes = std::max(1u, width_bits / 8u);
        auto address_expr = eval_value(call->getArgOperand(1));
        auto value_expr = eval_value(call->getArgOperand(2));
        if (!address_expr || !value_expr) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=write-memory-operands");
          return std::nullopt;
        }
        auto normalized_value = *value_expr;
        if (!normalized_value.bit_width)
          normalized_value.bit_width = std::max(1u, width_bits);
        auto cell = extractStackCellSummaryFromExpr(*address_expr, width_bytes,
                                                    native_sp_offset);
        if (!cell) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=write-memory-target");
          return std::nullopt;
        }
        auto canonical_cell = canonicalize_cell(*cell);
        auto structural_key = stackCellKeyForSummary(canonical_cell);
        state.structural_stack_facts[structural_key] = normalized_value;
        localized_written_structural_stack_keys.insert(structural_key);
        if (canonical_cell.canonical_id.has_value()) {
          state.stack_facts[*canonical_cell.canonical_id] = normalized_value;
          localized_written_stack_cell_ids.insert(*canonical_cell.canonical_id);
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                     render_update("cell",
                                                   *canonical_cell.canonical_id,
                                                   normalized_value));
        } else {
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() +
                                     " structural-cell " +
                                     render_structural_update(canonical_cell,
                                                              normalized_value));
        }
        continue;
      }

      auto slot_facts_before_call = state.slot_facts;
      auto stack_facts_before_call = state.stack_facts;
      auto structural_stack_facts_before_call = state.structural_stack_facts;
      if (applySingleDirectCalleeEffects(
              F, *call, model, handler_index, outgoing_maps,
              outgoing_stack_maps, incoming_args, state.slot_facts,
              state.stack_facts, state.structural_stack_facts, slot_ids,
              slot_info, stack_cell_ids, stack_cell_info, dl, binary_memory,
              depth + 1, visiting, fallback_caller_structural_stack_facts,
              fallback_caller_stack_facts, fallback_caller_slot_facts)) {
        vmModelStageDebugLog("leaf-replay: helper=" + F.getName().str() +
                             " callee=" + callee->getName().str() +
                             " step=post-direct-call-begin");
        for (const auto &[slot_id, value] : state.slot_facts) {
          auto before_it = slot_facts_before_call.find(slot_id);
          if (before_it == slot_facts_before_call.end() ||
              !exprEquals(before_it->second, value)) {
            localized_written_slot_ids.insert(slot_id);
          }
        }
        for (const auto &[cell_id, value] : state.stack_facts) {
          auto before_it = stack_facts_before_call.find(cell_id);
          if (before_it == stack_facts_before_call.end() ||
              !exprEquals(before_it->second, value)) {
            localized_written_stack_cell_ids.insert(cell_id);
          }
        }
        for (const auto &[key, value] : state.structural_stack_facts) {
          auto before_it = structural_stack_facts_before_call.find(key);
          if (before_it == structural_stack_facts_before_call.end() ||
              !exprEquals(before_it->second, value)) {
            localized_written_structural_stack_keys.insert(key);
          }
        }
        vmModelStageDebugLog("leaf-replay: helper=" + F.getName().str() +
                             " callee=" + callee->getName().str() +
                             " step=post-direct-call-written-set-done");
        if (!isNestedCodeBearingReplayFunction(F, depth)) {
          vmModelStageDebugLog("leaf-replay: helper=" + F.getName().str() +
                               " callee=" + callee->getName().str() +
                               " step=post-direct-call-specialize-begin");
          specializeFactStateToFixpoint(state.slot_facts, state.stack_facts,
                                        &incoming_args, slot_ids,
                                        stack_cell_ids);
          vmModelStageDebugLog("leaf-replay: helper=" + F.getName().str() +
                               " callee=" + callee->getName().str() +
                               " step=post-direct-call-specialize-done");
        } else {
          vmModelStageDebugLog("leaf-replay: helper=" + F.getName().str() +
                               " callee=" + callee->getName().str() +
                               " step=post-direct-call-specialize-skipped");
        }
        vmModelLocalReplayDebugLog("helper=" + F.getName().str() +
                                   " direct-call-localized=" +
                                   callee->getName().str());
        continue;
      }

      vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                 " reason=unsupported-call callee=" +
                                 callee->getName().str());
      return std::nullopt;
    }
  }

  CallsiteLocalizedOutgoingFacts localized;
  localized.outgoing_slots = std::move(state.slot_facts);
  localized.outgoing_stack = std::move(state.stack_facts);
  localized.structural_outgoing_stack = std::move(state.structural_stack_facts);
  localized.written_slot_ids = std::move(localized_written_slot_ids);
  localized.written_stack_cell_ids = std::move(localized_written_stack_cell_ids);
  localized.written_structural_stack_keys =
      std::move(localized_written_structural_stack_keys);
  return localized;
}


}  // namespace omill::virtual_model::detail

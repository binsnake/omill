#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StableHashing.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/StructuralHash.h>

#include <algorithm>
#include <tuple>
#include <vector>

#include "omill/Utils/LiftedNames.h"

namespace omill::virtual_model::detail {

static uint64_t parseLeadingHex(llvm::StringRef text) {
  size_t hex_len = 0;
  while (hex_len < text.size() && llvm::isHexDigit(text[hex_len]))
    ++hex_len;
  if (hex_len == 0)
    return 0;

  uint64_t value = 0;
  if (text.substr(0, hex_len).getAsInteger(16, value))
    return 0;
  return value;
}

static uint64_t extractLiftedPCFromName(llvm::StringRef name) {
  if (uint64_t va = extractEntryVA(name))
    return va;

  if (name.starts_with("blk_"))
    return parseLeadingHex(name.drop_front(4));

  if (name.starts_with("block_"))
    return parseLeadingHex(name.drop_front(6));

  return 0;
}

std::optional<uint64_t> extractHexAttr(
    const llvm::Function &F, llvm::StringRef attr_name) {
  auto attr = F.getFnAttribute(attr_name);
  if (!attr.isValid() || !attr.isStringAttribute())
    return std::nullopt;

  uint64_t value = 0;
  if (attr.getValueAsString().getAsInteger(16, value))
    return std::nullopt;
  return value;
}

static llvm::stable_hash stableHashAttribute(const llvm::Function &F,
                                             llvm::StringRef attr_name) {
  auto attr = F.getFnAttribute(attr_name);
  if (!attr.isValid())
    return llvm::stable_hash_combine(llvm::stable_hash_name(attr_name), 0);
  if (attr.isStringAttribute()) {
    return llvm::stable_hash_combine(
        llvm::stable_hash_name(attr_name),
        llvm::stable_hash_name(attr.getValueAsString()));
  }
  return llvm::stable_hash_combine(llvm::stable_hash_name(attr_name), 1);
}

llvm::stable_hash summaryRelevantFunctionFingerprint(
    const llvm::Function &F) {
  llvm::stable_hash hash = llvm::StructuralHash(F, /*DetailedHash=*/true);
  static constexpr llvm::StringLiteral kRelevantAttrs[] = {
      "omill.output_root",
      "omill.virtual_specialized",
      "omill.virtual_specialization.root_va",
      "omill.virtual_specialization.facts",
      "omill.virtual_specialization.stack_facts",
      "omill.closed_root_slice",
      "omill.closed_root_slice_root",
      "omill.vm_handler",
      "omill.vm_wrapper",
      "omill.vm_newly_lifted",
      "omill.newly_lifted",
      "omill.vm_demerged_clone",
      "omill.vm_outlined_virtual_call",
  };
  for (llvm::StringLiteral attr_name : kRelevantAttrs)
    hash = llvm::stable_hash_combine(hash, stableHashAttribute(F, attr_name));
  return hash;
}

static std::vector<VirtualSlotFact> parseSpecializationFacts(
    const llvm::Function &F) {
  auto attr = F.getFnAttribute("omill.virtual_specialization.facts");
  if (!attr.isValid() || !attr.isStringAttribute())
    return {};

  std::vector<VirtualSlotFact> facts;
  llvm::SmallVector<llvm::StringRef, 8> entries;
  attr.getValueAsString().split(entries, ',', -1, false);
  for (auto entry : entries) {
    entry = entry.trim();
    if (entry.empty())
      continue;

    auto slot_and_value = entry.split('=');
    if (slot_and_value.first.empty() || slot_and_value.second.empty())
      continue;

    auto slot_and_width = slot_and_value.first.split(':');
    unsigned slot_id = 0;
    unsigned bit_width = 0;
    uint64_t value = 0;
    if (slot_and_width.first.getAsInteger(10, slot_id))
      continue;
    if (slot_and_width.second.getAsInteger(10, bit_width))
      continue;
    if (slot_and_value.second.getAsInteger(16, value))
      continue;

    VirtualValueExpr expr;
    expr.kind = VirtualExprKind::kConstant;
    expr.bit_width = bit_width;
    expr.complete = true;
    expr.constant = value;
    facts.push_back(VirtualSlotFact{slot_id, std::move(expr)});
  }
  return facts;
}

static std::vector<VirtualStackFact> parseSpecializationStackFacts(
    const llvm::Function &F) {
  auto attr = F.getFnAttribute("omill.virtual_specialization.stack_facts");
  if (!attr.isValid() || !attr.isStringAttribute())
    return {};

  std::vector<VirtualStackFact> facts;
  llvm::SmallVector<llvm::StringRef, 8> entries;
  attr.getValueAsString().split(entries, ',', -1, false);
  for (auto entry : entries) {
    entry = entry.trim();
    if (entry.empty())
      continue;

    auto cell_and_value = entry.split('=');
    if (cell_and_value.first.empty() || cell_and_value.second.empty())
      continue;

    auto cell_and_width = cell_and_value.first.split(':');
    unsigned cell_id = 0;
    unsigned bit_width = 0;
    uint64_t value = 0;
    if (cell_and_width.first.getAsInteger(10, cell_id))
      continue;
    if (cell_and_width.second.getAsInteger(10, bit_width))
      continue;
    if (cell_and_value.second.getAsInteger(16, value))
      continue;

    VirtualValueExpr expr;
    expr.kind = VirtualExprKind::kConstant;
    expr.bit_width = bit_width;
    expr.complete = true;
    expr.constant = value;
    facts.push_back(VirtualStackFact{cell_id, std::move(expr)});
  }
  return facts;
}

VirtualBoundaryKind classifyBoundaryKind(
    const llvm::Function &F) {
  auto kind_attr = F.getFnAttribute("omill.boundary_kind");
  if (kind_attr.isValid() && kind_attr.isStringAttribute()) {
    auto kind = kind_attr.getValueAsString();
    if (kind == "vm_entry_stub")
      return VirtualBoundaryKind::kProtectedEntryStub;
    return VirtualBoundaryKind::kProtectedBoundary;
  }

  if (F.hasFnAttribute("omill.protection_boundary"))
    return VirtualBoundaryKind::kProtectedBoundary;

  if (F.getName().starts_with("vm_entry_"))
    return VirtualBoundaryKind::kProtectedEntryStub;

  return VirtualBoundaryKind::kUnknown;
}

bool isBoundaryFunction(const llvm::Function &F) {
  return classifyBoundaryKind(F) != VirtualBoundaryKind::kUnknown;
}

static bool isLiftedOrHelperSeedFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.hasFnAttribute("omill.localized_continuation_shim"))
    return false;
  auto name = F.getName();
  if (name.starts_with("sub_") || name.starts_with("blk_") ||
      name.starts_with("block_")) {
    return true;
  }
  if (F.hasFnAttribute("omill.output_root") ||
      F.hasFnAttribute("omill.virtual_specialized") ||
      F.hasFnAttribute("omill.closed_root_slice") ||
      F.hasFnAttribute("omill.vm_handler") ||
      F.hasFnAttribute("omill.vm_wrapper")) {
    return true;
  }
  return false;
}

static bool isVirtualModelNamedCodeFunction(const llvm::Function &F) {
  auto name = F.getName();
  return name.starts_with("sub_") || name.starts_with("blk_") ||
         name.starts_with("block_") || name.starts_with("__lifted_");
}

static bool hasVirtualModelCodeBearingAttr(const llvm::Function &F) {
  return F.hasFnAttribute("omill.output_root") ||
         F.hasFnAttribute("omill.virtual_specialized") ||
         F.hasFnAttribute("omill.closed_root_slice_root") ||
         F.hasFnAttribute("omill.vm_wrapper") ||
         F.hasFnAttribute("omill.vm_newly_lifted") ||
         F.hasFnAttribute("omill.newly_lifted") ||
         F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
         F.getFnAttribute("omill.vm_outlined_virtual_call").isValid();
}

bool isVirtualModelInitialSeedFunction(
    const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.hasFnAttribute("omill.localized_continuation_shim"))
    return false;
  return isVirtualModelNamedCodeFunction(F) ||
         hasVirtualModelCodeBearingAttr(F);
}

bool isVirtualModelCodeBearingFunction(
    const llvm::Function &F) {
  return !F.isDeclaration() &&
         !F.hasFnAttribute("omill.localized_continuation_shim") &&
         (isVirtualModelNamedCodeFunction(F) ||
          hasVirtualModelCodeBearingAttr(F));
}

static bool isDispatchIntrinsic(const llvm::Function &F) {
  return isDispatchIntrinsicName(F.getName());
}

static void collectExprReferencedStackCells(
    const VirtualValueExpr &expr,
    std::vector<VirtualStackCellSummary> &cells) {
  auto expr_width_bytes = [](const VirtualValueExpr &value) {
    return value.bit_width ? std::max(1u, value.bit_width / 8u) : 8u;
  };
  if (expr.kind == VirtualExprKind::kStackCell && expr.state_base_name.has_value() &&
      expr.state_offset.has_value() && expr.stack_offset.has_value()) {
    llvm::StringRef base_name = *expr.state_base_name;
    const bool from_argument = base_name.starts_with("arg");
    cells.push_back(VirtualStackCellSummary{
        *expr.state_base_name,
        *expr.state_offset,
        expr_width_bytes(expr),
        *expr.stack_offset,
        expr_width_bytes(expr),
        1,
        0,
        from_argument,
        !from_argument,
        std::nullopt,
        std::nullopt,
    });
  }
  for (const auto &operand : expr.operands)
    collectExprReferencedStackCells(operand, cells);
}

void collectExprReferencedStateSlots(
    const VirtualValueExpr &expr,
    std::vector<VirtualStateSlotSummary> &slots) {
  auto expr_width_bytes = [](const VirtualValueExpr &value) {
    return value.bit_width ? std::max(1u, value.bit_width / 8u) : 8u;
  };
  if (expr.kind == VirtualExprKind::kStateSlot && expr.state_base_name.has_value() &&
      expr.state_offset.has_value()) {
    llvm::StringRef base_name = *expr.state_base_name;
    const bool from_argument = base_name.starts_with("arg");
    slots.push_back(VirtualStateSlotSummary{
        *expr.state_base_name,
        *expr.state_offset,
        expr_width_bytes(expr),
        1,
        0,
        from_argument,
        !from_argument,
        std::nullopt,
    });
  }
  for (const auto &operand : expr.operands)
    collectExprReferencedStateSlots(operand, slots);
}

VirtualHandlerSummary summarizeFunction(
    llvm::Function &F) {
  constexpr unsigned kDefaultMaxSummaryStackCells = 16;
  const unsigned kMaxSummaryStackCells = []() {
    if (const char *v = std::getenv("OMILL_VM_SUMMARY_STACK_CELL_BUDGET")) {
      unsigned parsed = 0;
      if (!llvm::StringRef(v).getAsInteger(10, parsed) && parsed != 0)
        return parsed;
    }
    return kDefaultMaxSummaryStackCells;
  }();

  VirtualHandlerSummary summary;
  summary.function_name = F.getName().str();
  uint64_t entry_va = extractLiftedPCFromName(F.getName());
  if (entry_va != 0)
    summary.entry_va = entry_va;
  summary.is_output_root = F.hasFnAttribute("omill.output_root");
  summary.is_closed_root_slice_root =
      F.hasFnAttribute("omill.closed_root_slice_root");
  summary.is_specialized = F.hasFnAttribute("omill.virtual_specialized");
  summary.is_dirty_seed = F.hasFnAttribute("omill.vm_newly_lifted") ||
                          F.hasFnAttribute("omill.newly_lifted") ||
                          F.hasFnAttribute("omill.terminal_boundary_recovery_seed");
  summary.specialization_root_va =
      extractHexAttr(F, "omill.virtual_specialization.root_va");
  summary.specialization_facts = parseSpecializationFacts(F);
  summary.specialization_stack_facts = parseSpecializationStackFacts(F);

  const llvm::DataLayout &dl = F.getParent()->getDataLayout();
  std::vector<std::tuple<std::string, int64_t, unsigned, unsigned, unsigned,
                         bool, bool>>
      slot_accum;
  std::vector<std::tuple<std::string, int64_t, unsigned, int64_t, unsigned,
                         unsigned, unsigned, bool, bool>>
      stack_cell_accum;

  auto recordSlot = [&](const VirtualStateSlotSummary &slot, bool is_store) {
    auto it = std::find_if(slot_accum.begin(), slot_accum.end(),
                           [&](const auto &current) {
                             return std::get<0>(current) == slot.base_name &&
                                    std::get<1>(current) == slot.offset &&
                                    std::get<2>(current) == slot.width &&
                                    std::get<5>(current) == slot.from_argument &&
                                    std::get<6>(current) == slot.from_alloca;
                           });
    if (it == slot_accum.end()) {
      slot_accum.emplace_back(slot.base_name, slot.offset, slot.width,
                              is_store ? 0u : 1u, is_store ? 1u : 0u,
                              slot.from_argument, slot.from_alloca);
      return;
    }
    if (is_store)
      ++std::get<4>(*it);
    else
      ++std::get<3>(*it);
  };

  auto recordStackCell = [&](const VirtualStackCellSummary &cell,
                             bool is_store) {
    auto it = std::find_if(stack_cell_accum.begin(), stack_cell_accum.end(),
                           [&](const auto &current) {
                              return std::get<0>(current) == cell.base_name &&
                                     std::get<1>(current) == cell.base_offset &&
                                     std::get<2>(current) == cell.base_width &&
                                     std::get<3>(current) == cell.offset &&
                                     std::get<4>(current) == cell.width &&
                                     std::get<7>(current) ==
                                         cell.base_from_argument &&
                                     std::get<8>(current) ==
                                         cell.base_from_alloca;
                           });
    if (it == stack_cell_accum.end()) {
      if (stack_cell_accum.size() >= kMaxSummaryStackCells) {
        summary.stack_memory_budget_exceeded = true;
        return false;
      }
      stack_cell_accum.emplace_back(
          cell.base_name, cell.base_offset, cell.base_width, cell.offset,
          cell.width, is_store ? 0u : 1u, is_store ? 1u : 0u,
          cell.base_from_argument, cell.base_from_alloca);
      return true;
    }
    if (is_store)
      ++std::get<6>(*it);
    else
      ++std::get<5>(*it);
    return true;
  };

  auto recordExprStackCells = [&](const VirtualValueExpr &expr) {
    unsigned expr_width = expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u;
    if (auto cell = extractStackCellSummaryFromExpr(expr, expr_width))
      recordStackCell(*cell, /*is_store=*/false);
    std::vector<VirtualStackCellSummary> referenced_cells;
    collectExprReferencedStackCells(expr, referenced_cells);
    for (const auto &cell : referenced_cells)
      recordStackCell(cell, /*is_store=*/false);
  };

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *load = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        auto width = dl.getTypeStoreSize(load->getType());
        if (width.isScalable())
          continue;
        if (auto slot = extractStateSlotSummary(load->getPointerOperand(),
                                                width.getFixedValue(), dl)) {
          recordSlot(*slot, /*is_store=*/false);
        } else {
          auto pointer_expr = summarizeValueExpr(load->getPointerOperand(), dl);
          if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                          width.getFixedValue())) {
            recordStackCell(*cell, /*is_store=*/false);
          } else if (pointer_expr.kind == VirtualExprKind::kStateSlot ||
                     (pointer_expr.kind == VirtualExprKind::kAdd &&
                      llvm::any_of(pointer_expr.operands,
                                   [](const VirtualValueExpr &operand) {
                                     return operand.kind ==
                                            VirtualExprKind::kStateSlot;
                                   })) ||
                     (pointer_expr.kind == VirtualExprKind::kSub &&
                      !pointer_expr.operands.empty() &&
                      pointer_expr.operands.front().kind ==
                          VirtualExprKind::kStateSlot)) {
            summary.has_unsupported_stack_memory = true;
          }
        }
        continue;
      }

      if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto width = dl.getTypeStoreSize(store->getValueOperand()->getType());
        if (width.isScalable())
          continue;
        if (auto slot = extractStateSlotSummary(store->getPointerOperand(),
                                                width.getFixedValue(), dl)) {
          recordSlot(*slot, /*is_store=*/true);
          auto value_expr = summarizeValueExpr(store->getValueOperand(), dl);
          recordExprStackCells(value_expr);
          summary.state_transfers.push_back(
              VirtualStateTransferSummary{*slot, std::move(value_expr)});
        } else {
          auto pointer_expr = summarizeValueExpr(store->getPointerOperand(), dl);
          if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                          width.getFixedValue())) {
            if (recordStackCell(*cell, /*is_store=*/true)) {
              auto value_expr = summarizeValueExpr(store->getValueOperand(), dl);
              recordExprStackCells(value_expr);
              summary.stack_transfers.push_back(
                  VirtualStackTransferSummary{*cell, std::move(value_expr)});
            }
          } else if (pointer_expr.kind == VirtualExprKind::kStateSlot ||
                     (pointer_expr.kind == VirtualExprKind::kAdd &&
                      llvm::any_of(pointer_expr.operands,
                                   [](const VirtualValueExpr &operand) {
                                     return operand.kind ==
                                            VirtualExprKind::kStateSlot;
                                   })) ||
                     (pointer_expr.kind == VirtualExprKind::kSub &&
                      !pointer_expr.operands.empty() &&
                      pointer_expr.operands.front().kind ==
                          VirtualExprKind::kStateSlot)) {
            summary.has_unsupported_stack_memory = true;
          }
        }
        continue;
      }

      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;

      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;

      for (llvm::Value *arg : call->args()) {
        auto arg_expr = summarizeValueExpr(arg, dl);
        recordExprStackCells(arg_expr);
      }

      if (isRemillWriteMemoryIntrinsic(*callee) && call->arg_size() >= 3) {
        unsigned width_bits =
            remillMemoryBitWidth(callee->getName()).value_or(0);
        unsigned width_bytes = width_bits / 8;
        auto address_expr = summarizeValueExpr(call->getArgOperand(1), dl);
        if (auto cell =
                extractStackCellSummaryFromExpr(address_expr, width_bytes)) {
          if (recordStackCell(*cell, /*is_store=*/true)) {
            auto value_expr = summarizeValueExpr(call->getArgOperand(2), dl);
            recordExprStackCells(value_expr);
            summary.stack_transfers.push_back(VirtualStackTransferSummary{
                *cell, std::move(value_expr)});
          }
        } else if (address_expr.kind == VirtualExprKind::kStateSlot ||
                   address_expr.kind == VirtualExprKind::kArgument ||
                   (address_expr.kind == VirtualExprKind::kAdd &&
                    llvm::any_of(address_expr.operands,
                                 [](const VirtualValueExpr &operand) {
                                   return operand.kind ==
                                              VirtualExprKind::kStateSlot ||
                                          operand.kind ==
                                              VirtualExprKind::kArgument;
                                 })) ||
                   (address_expr.kind == VirtualExprKind::kSub &&
                    !address_expr.operands.empty() &&
                    (address_expr.operands.front().kind ==
                         VirtualExprKind::kStateSlot ||
                     address_expr.operands.front().kind ==
                         VirtualExprKind::kArgument))) {
          summary.has_unsupported_stack_memory = true;
        }
        continue;
      }

      if (isDispatchIntrinsic(*callee)) {
        if (callee->getName().ends_with("call"))
          ++summary.dispatch_call_count;
        else
          ++summary.dispatch_jump_count;
        if (call->arg_size() >= 2) {
          VirtualDispatchSummary dispatch;
          dispatch.is_jump = callee->getName().ends_with("jump");
          dispatch.target = summarizeValueExpr(call->getArgOperand(1), dl);
          summary.dispatches.push_back(std::move(dispatch));
        }
        continue;
      }

      if (!isBoundaryFunction(*callee))
        goto non_boundary_call;

      ++summary.protected_boundary_call_count;
      summary.called_boundaries.push_back(callee->getName().str());
      continue;

    non_boundary_call:
      if (isCallSiteHelper(*callee) && call->arg_size() >= 3) {
        VirtualCallSiteSummary callsite;
        callsite.is_call = true;
        callsite.target = summarizeValueExpr(call->getArgOperand(2), dl);
        summary.callsites.push_back(std::move(callsite));
      }
      if (!callee->isDeclaration())
        summary.direct_callees.push_back(callee->getName().str());
    }
  }

  for (const auto &slot : slot_accum) {
    summary.state_slots.push_back(VirtualStateSlotSummary{
        std::get<0>(slot),
        std::get<1>(slot),
        std::get<2>(slot),
        std::get<3>(slot),
        std::get<4>(slot),
        std::get<5>(slot),
        std::get<6>(slot),
        std::nullopt,
    });
  }

  for (const auto &cell : stack_cell_accum) {
    summary.stack_cells.push_back(VirtualStackCellSummary{
        std::get<0>(cell),
        std::get<1>(cell),
        std::get<2>(cell),
        std::get<3>(cell),
        std::get<4>(cell),
        std::get<5>(cell),
        std::get<6>(cell),
        std::get<7>(cell),
        std::get<8>(cell),
        std::nullopt,
        std::nullopt,
    });
  }

  std::sort(summary.called_boundaries.begin(), summary.called_boundaries.end());
  summary.called_boundaries.erase(
      std::unique(summary.called_boundaries.begin(),
                  summary.called_boundaries.end()),
      summary.called_boundaries.end());
  std::sort(summary.direct_callees.begin(), summary.direct_callees.end());
  summary.direct_callees.erase(
      std::unique(summary.direct_callees.begin(), summary.direct_callees.end()),
      summary.direct_callees.end());

  const bool has_dispatch =
      (summary.dispatch_call_count + summary.dispatch_jump_count) != 0;
  const bool has_boundary_call = summary.protected_boundary_call_count != 0;
  const bool has_callsite = !summary.callsites.empty();
  const bool has_control_transfer =
      has_dispatch || has_boundary_call || has_callsite;
  const bool has_state_shape = summary.state_slots.size() >= 2;
  const bool has_minimal_state =
      !summary.state_slots.empty() || !summary.stack_cells.empty();
  const bool is_lifted_like = isLiftedOrHelperSeedFunction(F);
  summary.is_candidate =
      (has_state_shape && (has_dispatch || has_boundary_call)) ||
      (is_lifted_like && has_control_transfer && has_minimal_state);
  return summary;
}

llvm::SmallVector<std::string, 8> collectDirectCalleesForFunction(
    const llvm::Function &F) {
  llvm::SmallVector<std::string, 8> callees;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->isDeclaration() ||
          callee->hasFnAttribute("omill.localized_continuation_shim")) {
        continue;
      }
      if (!llvm::is_contained(callees, callee->getName().str()))
        callees.push_back(callee->getName().str());
    }
  }
  return callees;
}

}  // namespace omill::virtual_model::detail

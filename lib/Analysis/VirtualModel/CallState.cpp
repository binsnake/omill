#include "Analysis/VirtualModel/Internal.h"

#include <llvm/IR/DataLayout.h>

namespace omill::virtual_model::detail {

static constexpr unsigned kMaxPreCallFactScanInstructions = 40;

LocalCallSiteState computeLocalFactsBeforeCall(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &base_slot_facts,
    const std::map<unsigned, VirtualValueExpr> &base_stack_facts,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  LocalCallSiteState state{base_slot_facts, base_stack_facts};
  auto *block = call.getParent();
  if (!block)
    return state;
  const auto native_sp_offset = nativeStackPointerOffsetForValue(&call);
  auto caller_name = call.getFunction() ? call.getFunction()->getName().str()
                                        : std::string("<null>");
  auto callee_name = call.getCalledFunction()
                         ? call.getCalledFunction()->getName().str()
                         : std::string("<indirect>");
  vmModelStageDebugLog("precall-facts: caller=" + caller_name + " callee=" +
                       callee_name + " step=begin");

  auto record_value = [&](llvm::Value *value) {
    auto expr = summarizeValueExpr(value, dl);
    return specializeExprToFixpoint(expr, state.slot_facts, &state.stack_facts,
                                    &caller_argument_map, slot_ids,
                                    stack_cell_ids);
  };

  unsigned inst_index = 0;
  for (auto &I : *block) {
    if (&I == &call)
      break;
    vmModelStageDebugLog("precall-facts: caller=" + caller_name + " callee=" +
                         callee_name + " inst=" +
                         llvm::Twine(inst_index).str() + " opcode=" +
                         I.getOpcodeName());
    if (inst_index >= kMaxPreCallFactScanInstructions) {
      vmModelStageDebugLog("precall-facts: caller=" + caller_name +
                           " callee=" + callee_name +
                           " step=budget-exceeded");
      return state;
    }
    ++inst_index;

    if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto width = dl.getTypeStoreSize(store->getValueOperand()->getType());
      if (width.isScalable())
        continue;
      if (auto slot = extractStateSlotSummary(store->getPointerOperand(),
                                              width.getFixedValue(), dl)) {
        auto slot_id = lookupSlotIdForSummary(*slot, slot_ids);
        if (!slot_id)
          continue;
        state.slot_facts[*slot_id] = record_value(store->getValueOperand());
        continue;
      }
      auto pointer_expr = summarizeValueExpr(store->getPointerOperand(), dl);
      if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                      width.getFixedValue(),
                                                      native_sp_offset)) {
        auto cell_id = lookupStackCellIdForSummary(*cell, stack_cell_ids);
        if (!cell_id)
          continue;
        state.stack_facts[*cell_id] = record_value(store->getValueOperand());
      }
      continue;
    }

    auto *cb = llvm::dyn_cast<llvm::CallBase>(&I);
    if (!cb)
      continue;
    auto *callee = cb->getCalledFunction();
    if (!callee || !isRemillWriteMemoryIntrinsic(*callee) || cb->arg_size() < 3)
      continue;

    unsigned width_bits = remillMemoryBitWidth(callee->getName()).value_or(0);
    unsigned width_bytes = width_bits / 8;
    auto address_expr = summarizeValueExpr(cb->getArgOperand(1), dl);
    if (auto cell = extractStackCellSummaryFromExpr(address_expr, width_bytes,
                                                    native_sp_offset)) {
      auto cell_id = lookupStackCellIdForSummary(*cell, stack_cell_ids);
      if (!cell_id)
        continue;
      state.stack_facts[*cell_id] = record_value(cb->getArgOperand(2));
    }
  }

  specializeFactStateToFixpoint(state.slot_facts, state.stack_facts,
                                &caller_argument_map, slot_ids,
                                stack_cell_ids);
  vmModelStageDebugLog("precall-facts: caller=" + caller_name + " callee=" +
                       callee_name + " step=done");
  return state;
}

VirtualValueExpr summarizeSpecializedCallArg(
    llvm::CallBase &call, unsigned arg_index, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  if (arg_index >= call.arg_size())
    return VirtualValueExpr{};
  auto expr = summarizeValueExpr(call.getArgOperand(arg_index), dl);
  return specializeExprToFixpoint(expr, caller_outgoing, &caller_outgoing_stack,
                                  &caller_argument_map, slot_ids,
                                  stack_cell_ids);
}

std::map<unsigned, VirtualValueExpr> buildSpecializedCallArgumentMap(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  std::map<unsigned, VirtualValueExpr> specialized_args;
  auto caller_name = call.getFunction() ? call.getFunction()->getName().str()
                                        : std::string("<null>");
  auto callee_name = call.getCalledFunction()
                         ? call.getCalledFunction()->getName().str()
                         : std::string("<indirect>");
  for (unsigned arg_index = 0; arg_index < call.arg_size(); ++arg_index) {
    vmModelStageDebugLog("call-arg-specialize: caller=" + caller_name +
                         " callee=" + callee_name + " arg=" +
                         llvm::Twine(arg_index).str() + " step=begin");
    specialized_args.emplace(
        arg_index,
        summarizeSpecializedCallArg(call, arg_index, dl, slot_ids,
                                    stack_cell_ids, caller_outgoing,
                                    caller_outgoing_stack, caller_argument_map));
    vmModelStageDebugLog("call-arg-specialize: caller=" + caller_name +
                         " callee=" + callee_name + " arg=" +
                         llvm::Twine(arg_index).str() + " step=done");
  }
  return specialized_args;
}

}  // namespace omill::virtual_model::detail

#include "omill/Passes/VirtualCFGMaterialization.h"

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <algorithm>
#include <cstdlib>
#include <map>
#include <set>

#include "omill/Analysis/VirtualMachineModel.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/BC/TraceLiftAnalysis.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/ProtectedBoundaryUtils.h"
#include "omill/Utils/StateFieldMap.h"
#if OMILL_ENABLE_Z3
#include "omill/Utils/TranslationValidator.h"
#include <z3++.h>
#endif

namespace omill {

namespace {

struct MaterializationResult {
  bool changed = false;
  llvm::SmallPtrSet<llvm::Function *, 8> changed_functions;
  llvm::SmallVector<std::string, 8> diagnostics;
};

struct ResolvedTarget {
  llvm::Function *function = nullptr;
  uint64_t pc = 0;
  bool store_pc_to_state = false;
};

struct BoundaryTargetSummary {
  std::string name;
  std::optional<uint64_t> canonical_target_va;
};

static bool isDispatchIntrinsicName(llvm::StringRef name) {
  return name == "__omill_dispatch_call" || name == "__omill_dispatch_jump";
}

static bool genericDebugEnabled() {
  const char *v = std::getenv("OMILL_DEBUG_GENERIC_STATIC_DEVIRT");
  return v && v[0] != '\0';
}

static void genericDebugLog(llvm::StringRef message) {
  if (!genericDebugEnabled())
    return;
  llvm::errs() << "[omill.generic] " << message << "\n";
}

static bool isBoundaryFunctionName(llvm::StringRef name) {
  return name.starts_with("vm_entry_");
}

static const VirtualHandlerSummary *lookupHandlerByVA(const VirtualMachineModel &model,
                                                      uint64_t entry_va) {
  for (const auto &handler : model.handlers()) {
    if (handler.entry_va.has_value() && *handler.entry_va == entry_va)
      return &handler;
  }
  return nullptr;
}

static llvm::Function *lookupLiftedTargetByPC(llvm::Module &M, uint64_t pc) {
  if (auto *fn = M.getFunction(liftedFunctionName(pc)))
    return fn;

  auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *fn = M.getFunction(block_name))
    return fn;

  auto trace_block_name =
      (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  return M.getFunction(trace_block_name);
}

static bool isTerminalMissingBlockStub(const llvm::Function &F) {
  const llvm::Function *missing_block = nullptr;
  unsigned direct_calls = 0;

  for (const auto &BB : F) {
    for (const auto &I : BB) {
      const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;
      auto *callee = CB->getCalledFunction();
      if (!callee)
        return false;
      ++direct_calls;
      if (callee->getName() != "__remill_missing_block")
        return false;
      missing_block = callee;
    }
  }

  return missing_block != nullptr && direct_calls == 1;
}

static bool isSyntheticBlockLikeFunctionName(llvm::StringRef name) {
  return name.starts_with("blk_") || name.starts_with("block_");
}

static std::optional<unsigned> lookupProgramCounterOffset(llvm::Module &M) {
  StateFieldMap field_map(M);
  if (auto pc = field_map.fieldByName("PC"))
    return pc->offset;
  return std::nullopt;
}

static void maybeStoreProgramCounter(llvm::IRBuilder<> &builder,
                                     llvm::Value *state_arg,
                                     const ResolvedTarget &target) {
  if (!target.store_pc_to_state || !state_arg || !state_arg->getType()->isPointerTy())
    return;

  auto *module = builder.GetInsertBlock()->getModule();
  if (!module)
    return;
  auto pc_offset = lookupProgramCounterOffset(*module);
  if (!pc_offset)
    return;

  auto &ctx = builder.getContext();
  auto *pc_gep = builder.CreateGEP(
      llvm::Type::getInt8Ty(ctx), state_arg,
      llvm::ConstantInt::get(llvm::Type::getInt64Ty(ctx), *pc_offset));
  builder.CreateStore(
      llvm::ConstantInt::get(llvm::Type::getInt64Ty(ctx), target.pc), pc_gep);
}

static const VirtualBoundaryInfo *lookupBoundaryByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va) {
  for (const auto &boundary : model.boundaries()) {
    if (boundary.entry_va.has_value() && *boundary.entry_va == entry_va)
      return &boundary;
  }
  return nullptr;
}

static std::optional<BoundaryTargetSummary> lookupBoundaryTargetSummary(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    uint64_t pc) {
  if (const auto *boundary = lookupBoundaryByEntryVA(model, pc)) {
    return BoundaryTargetSummary{boundary->name, boundary->target_va};
  }

  auto fallback_name = std::string("vm_entry_") + llvm::utohexstr(pc, true);
  if (const auto *boundary = model.lookupBoundary(fallback_name)) {
    return BoundaryTargetSummary{boundary->name, boundary->target_va};
  }

  if (auto boundary = classifyProtectedBoundary(binary_memory, pc)) {
    if (const auto *existing =
            lookupBoundaryByEntryVA(model, boundary->entry_va)) {
      return BoundaryTargetSummary{
          existing->name,
          existing->target_va.has_value()
              ? existing->target_va
              : std::optional<uint64_t>(boundary->canonical_target_va)};
    }
    return BoundaryTargetSummary{fallback_name, boundary->canonical_target_va};
  }

  return std::nullopt;
}

static std::optional<uint64_t> evaluateVirtualExprImpl(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    llvm::SmallDenseSet<unsigned, 8> &visiting_slots,
    llvm::SmallDenseSet<unsigned, 8> &visiting_cells) {
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
                                         visiting_slots, visiting_cells);
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
                                         visiting_slots, visiting_cells);
    visiting_cells.erase(cell_id);
    return value;
  };

  auto fold_binary = [&](auto fn) -> std::optional<uint64_t> {
    if (expr.operands.size() != 2)
      return std::nullopt;
    auto lhs = evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                       visiting_slots, visiting_cells);
    auto rhs = evaluateVirtualExprImpl(expr.operands[1], facts, stack_facts,
                                       visiting_slots, visiting_cells);
    if (!lhs || !rhs)
      return std::nullopt;
    return fn(*lhs, *rhs);
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
      return fold_binary([](uint64_t a, uint64_t b) { return b < 64 ? (a << b) : 0ULL; });
    case VirtualExprKind::kLShr:
      return fold_binary([](uint64_t a, uint64_t b) { return b < 64 ? (a >> b) : 0ULL; });
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
                                      visiting_slots, visiting_cells)) {
        return evaluateVirtualExprImpl(expr.operands[*cond ? 1 : 2], facts,
                                       stack_facts, visiting_slots,
                                       visiting_cells);
      }
      return std::nullopt;
    case VirtualExprKind::kPhi:
      if (expr.operands.empty())
        return std::nullopt;
      {
        auto first =
            evaluateVirtualExprImpl(expr.operands.front(), facts, stack_facts,
                                    visiting_slots, visiting_cells);
        if (!first)
          return std::nullopt;
        for (size_t i = 1; i < expr.operands.size(); ++i) {
          auto other = evaluateVirtualExprImpl(expr.operands[i], facts,
                                               stack_facts, visiting_slots,
                                               visiting_cells);
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

static std::optional<uint64_t> evaluateVirtualExpr(
    const VirtualValueExpr &expr,
    const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts = {}) {
  llvm::SmallDenseSet<unsigned, 8> visiting_slots;
  llvm::SmallDenseSet<unsigned, 8> visiting_cells;
  return evaluateVirtualExprImpl(expr, facts, stack_facts, visiting_slots,
                                 visiting_cells);
}

static bool isExecutableTargetAddress(const BinaryMemoryMap &binary_memory,
                                      uint64_t pc) {
  return binary_memory.isExecutable(pc, 1);
}

static ResolvedTarget resolveTarget(llvm::Module &M,
                                    const BinaryMemoryMap &binary_memory,
                                    const VirtualMachineModel &model,
                                    llvm::FunctionType *fn_ty, uint64_t pc,
                                    llvm::SmallVectorImpl<std::string> *diagnostics) {
  ResolvedTarget resolved;
  resolved.pc = pc;
  if (const auto *target_summary = lookupHandlerByVA(model, pc)) {
    resolved.function = M.getFunction(target_summary->function_name);
    if (resolved.function && isTerminalMissingBlockStub(*resolved.function)) {
      resolved.function = M.getFunction("__remill_missing_block");
      resolved.store_pc_to_state = (resolved.function != nullptr);
      if (diagnostics) {
        diagnostics->push_back(
            "missing-block-collapse target=0x" + llvm::utohexstr(pc) +
            " stub=" + target_summary->function_name);
      }
    }
    return resolved;
  }

  if (auto *lifted_target = lookupLiftedTargetByPC(M, pc)) {
    if (isTerminalMissingBlockStub(*lifted_target)) {
      resolved.function = M.getFunction("__remill_missing_block");
      resolved.store_pc_to_state = (resolved.function != nullptr);
      if (diagnostics) {
        diagnostics->push_back(
            "missing-block-collapse target=0x" + llvm::utohexstr(pc) +
            " stub=" + lifted_target->getName().str());
      }
      return resolved;
    }

    resolved.function = lifted_target;
    if (diagnostics) {
      diagnostics->push_back(
          "lifted target=0x" + llvm::utohexstr(pc) + " -> " +
          resolved.function->getName().str());
    }
    return resolved;
  }

  if (auto boundary = lookupBoundaryTargetSummary(model, binary_memory, pc)) {
    if (boundary->canonical_target_va.has_value()) {
      if (auto *continued_target =
              lookupLiftedTargetByPC(M, *boundary->canonical_target_va)) {
        resolved.function = continued_target;
        resolved.pc = *boundary->canonical_target_va;
        if (diagnostics) {
          diagnostics->push_back(
              "boundary-continue target=0x" + llvm::utohexstr(pc) + " -> " +
              resolved.function->getName().str() + " continued_pc=0x" +
              llvm::utohexstr(*boundary->canonical_target_va));
        }
        return resolved;
      }
    }

    ProtectedBoundaryInfo info;
    info.entry_va = pc;
    info.canonical_target_va = boundary->canonical_target_va.value_or(0);
    info.is_vm_entry_stub = true;
    auto callee = getOrInsertProtectedBoundaryDecl(M, fn_ty, info);
    resolved.function = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (diagnostics) {
      diagnostics->push_back(
          "boundary target=0x" + llvm::utohexstr(pc) + " -> " +
          (resolved.function ? resolved.function->getName().str()
                             : std::string("<non-function>")));
    }
    return resolved;
  }

  if (auto boundary = classifyProtectedBoundary(binary_memory, pc)) {
    auto callee = getOrInsertProtectedBoundaryDecl(M, fn_ty, *boundary);
    resolved.function = llvm::dyn_cast<llvm::Function>(callee.getCallee());
    if (diagnostics) {
      diagnostics->push_back(
          "boundary target=0x" + llvm::utohexstr(pc) + " -> " +
          (resolved.function ? resolved.function->getName().str()
                             : std::string("<non-function>")));
    }
    return resolved;
  }

  if (diagnostics) {
    diagnostics->push_back("unresolved constant target=0x" +
                           llvm::utohexstr(pc) + " no_handler_no_boundary");
  }
  return resolved;
}

static bool lowerToDirectCall(llvm::CallInst *dispatch_call, llvm::Function *target_fn,
                              uint64_t target_pc, bool is_jump,
                              bool store_pc_to_state = false) {
  if (dispatch_call->arg_size() < 3 || !target_fn)
    return false;

  auto *pc_val = llvm::ConstantInt::get(
      llvm::Type::getInt64Ty(dispatch_call->getContext()), target_pc);
  if (store_pc_to_state) {
    llvm::IRBuilder<> builder(dispatch_call);
    maybeStoreProgramCounter(
        builder, dispatch_call->getArgOperand(0),
        ResolvedTarget{target_fn, target_pc, true});
  }
  dispatch_call->setCalledFunction(target_fn);
  dispatch_call->setArgOperand(1, pc_val);
  if (is_jump) {
    if (auto *ret = llvm::dyn_cast_or_null<llvm::ReturnInst>(
            dispatch_call->getNextNonDebugInstruction())) {
      dispatch_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
      if (!dispatch_call->getType()->isVoidTy())
        ret->setOperand(0, dispatch_call);
    }
  }
  return true;
}

static bool lowerSelectDispatchToBranches(llvm::CallInst *dispatch_call,
                                          llvm::Value *condition,
                                          const ResolvedTarget &true_target,
                                          const ResolvedTarget &false_target) {
  if (!dispatch_call || !dispatch_call->getParent() || !condition ||
      !condition->getType()->isIntegerTy(1) || !true_target.function ||
      !false_target.function || true_target.function == false_target.function) {
    return false;
  }

  auto *orig_bb = dispatch_call->getParent();
  auto *parent_fn = orig_bb->getParent();
  auto &ctx = dispatch_call->getContext();
  auto *cont_bb = orig_bb->splitBasicBlock(dispatch_call->getIterator(),
                                           orig_bb->getName() + ".cont");
  orig_bb->getTerminator()->eraseFromParent();

  auto *then_bb = llvm::BasicBlock::Create(ctx, orig_bb->getName() + ".then",
                                           parent_fn, cont_bb);
  auto *else_bb = llvm::BasicBlock::Create(ctx, orig_bb->getName() + ".else",
                                           parent_fn, cont_bb);

  llvm::IRBuilder<> entry_builder(orig_bb);
  entry_builder.CreateCondBr(condition, then_bb, else_bb);

  llvm::CallInst *then_call = nullptr;
  llvm::CallInst *else_call = nullptr;
  auto *pc_ty = llvm::Type::getInt64Ty(ctx);

  auto build_direct_call = [&](llvm::BasicBlock *bb, const ResolvedTarget &target,
                               llvm::CallInst *&out_call) {
    llvm::IRBuilder<> builder(bb);
    llvm::SmallVector<llvm::Value *, 8> args(dispatch_call->args());
    args[1] = llvm::ConstantInt::get(pc_ty, target.pc);
    maybeStoreProgramCounter(builder, args[0], target);
    out_call = builder.CreateCall(target.function, args);
    builder.CreateBr(cont_bb);
  };

  build_direct_call(then_bb, true_target, then_call);
  build_direct_call(else_bb, false_target, else_call);

  if (!dispatch_call->getType()->isVoidTy()) {
    llvm::IRBuilder<> cont_builder(&cont_bb->front());
    auto *phi = cont_builder.CreatePHI(dispatch_call->getType(), 2);
    phi->addIncoming(then_call, then_bb);
    phi->addIncoming(else_call, else_bb);
    dispatch_call->replaceAllUsesWith(phi);
  }

  dispatch_call->eraseFromParent();
  return true;
}

static bool lowerChoiceDispatchToSwitch(
    llvm::CallInst *dispatch_call, llvm::Value *dispatch_value,
    llvm::ArrayRef<ResolvedTarget> targets) {
  if (!dispatch_call || !dispatch_call->getParent() || !dispatch_value ||
      !dispatch_value->getType()->isIntegerTy() || targets.size() < 2)
    return false;
  for (const auto &target : targets) {
    if (!target.function)
      return false;
  }

  auto *orig_bb = dispatch_call->getParent();
  auto *parent_fn = orig_bb->getParent();
  auto &ctx = dispatch_call->getContext();
  auto *default_bb = orig_bb->splitBasicBlock(dispatch_call->getIterator(),
                                              orig_bb->getName() + ".default");
  auto *after_bb = default_bb->splitBasicBlock(
      std::next(default_bb->begin()), default_bb->getName() + ".cont");
  orig_bb->getTerminator()->eraseFromParent();

  llvm::IRBuilder<> entry_builder(orig_bb);
  auto *switch_inst = entry_builder.CreateSwitch(
      dispatch_value, default_bb, static_cast<unsigned>(targets.size()));

  llvm::SmallVector<llvm::CallInst *, 4> case_calls;
  llvm::SmallVector<llvm::BasicBlock *, 4> case_blocks;
  case_calls.reserve(targets.size());
  case_blocks.reserve(targets.size());
  auto *pc_ty = llvm::Type::getInt64Ty(ctx);

  for (const auto &target : targets) {
    auto *case_bb = llvm::BasicBlock::Create(
        ctx, orig_bb->getName() + ".case", parent_fn, after_bb);
    llvm::IRBuilder<> builder(case_bb);
    llvm::SmallVector<llvm::Value *, 8> args(dispatch_call->args());
    args[1] = llvm::ConstantInt::get(pc_ty, target.pc);
    maybeStoreProgramCounter(builder, args[0], target);
    auto *direct_call = builder.CreateCall(target.function, args);
    builder.CreateBr(after_bb);
    auto *case_value = llvm::ConstantInt::get(
        llvm::cast<llvm::IntegerType>(dispatch_value->getType()), target.pc);
    switch_inst->addCase(case_value, case_bb);
    case_calls.push_back(direct_call);
    case_blocks.push_back(case_bb);
  }

  if (!dispatch_call->getType()->isVoidTy()) {
    llvm::IRBuilder<> after_builder(&after_bb->front());
    auto *phi = after_builder.CreatePHI(dispatch_call->getType(),
                                        static_cast<unsigned>(targets.size()));
    for (size_t i = 0; i < case_calls.size(); ++i)
      phi->addIncoming(case_calls[i], case_blocks[i]);
    dispatch_call->replaceAllUsesWith(phi);
  }

  dispatch_call->eraseFromParent();
  default_bb->getTerminator()->eraseFromParent();
  llvm::IRBuilder<> default_builder(default_bb);
  default_builder.CreateUnreachable();

  return true;
}

static std::optional<uint64_t> resolveDispatchFromFacts(
    const VirtualMachineModel &model, const VirtualHandlerSummary &summary,
    const VirtualDispatchSummary &dispatch,
    llvm::SmallVectorImpl<std::string> *diagnostics) {
  if (auto resolved = evaluateVirtualExpr(dispatch.target, summary.outgoing_facts,
                                          summary.outgoing_stack_facts))
    return resolved;

  if (const auto *region = model.lookupRegionForHandler(summary.function_name)) {
    if (auto resolved =
            evaluateVirtualExpr(dispatch.target, region->outgoing_facts,
                                region->outgoing_stack_facts)) {
      if (diagnostics) {
        diagnostics->push_back("region-fallback " + summary.function_name +
                               " region=" + std::to_string(region->id) +
                               " target=0x" + llvm::utohexstr(*resolved));
      }
      return resolved;
    }
    if (auto resolved =
            evaluateVirtualExpr(dispatch.target, region->incoming_facts,
                                region->incoming_stack_facts)) {
      if (diagnostics) {
        diagnostics->push_back("region-in-fallback " + summary.function_name +
                               " region=" + std::to_string(region->id) +
                               " target=0x" + llvm::utohexstr(*resolved));
      }
      return resolved;
    }
  }

  return std::nullopt;
}

static std::optional<unsigned> lookupSummaryNamedSlotId(
    const VirtualHandlerSummary &summary, llvm::StringRef base_name) {
  for (const auto &slot : summary.state_slots) {
    if (slot.base_name != base_name || slot.offset != 0 ||
        !slot.canonical_id.has_value()) {
      continue;
    }
    return slot.canonical_id;
  }
  return std::nullopt;
}

static const VirtualSlotFact *lookupSlotFactById(
    llvm::ArrayRef<VirtualSlotFact> facts, unsigned slot_id) {
  auto it = llvm::find_if(facts, [&](const VirtualSlotFact &fact) {
    return fact.slot_id == slot_id;
  });
  if (it == facts.end())
    return nullptr;
  return &*it;
}

static std::optional<uint64_t> resolveTerminalNextPcFromFacts(
    const VirtualHandlerSummary &summary, const BinaryMemoryMap &binary_memory,
    llvm::SmallVectorImpl<std::string> *diagnostics) {
  auto next_pc_slot_id = lookupSummaryNamedSlotId(summary, "NEXT_PC");
  if (!next_pc_slot_id)
    return std::nullopt;

  const auto *next_pc_fact = lookupSlotFactById(summary.outgoing_facts,
                                                *next_pc_slot_id);
  if (!next_pc_fact)
    return std::nullopt;

  struct FactStateRef {
    llvm::ArrayRef<VirtualSlotFact> slots;
    llvm::ArrayRef<VirtualStackFact> stack;
    llvm::StringRef name;
  };

  const FactStateRef states[] = {
      {summary.outgoing_facts, summary.outgoing_stack_facts, "out/out"},
      {summary.outgoing_facts, summary.incoming_stack_facts, "out/in-stack"},
      {summary.incoming_facts, summary.outgoing_stack_facts, "in/out-stack"},
      {summary.incoming_facts, summary.incoming_stack_facts, "in/in"},
  };

  std::optional<uint64_t> first_resolved;
  for (const auto &state : states) {
    if (auto resolved =
            evaluateVirtualExpr(next_pc_fact->value, state.slots, state.stack)) {
      if (diagnostics) {
        diagnostics->push_back("terminal-next-pc " + summary.function_name +
                               " state=" + state.name.str() + " target=0x" +
                               llvm::utohexstr(*resolved));
      }
      if (!first_resolved)
        first_resolved = resolved;
      if (isExecutableTargetAddress(binary_memory, *resolved))
        return resolved;
    }
  }

  return first_resolved;
}

static void collectExprSlotIds(const VirtualValueExpr &expr,
                               std::set<unsigned> &slot_ids) {
  if (expr.slot_id.has_value())
    slot_ids.insert(*expr.slot_id);
  for (const auto &operand : expr.operands)
    collectExprSlotIds(operand, slot_ids);
}

static void collectExprStackCellIds(const VirtualValueExpr &expr,
                                    std::set<unsigned> &cell_ids) {
  if (expr.stack_cell_id.has_value())
    cell_ids.insert(*expr.stack_cell_id);
  for (const auto &operand : expr.operands)
    collectExprStackCellIds(operand, cell_ids);
}

static const VirtualSlotFact *findFact(llvm::ArrayRef<VirtualSlotFact> facts,
                                       unsigned slot_id) {
  auto it = std::find_if(facts.begin(), facts.end(),
                         [&](const VirtualSlotFact &fact) {
                           return fact.slot_id == slot_id;
                         });
  return it == facts.end() ? nullptr : &*it;
}

static const VirtualStackFact *findStackFact(llvm::ArrayRef<VirtualStackFact> facts,
                                             unsigned cell_id) {
  auto it = std::find_if(facts.begin(), facts.end(),
                         [&](const VirtualStackFact &fact) {
                           return fact.cell_id == cell_id;
                         });
  return it == facts.end() ? nullptr : &*it;
}

static std::map<unsigned, VirtualSlotFact> collectCallsiteConstantFacts(
    llvm::CallInst &call, const VirtualMachineModel &model) {
  std::map<unsigned, VirtualSlotFact> facts;
  const auto &dl = call.getModule()->getDataLayout();

  for (auto it = call.getParent()->begin(); &*it != &call; ++it) {
    auto *store = llvm::dyn_cast<llvm::StoreInst>(&*it);
    if (!store)
      continue;
    auto size = dl.getTypeStoreSize(store->getValueOperand()->getType());
    if (size.isScalable())
      continue;

    int64_t offset = 0;
    auto *base = llvm::GetPointerBaseWithConstantOffset(store->getPointerOperand(),
                                                        offset, dl, true);
    auto *arg = llvm::dyn_cast_or_null<llvm::Argument>(base);
    if (!arg || arg->getArgNo() != 0)
      continue;

    auto *constant = llvm::dyn_cast<llvm::ConstantInt>(store->getValueOperand());
    if (!constant)
      continue;

    const VirtualStateSlotInfo *slot_info = nullptr;
    for (const auto &slot : model.slots()) {
      if (slot.base_name == "arg0" && slot.offset == offset &&
          slot.width == size.getFixedValue()) {
        slot_info = &slot;
        break;
      }
    }
    if (!slot_info)
      continue;

    VirtualValueExpr expr;
    expr.kind = VirtualExprKind::kConstant;
    expr.bit_width = constant->getBitWidth();
    expr.complete = true;
    expr.constant = constant->getZExtValue();
    facts[slot_info->id] = VirtualSlotFact{slot_info->id, std::move(expr)};
  }

  return facts;
}

static std::optional<VirtualSlotFact> asConstantFact(
    const VirtualSlotFact &fact) {
  if (!fact.value.constant.has_value())
    return std::nullopt;
  return VirtualSlotFact{
      fact.slot_id,
      VirtualValueExpr{VirtualExprKind::kConstant, fact.value.bit_width, true,
                       fact.value.constant, std::nullopt, std::nullopt,
                       std::nullopt, std::nullopt, std::nullopt, std::nullopt,
                       {}}};
}

static std::optional<VirtualStackFact> asConstantStackFact(
    const VirtualStackFact &fact) {
  if (!fact.value.constant.has_value())
    return std::nullopt;
  return VirtualStackFact{
      fact.cell_id,
      VirtualValueExpr{VirtualExprKind::kConstant, fact.value.bit_width, true,
                       fact.value.constant, std::nullopt, std::nullopt,
                       std::nullopt, std::nullopt, std::nullopt, std::nullopt,
                       {}}};
}

static std::string serializeSpecializationFacts(
    llvm::ArrayRef<VirtualSlotFact> facts) {
  std::vector<VirtualSlotFact> ordered(facts.begin(), facts.end());
  std::sort(ordered.begin(), ordered.end(),
            [](const VirtualSlotFact &lhs, const VirtualSlotFact &rhs) {
              return lhs.slot_id < rhs.slot_id;
            });

  std::string encoded;
  llvm::raw_string_ostream os(encoded);
  bool first = true;
  for (const auto &fact : ordered) {
    if (!fact.value.constant.has_value())
      continue;
    if (!first)
      os << ",";
    first = false;
    os << fact.slot_id << ":" << fact.value.bit_width << "="
       << llvm::utohexstr(*fact.value.constant);
  }
  return os.str();
}

static std::string serializeSpecializationStackFacts(
    llvm::ArrayRef<VirtualStackFact> facts) {
  std::vector<VirtualStackFact> ordered(facts.begin(), facts.end());
  std::sort(ordered.begin(), ordered.end(),
            [](const VirtualStackFact &lhs, const VirtualStackFact &rhs) {
              return lhs.cell_id < rhs.cell_id;
            });

  std::string encoded;
  llvm::raw_string_ostream os(encoded);
  bool first = true;
  for (const auto &fact : ordered) {
    if (!fact.value.constant.has_value())
      continue;
    if (!first)
      os << ",";
    first = false;
    os << fact.cell_id << ":" << fact.value.bit_width << "="
       << llvm::utohexstr(*fact.value.constant);
  }
  return os.str();
}

static std::string specializedCloneName(llvm::StringRef base_name,
                                        uint64_t root_va,
                                        llvm::ArrayRef<VirtualSlotFact> facts,
                                        llvm::ArrayRef<VirtualStackFact> stack_facts) {
  auto facts_key = serializeSpecializationFacts(facts);
  auto stack_facts_key = serializeSpecializationStackFacts(stack_facts);
  auto hash = llvm::hash_combine(facts_key, stack_facts_key);
  return (llvm::Twine(base_name) + "__gspec_" + llvm::Twine::utohexstr(root_va) +
          "_" + llvm::Twine::utohexstr(static_cast<uint64_t>(hash)))
      .str();
}

static llvm::Function *getOrCreateSpecializedClone(
    llvm::Module &M, llvm::Function &base_fn, uint64_t root_va,
    llvm::ArrayRef<VirtualSlotFact> facts,
    llvm::ArrayRef<VirtualStackFact> stack_facts, bool *created = nullptr) {
  auto clone_name =
      specializedCloneName(base_fn.getName(), root_va, facts, stack_facts);
  if (auto *existing = M.getFunction(clone_name)) {
    if (created)
      *created = false;
    return existing;
  }

  llvm::ValueToValueMapTy vmap;
  auto *clone = llvm::CloneFunction(&base_fn, vmap);
  clone->setName(clone_name);
  clone->setLinkage(llvm::GlobalValue::InternalLinkage);
  clone->addFnAttr("omill.virtual_specialized", "1");
  clone->addFnAttr("omill.virtual_specialization.root_va",
                   llvm::utohexstr(root_va));
  clone->addFnAttr("omill.virtual_specialization.facts",
                   serializeSpecializationFacts(facts));
  clone->addFnAttr("omill.virtual_specialization.stack_facts",
                   serializeSpecializationStackFacts(stack_facts));
  if (clone->hasFnAttribute("omill.output_root"))
    clone->removeFnAttr("omill.output_root");
  if (created)
    *created = true;
  return clone;
}

static std::optional<uint64_t> findRootVAForHandler(
    const VirtualMachineModel &model, llvm::StringRef handler_name) {
  for (const auto &slice : model.rootSlices()) {
    if (llvm::is_contained(slice.reachable_handler_names, handler_name.str()))
      return slice.root_va;
  }
  return std::nullopt;
}

static std::optional<unsigned> lookupNativeStackPointerOffset(llvm::Module &M) {
  StateFieldMap field_map(M);
  for (const char *sp_name : {"RSP", "SP", "sp"}) {
    if (auto field = field_map.fieldByName(sp_name))
      return field->offset;
  }
  return std::nullopt;
}

static std::optional<uint64_t> inferLiftedCallContinuationPc(llvm::CallBase &call) {
  auto *callee = call.getCalledFunction();
  if (!callee || !hasLiftedSignature(*callee))
    return std::nullopt;

  for (auto *I = call.getNextNode(); I; I = I->getNextNode()) {
    if (auto *next_call = llvm::dyn_cast<llvm::CallBase>(I)) {
      auto *next_callee = next_call->getCalledFunction();
      if (!next_callee || !hasLiftedSignature(*next_callee))
        continue;
      auto *next_call_inst = llvm::dyn_cast<llvm::CallInst>(next_call);
      if (!next_call_inst ||
          next_call_inst->getTailCallKind() != llvm::CallInst::TCK_MustTail)
        continue;
      if (next_call->arg_size() < 3 || next_call->getArgOperand(2) != &call)
        continue;
      auto *pc = llvm::dyn_cast<llvm::ConstantInt>(next_call->getArgOperand(1));
      if (!pc)
        return std::nullopt;
      return pc->getZExtValue();
    }

    if (I->isTerminator())
      break;
  }

  return std::nullopt;
}

static std::map<unsigned, VirtualStackFact> collectCallsiteConstantStackFacts(
    llvm::CallInst &call, const VirtualMachineModel &model) {
  std::map<unsigned, VirtualStackFact> facts;

  auto continuation_pc = inferLiftedCallContinuationPc(call);
  if (!continuation_pc)
    return facts;

  auto *module = call.getModule();
  if (!module)
    return facts;
  auto sp_offset = lookupNativeStackPointerOffset(*module);
  if (!sp_offset)
    return facts;

  for (const auto &cell : model.stackCells()) {
    if (!cell.base_from_argument || cell.base_from_alloca ||
        cell.base_name != "arg0" ||
        cell.base_offset != static_cast<int64_t>(*sp_offset) ||
        cell.cell_offset != 0) {
      continue;
    }
    VirtualValueExpr expr;
    expr.kind = VirtualExprKind::kConstant;
    expr.bit_width = cell.width * 8;
    expr.complete = true;
    expr.constant = *continuation_pc;
    facts[cell.id] = VirtualStackFact{cell.id, std::move(expr)};
  }

  return facts;
}

static bool specializeReachableCallsites(
    llvm::Module &M, const VirtualMachineModel &model,
    llvm::SmallVectorImpl<std::string> *diagnostics,
    std::map<std::pair<uint64_t, std::string>, unsigned> &variants_per_source,
    unsigned &total_specialized_functions,
    llvm::SmallPtrSetImpl<llvm::Function *> &changed_functions) {
  constexpr unsigned kMaxVariantsPerSource = 8;
  constexpr unsigned kMaxSpecializedPerRootSlice = 64;

  bool changed = false;
  for (auto &caller_fn : M) {
    if (caller_fn.isDeclaration())
      continue;

    const auto *caller_summary = model.lookupHandler(caller_fn.getName());
    if (!caller_summary)
      continue;
    auto root_va = findRootVAForHandler(model, caller_fn.getName());
    if (!root_va)
      continue;

    for (auto &BB : caller_fn) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee_fn = call->getCalledFunction();
        if (!callee_fn || callee_fn->isDeclaration())
          continue;
        if (isDispatchIntrinsicName(callee_fn->getName()) ||
            isBoundaryFunctionName(callee_fn->getName()))
          continue;

        const auto *callee_summary = model.lookupHandler(callee_fn->getName());
        if (!callee_summary || callee_summary->is_specialized)
          continue;

        bool has_unresolved_dispatch = std::any_of(
            callee_summary->dispatches.begin(), callee_summary->dispatches.end(),
            [](const VirtualDispatchSummary &dispatch) {
              return !dispatch.unresolved_reason.empty() ||
                     dispatch.successors.empty() ||
                     (dispatch.is_jump && dispatch.successors.size() > 1);
            });
        if (!has_unresolved_dispatch)
          continue;

        std::set<unsigned> required_slots;
        std::set<unsigned> required_stack_cells;
        bool needs_stack_fact_specialization = false;
        for (const auto &dispatch : callee_summary->dispatches) {
          if (dispatch.unresolved_reason.empty() && !dispatch.successors.empty())
            if (!(dispatch.is_jump && dispatch.successors.size() > 1))
              continue;
          needs_stack_fact_specialization = true;
          const auto &relevant_expr =
              dispatch.specialized_target_source !=
                      VirtualDispatchResolutionSource::kUnknown
                  ? dispatch.specialized_target
                  : dispatch.target;
          collectExprSlotIds(relevant_expr, required_slots);
          collectExprStackCellIds(relevant_expr, required_stack_cells);
        }
        for (unsigned slot_id : required_slots) {
          if (const auto *fact =
                  findFact(callee_summary->outgoing_facts, slot_id)) {
            collectExprStackCellIds(fact->value, required_stack_cells);
          }
          if (const auto *fact =
                  findFact(callee_summary->incoming_facts, slot_id)) {
            collectExprStackCellIds(fact->value, required_stack_cells);
          }
          if (const auto *fact =
                  findFact(caller_summary->outgoing_facts, slot_id)) {
            collectExprStackCellIds(fact->value, required_stack_cells);
          }
          for (const auto &stack_fact : caller_summary->outgoing_stack_facts) {
            if (stack_fact.value.kind != VirtualExprKind::kStateSlot ||
                !stack_fact.value.slot_id.has_value() ||
                *stack_fact.value.slot_id != slot_id) {
              continue;
            }
            required_stack_cells.insert(stack_fact.cell_id);
          }
        }
        if (needs_stack_fact_specialization) {
          for (const auto &fact : callee_summary->incoming_stack_facts) {
            if (!fact.value.constant.has_value())
              required_stack_cells.insert(fact.cell_id);
          }
        }
        if (required_slots.empty() && required_stack_cells.empty())
          continue;

        auto callsite_facts = collectCallsiteConstantFacts(*call, model);
        auto callsite_stack_facts = collectCallsiteConstantStackFacts(*call, model);
        if (genericDebugEnabled()) {
          genericDebugLog(
              (llvm::Twine("specialize candidate caller=") +
               caller_fn.getName() + " callee=" + callee_fn->getName() +
               " req_slots=" + llvm::Twine(required_slots.size()) +
               " req_stack=" + llvm::Twine(required_stack_cells.size()) +
               " callsite_stack=" +
               llvm::Twine(callsite_stack_facts.size()))
                  .str());
        }
        llvm::SmallVector<VirtualSlotFact, 8> specialization_facts;
        for (unsigned slot_id : required_slots) {
          auto callsite_it = callsite_facts.find(slot_id);
          if (callsite_it != callsite_facts.end()) {
            specialization_facts.push_back(callsite_it->second);
            continue;
          }
          const auto *fact = findFact(caller_summary->outgoing_facts, slot_id);
          if (!fact)
            continue;
          if (auto constant_fact = asConstantFact(*fact))
            specialization_facts.push_back(*constant_fact);
        }

        llvm::SmallVector<VirtualStackFact, 8> specialization_stack_facts;
        for (unsigned cell_id : required_stack_cells) {
          auto callsite_it = callsite_stack_facts.find(cell_id);
          if (callsite_it != callsite_stack_facts.end()) {
            specialization_stack_facts.push_back(callsite_it->second);
            continue;
          }
          const auto *fact =
              findStackFact(caller_summary->outgoing_stack_facts, cell_id);
          if (!fact)
            continue;
          if (auto constant_fact = asConstantStackFact(*fact))
            specialization_stack_facts.push_back(*constant_fact);
        }

        if (specialization_facts.empty() && specialization_stack_facts.empty())
          continue;
        if (genericDebugEnabled()) {
          genericDebugLog(
              (llvm::Twine("specialize facts caller=") + caller_fn.getName() +
               " callee=" + callee_fn->getName() + " slots=" +
               llvm::Twine(specialization_facts.size()) + " stack=" +
               llvm::Twine(specialization_stack_facts.size()))
                  .str());
        }

        auto source_key =
            std::make_pair(*root_va, callee_summary->function_name);
        auto existing_variant = variants_per_source.find(source_key);
        if (existing_variant == variants_per_source.end())
          existing_variant = variants_per_source.emplace(source_key, 0).first;
        if (existing_variant->second >= kMaxVariantsPerSource ||
            total_specialized_functions >= kMaxSpecializedPerRootSlice)
          continue;

        bool created = false;
        auto *clone = getOrCreateSpecializedClone(M, *callee_fn, *root_va,
                                                  specialization_facts,
                                                  specialization_stack_facts,
                                                  &created);
        if (!clone || clone == callee_fn)
          continue;
        if (call->getCalledFunction() == clone)
          continue;

        if (created)
          ++existing_variant->second;
        call->setCalledFunction(clone);
        if (created)
          ++total_specialized_functions;
        changed = true;
        changed_functions.insert(&caller_fn);
        if (diagnostics) {
          diagnostics->push_back("specialized-callsite caller=" +
                                 caller_fn.getName().str() + " callee=" +
                                 callee_summary->function_name + " -> " +
                                 clone->getName().str());
        }
      }
    }
  }

  return changed;
}

static std::set<std::string> collectReachableHandlerNames(
    const VirtualMachineModel &model, bool &has_root_slices) {
  std::set<std::string> reachable;
  has_root_slices = !model.rootSlices().empty();
  if (!has_root_slices)
    return reachable;

  for (const auto &slice : model.rootSlices()) {
    for (const auto &handler_name : slice.reachable_handler_names)
      reachable.insert(handler_name);
  }
  return reachable;
}

static bool tryLiftTarget(
    llvm::Module &M, llvm::ModuleAnalysisManager &AM, uint64_t target_pc,
    llvm::SmallDenseSet<uint64_t, 16> &failed_targets,
    llvm::SmallVectorImpl<std::string> *diagnostics) {
  if (target_pc == 0 || lookupLiftedTargetByPC(M, target_pc))
    return false;
  if (failed_targets.contains(target_pc))
    return false;

  auto session_result = AM.getResult<IterativeLiftingSessionAnalysis>(M);
  const auto &block_lift = AM.getResult<BlockLiftAnalysis>(M).lift_block;
  const auto &trace_lift = AM.getResult<TraceLiftAnalysis>(M).lift_trace;

  bool lifted = false;
  if (session_result.session && session_result.session->useBlockLifting() &&
      block_lift) {
    lifted = block_lift(target_pc);
  } else if (block_lift) {
    lifted = block_lift(target_pc);
  } else if (trace_lift) {
    lifted = trace_lift(target_pc);
  }

  if (lifted && session_result.session)
    session_result.session->noteLiftedTarget(target_pc);

  if (!lifted || !lookupLiftedTargetByPC(M, target_pc)) {
    failed_targets.insert(target_pc);
    if (diagnostics) {
      diagnostics->push_back("lift-failed target=0x" +
                             llvm::utohexstr(target_pc));
    }
    return false;
  }

  if (diagnostics) {
    diagnostics->push_back("lifted target=0x" + llvm::utohexstr(target_pc) +
                           " -> " + lookupLiftedTargetByPC(M, target_pc)->getName().str());
  }
  return true;
}

static bool shouldAttemptLiftFrontier(
    const VirtualRootSliceSummary::FrontierEdge &frontier) {
  switch (frontier.kind) {
    case VirtualRootFrontierKind::kDispatch:
      return frontier.reason == "missing_lifted_target" ||
             frontier.reason == "boundary_target_unlifted";
    case VirtualRootFrontierKind::kCall:
      return frontier.reason == "call_target_unlifted" ||
             frontier.reason == "call_target_nearby_unlifted";
  }
  return false;
}

static void annotateClosedRootSlices(llvm::Module &M,
                                     const VirtualMachineModel &model) {
  for (auto &F : M) {
    F.removeFnAttr("omill.closed_root_slice");
    F.removeFnAttr("omill.closed_root_slice_root");
  }

  bool has_closed_slice = false;
  for (const auto &slice : model.rootSlices()) {
    if (!slice.is_closed)
      continue;
    has_closed_slice = true;

    for (const auto &handler_name : slice.reachable_handler_names) {
      if (auto *F = M.getFunction(handler_name))
        F->addFnAttr("omill.closed_root_slice", "1");
    }

    if (auto *root_fn = lookupLiftedTargetByPC(M, slice.root_va)) {
      root_fn->addFnAttr("omill.closed_root_slice", "1");
      root_fn->addFnAttr("omill.closed_root_slice_root", "1");
    }
  }

  M.addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope",
                  static_cast<uint32_t>(has_closed_slice ? 1 : 0));
}

static MaterializationResult runMaterialization(llvm::Module &M,
                                                llvm::ModuleAnalysisManager &AM) {
  MaterializationResult result;
  genericDebugLog("begin materialization");
  const auto &binary_memory = AM.getResult<BinaryMemoryAnalysis>(M);
  VirtualMachineModel final_model;
  unsigned total_direct_rewrites = 0;
  llvm::SmallDenseSet<uint64_t, 16> failed_lift_targets;
  std::map<std::pair<uint64_t, std::string>, unsigned> variants_per_source;
  unsigned total_specialized_functions = 0;

  constexpr unsigned kMaxIterations = 32;
  for (unsigned iteration = 0; iteration < kMaxIterations; ++iteration) {
    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " model-start");
    final_model = VirtualMachineModelAnalysis().run(M, AM);
    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " model-done handlers=" +
                    llvm::Twine(final_model.handlers().size()).str() +
                    " roots=" + llvm::Twine(final_model.rootSlices().size()).str());

    bool has_root_slices = false;
    auto reachable_handlers =
        collectReachableHandlerNames(final_model, has_root_slices);
    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " reachable-handlers=" +
                    llvm::Twine(reachable_handlers.size()).str());

    bool lifted_new_target = false;
    for (const auto &slice : final_model.rootSlices()) {
      if (slice.is_closed)
        continue;
      for (const auto &frontier : slice.frontier_edges) {
        if (!shouldAttemptLiftFrontier(frontier))
          continue;
        uint64_t target_pc =
            frontier.canonical_target_va.value_or(frontier.target_pc.value_or(0));
        if (target_pc == 0)
          continue;
        if (tryLiftTarget(M, AM, target_pc, failed_lift_targets,
                          &result.diagnostics)) {
          lifted_new_target = true;
          result.changed = true;
        }
      }
    }
    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " frontier-lift-done changed=" +
                    llvm::Twine(lifted_new_target ? 1 : 0).str());
    if (lifted_new_target)
      continue;

    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " specialize-start");
    if (specializeReachableCallsites(M, final_model, &result.diagnostics,
                                     variants_per_source,
                                     total_specialized_functions,
                                     result.changed_functions)) {
      genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                      " specialize-changed");
      result.changed = true;
      continue;
    }
    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " scan-start");

    bool lifted_terminal_target = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (has_root_slices &&
          reachable_handlers.find(F.getName().str()) == reachable_handlers.end())
        continue;

      const auto *summary = final_model.lookupHandler(F.getName());
      if (!summary)
        continue;

      bool has_missing_block = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (callee && callee->getName() == "__remill_missing_block") {
            has_missing_block = true;
            break;
          }
        }
        if (has_missing_block)
          break;
      }
      if (!has_missing_block)
        continue;

      auto target_pc = resolveTerminalNextPcFromFacts(*summary, binary_memory,
                                                      &result.diagnostics);
      if (!target_pc || lookupLiftedTargetByPC(M, *target_pc))
        continue;
      if (tryLiftTarget(M, AM, *target_pc, failed_lift_targets,
                        &result.diagnostics)) {
        lifted_terminal_target = true;
        result.changed = true;
      }
    }
    if (lifted_terminal_target) {
      genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                      " terminal-lift-changed");
      continue;
    }

    struct Candidate {
      llvm::CallInst *call = nullptr;
      llvm::Function *source_fn = nullptr;
      llvm::Function *target_fn = nullptr;
      uint64_t target_pc = 0;
      bool is_jump = false;
      bool store_pc_to_state = false;
    };
    struct BranchCandidate {
      llvm::CallInst *call = nullptr;
      llvm::Function *source_fn = nullptr;
      llvm::Value *condition = nullptr;
      ResolvedTarget true_target;
      ResolvedTarget false_target;
    };
    struct ChoiceCandidate {
      llvm::CallInst *call = nullptr;
      llvm::Function *source_fn = nullptr;
      llvm::Value *dispatch_value = nullptr;
      llvm::SmallVector<ResolvedTarget, 4> targets;
    };
    struct MissingCandidate {
      llvm::CallInst *call = nullptr;
      llvm::Function *source_fn = nullptr;
      llvm::Function *target_fn = nullptr;
      uint64_t target_pc = 0;
      bool store_pc_to_state = false;
    };

    llvm::SmallVector<Candidate, 16> candidates;
    llvm::SmallVector<BranchCandidate, 8> branch_candidates;
    llvm::SmallVector<ChoiceCandidate, 8> switch_candidates;
    llvm::SmallVector<MissingCandidate, 8> missing_candidates;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (has_root_slices &&
          reachable_handlers.find(F.getName().str()) == reachable_handlers.end())
        continue;

      const auto *summary = final_model.lookupHandler(F.getName());
      if (!summary)
        continue;

      if (auto target_pc = resolveTerminalNextPcFromFacts(*summary, binary_memory,
                                                          &result.diagnostics)) {
        auto resolved = resolveTarget(M, binary_memory, final_model,
                                      F.getFunctionType(), *target_pc,
                                      &result.diagnostics);
        if (resolved.function && resolved.function != &F &&
            resolved.function->getName() != "__remill_missing_block") {
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call)
                continue;
              auto *callee = call->getCalledFunction();
              if (!callee || callee->getName() != "__remill_missing_block")
                continue;
              missing_candidates.push_back(
                  MissingCandidate{call, &F, resolved.function, resolved.pc,
                                   resolved.store_pc_to_state});
            }
          }
        }
      }

      size_t dispatch_index = 0;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          auto name = callee->getName();
          if (name != "__omill_dispatch_call" && name != "__omill_dispatch_jump")
            continue;
          if (dispatch_index >= summary->dispatches.size())
            continue;

          const auto &dispatch = summary->dispatches[dispatch_index++];

          if (auto *select =
                  llvm::dyn_cast<llvm::SelectInst>(call->getArgOperand(1));
              select && !name.ends_with("jump") &&
              select->getCondition()->getType()->isIntegerTy(1)) {
            auto *true_pc =
                llvm::dyn_cast<llvm::ConstantInt>(select->getTrueValue());
            auto *false_pc =
                llvm::dyn_cast<llvm::ConstantInt>(select->getFalseValue());
            if (true_pc && false_pc) {
              auto true_target =
                  resolveTarget(M, binary_memory, final_model,
                                call->getFunctionType(), true_pc->getZExtValue(),
                                &result.diagnostics);
              auto false_target =
                  resolveTarget(M, binary_memory, final_model,
                                call->getFunctionType(),
                                false_pc->getZExtValue(), &result.diagnostics);
              if (true_target.function && false_target.function) {
                branch_candidates.push_back(BranchCandidate{
                    call, &F, select->getCondition(), true_target, false_target});
                continue;
              }
            }
          }

          if (dispatch.successors.size() >= 2 && !dispatch.is_jump &&
              call->getArgOperand(1)->getType()->isIntegerTy()) {
            llvm::SmallVector<ResolvedTarget, 4> resolved_choices;
            bool all_resolved = true;
            for (const auto &successor : dispatch.successors) {
              auto resolved =
                  resolveTarget(M, binary_memory, final_model,
                                call->getFunctionType(), successor.target_pc,
                                &result.diagnostics);
              if (!resolved.function || resolved.function == &F) {
                all_resolved = false;
                break;
              }
              resolved_choices.push_back(resolved);
            }
            if (all_resolved) {
              ChoiceCandidate candidate;
              candidate.call = call;
              candidate.source_fn = &F;
              candidate.dispatch_value = call->getArgOperand(1);
              candidate.targets.assign(resolved_choices.begin(),
                                       resolved_choices.end());
              switch_candidates.push_back(candidate);
              continue;
            }
          }

          uint64_t resolved_pc = 0;
          if (!dispatch.successors.empty()) {
            const auto &successor = dispatch.successors.front();
            if (dispatch.successors.size() == 1 && successor.target_pc != 0)
              resolved_pc = successor.target_pc;
          }
          if (!resolved_pc) {
            if (auto fallback =
                    resolveDispatchFromFacts(final_model, *summary, dispatch,
                                             &result.diagnostics)) {
              resolved_pc = *fallback;
            }
          }
          if (!resolved_pc)
            continue;

          auto resolved = resolveTarget(M, binary_memory, final_model,
                                        call->getFunctionType(), resolved_pc,
                                        &result.diagnostics);
          if (!resolved.function || resolved.function == &F)
            continue;

          candidates.push_back(Candidate{call, &F, resolved.function,
                                         resolved.pc,
                                         name == "__omill_dispatch_jump",
                                         resolved.store_pc_to_state});
        }
      }
    }

    bool iteration_changed = false;
    for (const auto &branch_candidate : branch_candidates) {
      if (!branch_candidate.call || !branch_candidate.call->getParent())
        continue;
      if (lowerSelectDispatchToBranches(branch_candidate.call,
                                        branch_candidate.condition,
                                        branch_candidate.true_target,
                                        branch_candidate.false_target)) {
        result.changed = true;
        iteration_changed = true;
        result.changed_functions.insert(branch_candidate.source_fn);
      }
    }

    for (const auto &switch_candidate : switch_candidates) {
      if (!switch_candidate.call || !switch_candidate.call->getParent())
        continue;
      if (lowerChoiceDispatchToSwitch(switch_candidate.call,
                                      switch_candidate.dispatch_value,
                                      switch_candidate.targets)) {
        result.changed = true;
        iteration_changed = true;
        result.changed_functions.insert(switch_candidate.source_fn);
      }
    }

    for (const auto &candidate : candidates) {
      if (!candidate.call || !candidate.call->getParent())
        continue;
      if (lowerToDirectCall(candidate.call, candidate.target_fn,
                            candidate.target_pc, candidate.is_jump,
                            candidate.store_pc_to_state)) {
        result.changed = true;
        iteration_changed = true;
        ++total_direct_rewrites;
        result.changed_functions.insert(candidate.source_fn);
      }
    }

    for (const auto &candidate : missing_candidates) {
      if (!candidate.call || !candidate.call->getParent())
        continue;
      if (lowerToDirectCall(candidate.call, candidate.target_fn,
                            candidate.target_pc, /*is_jump=*/false,
                            candidate.store_pc_to_state)) {
        result.changed = true;
        iteration_changed = true;
        ++total_direct_rewrites;
        result.changed_functions.insert(candidate.source_fn);
      }
    }

    if (!iteration_changed)
      break;
    genericDebugLog("iteration " + llvm::Twine(iteration).str() +
                    " rewrite-changed");
  }

  genericDebugLog("final-model-start");
  final_model = VirtualMachineModelAnalysis().run(M, AM);
  genericDebugLog("final-model-done");
  annotateClosedRootSlices(M, final_model);

  llvm::SmallVector<llvm::Function *, 8> dead_missing_stubs;
  for (auto &F : M) {
    if (!isTerminalMissingBlockStub(F) || !F.use_empty() ||
        !isSyntheticBlockLikeFunctionName(F.getName()))
      continue;
    dead_missing_stubs.push_back(&F);
  }
  for (auto *F : dead_missing_stubs) {
    F->eraseFromParent();
    result.changed = true;
  }
  if (!dead_missing_stubs.empty()) {
    final_model = VirtualMachineModelAnalysis().run(M, AM);
  }

  if (const char *dump_path = std::getenv("OMILL_DUMP_VIRTUAL_MODEL");
      dump_path && dump_path[0] != '\0') {
    std::error_code ec;
    llvm::raw_fd_ostream os(dump_path, ec, llvm::sys::fs::OF_Text);
    if (!ec) {
      os << "module " << M.getName() << "\n";
      os << "binary_memory_empty " << (binary_memory.empty() ? "true" : "false")
         << "\n";
      os << "handlers " << final_model.handlers().size() << "\n";
      os << "slots " << final_model.slots().size() << "\n";
      os << "stack_cells " << final_model.stackCells().size() << "\n";
      os << "regions " << final_model.regions().size() << "\n";
      os << "root_slices " << final_model.rootSlices().size() << "\n";
      os << "materialized " << total_direct_rewrites << "\n";
      for (const auto &slice : final_model.rootSlices()) {
        os << "root-slice root=0x" << llvm::utohexstr(slice.root_va)
           << " reachable=" << slice.reachable_handler_names.size()
           << " frontier=" << slice.frontier_edges.size()
           << " closed=" << (slice.is_closed ? "true" : "false")
           << " specializations=" << slice.specialization_count << "\n";
        for (const auto &handler_name : slice.reachable_handler_names)
          os << "  slice-handler " << handler_name << "\n";
        for (const auto &frontier : slice.frontier_edges) {
          os << "  frontier " << frontier.source_handler_name
             << " kind="
             << (frontier.kind == VirtualRootFrontierKind::kCall ? "call"
                                                                 : "dispatch");
          if (frontier.kind == VirtualRootFrontierKind::kCall)
            os << " callsite=" << frontier.callsite_index;
          else
            os << " dispatch=" << frontier.dispatch_index;
          os
             << " reason=" << frontier.reason;
          if (frontier.target_pc.has_value())
            os << " target=0x" << llvm::utohexstr(*frontier.target_pc);
          if (frontier.canonical_target_va.has_value()) {
            os << " canonical=0x"
               << llvm::utohexstr(*frontier.canonical_target_va);
          }
          if (frontier.boundary_name.has_value())
            os << " boundary=" << *frontier.boundary_name;
          os << "\n";
        }
      }
      for (const auto &region : final_model.regions()) {
        os << "region " << region.id << " handlers=" << region.handler_names.size()
           << " boundaries=" << region.boundary_names.size()
           << " entries=" << region.entry_handler_names.size() << "\n";
        for (const auto &boundary_name : region.boundary_names)
          os << "  region-boundary " << boundary_name << "\n";
        for (const auto &handler_name : region.handler_names)
          os << "  region-handler " << handler_name << "\n";
        for (const auto &fact : region.incoming_facts) {
          os << "  region-in slot[" << fact.slot_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : region.outgoing_facts) {
          os << "  region-out slot[" << fact.slot_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : region.incoming_stack_facts) {
          os << "  region-stack-in cell[" << fact.cell_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : region.outgoing_stack_facts) {
          os << "  region-stack-out cell[" << fact.cell_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
      }
      for (const auto &slot : final_model.slots()) {
        os << "slot " << slot.id << " base=" << slot.base_name
           << " offset=0x" << llvm::utohexstr(static_cast<uint64_t>(slot.offset))
           << " width=" << slot.width
           << " from_argument=" << (slot.from_argument ? "true" : "false")
           << " from_alloca=" << (slot.from_alloca ? "true" : "false")
           << "\n";
      }
      for (const auto &cell : final_model.stackCells()) {
        os << "stack-cell " << cell.id << " base_slot=" << cell.base_slot_id
           << " base=" << cell.base_name
           << " base_offset=0x"
           << llvm::utohexstr(static_cast<uint64_t>(cell.base_offset))
           << " cell_offset=0x"
           << llvm::utohexstr(static_cast<uint64_t>(cell.cell_offset))
           << " width=" << cell.width << "\n";
      }
      for (const auto &handler : final_model.handlers()) {
        os << "handler " << handler.function_name;
        if (handler.entry_va.has_value())
          os << " entry=0x" << llvm::utohexstr(*handler.entry_va);
        os << " candidate=" << (handler.is_candidate ? "true" : "false");
        os << " output_root=" << (handler.is_output_root ? "true" : "false");
        os << " specialized=" << (handler.is_specialized ? "true" : "false");
        if (handler.specialization_root_va.has_value()) {
          os << " specialization_root=0x"
             << llvm::utohexstr(*handler.specialization_root_va);
        }
        os << " direct_callees=" << handler.direct_callees.size();
        os << " dispatches=" << handler.dispatches.size();
        os << " callsites=" << handler.callsites.size() << "\n";
        for (const auto &callee : handler.direct_callees)
          os << "  callee " << callee << "\n";
        for (const auto &fact : handler.incoming_facts) {
          os << "  in slot[" << fact.slot_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : handler.incoming_argument_facts) {
          os << "  in arg[" << fact.argument_index
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : handler.outgoing_facts) {
          os << "  out slot[" << fact.slot_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : handler.incoming_stack_facts) {
          os << "  stack-in cell[" << fact.cell_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &fact : handler.outgoing_stack_facts) {
          os << "  stack-out cell[" << fact.cell_id
             << "] = " << renderVirtualValueExpr(fact.value) << "\n";
        }
        for (const auto &dispatch : handler.dispatches) {
          os << "  dispatch " << (dispatch.is_jump ? "jump" : "call")
             << " target=" << renderVirtualValueExpr(dispatch.target) << "\n";
          if (!dispatch.unresolved_reason.empty()) {
            os << "    specialized_target source=";
            switch (dispatch.specialized_target_source) {
              case VirtualDispatchResolutionSource::kUnknown:
                os << "unknown";
                break;
              case VirtualDispatchResolutionSource::kDirect:
                os << "direct";
                break;
              case VirtualDispatchResolutionSource::kOutgoingFacts:
                os << "outgoing_facts";
                break;
              case VirtualDispatchResolutionSource::kRegionOutgoingFacts:
                os << "region_outgoing_facts";
                break;
              case VirtualDispatchResolutionSource::kIncomingFacts:
                os << "incoming_facts";
                break;
              case VirtualDispatchResolutionSource::kRegionIncomingFacts:
                os << "region_incoming_facts";
                break;
              case VirtualDispatchResolutionSource::kHelperArgumentSpecialization:
                os << "helper_argument_specialization";
                break;
            }
            os << " expr="
               << renderVirtualValueExpr(dispatch.specialized_target) << "\n";
          }
          for (const auto &successor : dispatch.successors) {
            os << "    successor kind=";
            switch (successor.kind) {
              case VirtualSuccessorKind::kUnknown:
                os << "unknown";
                break;
              case VirtualSuccessorKind::kLiftedHandler:
                os << "lifted_handler";
                break;
              case VirtualSuccessorKind::kLiftedBlock:
                os << "lifted_block";
                break;
              case VirtualSuccessorKind::kTraceBlock:
                os << "trace_block";
                break;
              case VirtualSuccessorKind::kProtectedBoundary:
                os << "protected_boundary";
                break;
            }
            os << " source=";
            switch (successor.resolution_source) {
              case VirtualDispatchResolutionSource::kUnknown:
                os << "unknown";
                break;
              case VirtualDispatchResolutionSource::kDirect:
                os << "direct";
                break;
              case VirtualDispatchResolutionSource::kOutgoingFacts:
                os << "outgoing_facts";
                break;
              case VirtualDispatchResolutionSource::kRegionOutgoingFacts:
                os << "region_outgoing_facts";
                break;
              case VirtualDispatchResolutionSource::kIncomingFacts:
                os << "incoming_facts";
                break;
              case VirtualDispatchResolutionSource::kRegionIncomingFacts:
                os << "region_incoming_facts";
                break;
              case VirtualDispatchResolutionSource::kHelperArgumentSpecialization:
                os << "helper_argument_specialization";
                break;
            }
            os << " pc=0x" << llvm::utohexstr(successor.target_pc);
            if (successor.target_function_name.has_value())
              os << " fn=" << *successor.target_function_name;
            if (successor.boundary_name.has_value())
              os << " boundary=" << *successor.boundary_name;
            if (successor.canonical_boundary_target_va.has_value()) {
              os << " canonical=0x"
                 << llvm::utohexstr(*successor.canonical_boundary_target_va);
            }
            os << "\n";
          }
          if (!dispatch.unresolved_reason.empty())
            os << "    unresolved " << dispatch.unresolved_reason << "\n";
        }
        for (const auto &callsite : handler.callsites) {
          os << "  callsite target=" << renderVirtualValueExpr(callsite.target)
             << "\n";
          os << "    specialized_target source=";
          switch (callsite.specialized_target_source) {
            case VirtualDispatchResolutionSource::kUnknown:
              os << "unknown";
              break;
            case VirtualDispatchResolutionSource::kDirect:
              os << "direct";
              break;
            case VirtualDispatchResolutionSource::kOutgoingFacts:
              os << "outgoing_facts";
              break;
            case VirtualDispatchResolutionSource::kRegionOutgoingFacts:
              os << "region_outgoing_facts";
              break;
            case VirtualDispatchResolutionSource::kIncomingFacts:
              os << "incoming_facts";
              break;
            case VirtualDispatchResolutionSource::kRegionIncomingFacts:
              os << "region_incoming_facts";
              break;
            case VirtualDispatchResolutionSource::kHelperArgumentSpecialization:
              os << "helper_argument_specialization";
              break;
          }
          os << " expr=" << renderVirtualValueExpr(callsite.specialized_target)
             << "\n";
          if (callsite.resolved_target_pc.has_value()) {
            os << "    resolved_target=0x"
               << llvm::utohexstr(*callsite.resolved_target_pc) << "\n";
          }
          if (callsite.recovered_entry_pc.has_value()) {
            os << "    recovered_entry=0x"
               << llvm::utohexstr(*callsite.recovered_entry_pc) << "\n";
          }
          if (callsite.continuation_pc.has_value()) {
            os << "    continuation_pc=0x"
               << llvm::utohexstr(*callsite.continuation_pc) << "\n";
          }
          os << "    executable_in_image="
             << (callsite.is_executable_in_image ? "true" : "false") << "\n";
          os << "    decodable_entry="
             << (callsite.is_decodable_entry ? "true" : "false") << "\n";
          if (callsite.target_function_name.has_value())
            os << "    target_fn=" << *callsite.target_function_name << "\n";
          if (callsite.recovered_target_function_name.has_value()) {
            os << "    recovered_target_fn="
               << *callsite.recovered_target_function_name << "\n";
          }
          for (const auto &fact : callsite.return_slot_facts) {
            os << "    return slot[" << fact.slot_id
               << "] = " << renderVirtualValueExpr(fact.value) << "\n";
          }
          for (const auto &fact : callsite.return_stack_facts) {
            os << "    return cell[" << fact.cell_id
               << "] = " << renderVirtualValueExpr(fact.value) << "\n";
          }
          if (!callsite.unresolved_reason.empty())
            os << "    unresolved " << callsite.unresolved_reason << "\n";
        }
      }
      for (const auto &diag : result.diagnostics)
        os << "diag " << diag << "\n";
    }
  }

  return result;
}

#if OMILL_ENABLE_Z3
static void restoreFunctionFromSnapshot(llvm::Function &target,
                                        const llvm::Function &snapshot) {
  target.deleteBody();
  target.copyAttributesFrom(&snapshot);
  target.setCallingConv(snapshot.getCallingConv());
  target.setLinkage(snapshot.getLinkage());
  target.setVisibility(snapshot.getVisibility());
  target.setDSOLocal(snapshot.isDSOLocal());
  target.setUnnamedAddr(snapshot.getUnnamedAddr());

  auto target_arg_it = target.arg_begin();
  for (const auto &snapshot_arg : snapshot.args()) {
    if (target_arg_it == target.arg_end())
      break;
    target_arg_it->setName(snapshot_arg.getName());
    ++target_arg_it;
  }

  llvm::ValueToValueMapTy vmap;
  auto dst_arg_it = target.arg_begin();
  for (const auto &src_arg : snapshot.args()) {
    if (dst_arg_it == target.arg_end())
      break;
    vmap[&src_arg] = &*dst_arg_it;
    ++dst_arg_it;
  }

  if (auto *snapshot_module = snapshot.getParent()) {
    auto &target_module = *target.getParent();
    for (const auto &snapshot_fn : snapshot_module->functions()) {
      if (auto *mapped_fn = target_module.getFunction(snapshot_fn.getName()))
        vmap[&snapshot_fn] = mapped_fn;
    }
    for (const auto &snapshot_global : snapshot_module->globals()) {
      if (auto *mapped_global =
              target_module.getNamedGlobal(snapshot_global.getName()))
        vmap[&snapshot_global] = mapped_global;
    }
    for (const auto &snapshot_alias : snapshot_module->aliases()) {
      if (auto *mapped_alias =
              target_module.getNamedAlias(snapshot_alias.getName()))
        vmap[&snapshot_alias] = mapped_alias;
    }
    for (const auto &snapshot_ifunc : snapshot_module->ifuncs()) {
      if (auto *mapped_ifunc =
              target_module.getNamedIFunc(snapshot_ifunc.getName()))
        vmap[&snapshot_ifunc] = mapped_ifunc;
    }
  }

  llvm::SmallVector<llvm::ReturnInst *, 4> returns;
  llvm::CloneFunctionInto(&target, &snapshot, vmap,
                          llvm::CloneFunctionChangeType::DifferentModule,
                          returns);
  for (auto &bb : target) {
    for (auto &inst : bb)
      llvm::RemapInstruction(&inst, vmap);
  }
}

static bool shouldForceValidationFailure(const llvm::Function &F) {
  return F.hasFnAttribute("omill.force_virtual_materialization_validation_fail");
}
#endif

}  // namespace

llvm::PreservedAnalyses VirtualCFGMaterializationPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &AM) {
  auto result = runMaterialization(M, AM);
  return result.changed ? llvm::PreservedAnalyses::none()
                        : llvm::PreservedAnalyses::all();
}

llvm::PreservedAnalyses VerifiedVirtualCFGMaterializationPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &AM) {
#if OMILL_ENABLE_Z3
  auto snapshot_module = llvm::CloneModule(M);
  z3::context z3_ctx;
  auto result = runMaterialization(M, AM);
  if (!result.changed)
    return llvm::PreservedAnalyses::all();

  bool kept_change = false;
  for (auto *changed_fn : result.changed_functions) {
    if (!changed_fn)
      continue;

    auto *snapshot_fn = snapshot_module->getFunction(changed_fn->getName());
    if (!snapshot_fn) {
      kept_change = true;
      continue;
    }

    bool validation_ok = false;
    std::string counterexample;
    if (!shouldForceValidationFailure(*changed_fn)) {
      TranslationValidator validator(z3_ctx);
      validator.snapshotBefore(*snapshot_fn);
      auto validation = validator.verify(*changed_fn);
      validation_ok = validation.equivalent;
      counterexample = validation.counterexample;
    }

    if (!validation_ok) {
      llvm::errs() << "omill: reverting virtual materialization in "
                   << changed_fn->getName();
      if (!counterexample.empty())
        llvm::errs() << " after validation failure: " << counterexample;
      llvm::errs() << "\n";
      restoreFunctionFromSnapshot(*changed_fn, *snapshot_fn);
      continue;
    }

    kept_change = true;
  }

  return kept_change ? llvm::PreservedAnalyses::none()
                     : llvm::PreservedAnalyses::all();
#else
  auto result = runMaterialization(M, AM);
  return result.changed ? llvm::PreservedAnalyses::none()
                        : llvm::PreservedAnalyses::all();
#endif
}

}  // namespace omill

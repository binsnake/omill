#include "omill/Passes/InlineJumpTargets.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/InlineCost.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Check if a function contains any __remill_jump calls.
bool containsRemillJump(const llvm::Function &F) {
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (auto *callee = CI->getCalledFunction())
          if (callee->getName() == "__remill_jump")
            return true;
  return false;
}

/// Connect disconnected jump table target blocks to the function's CFG by
/// replacing non-constant __remill_jump calls with switches over the known
/// target PCs.  Only creates switch cases for disconnected blocks (lifted from
/// jump table analysis) to avoid PHI corruption from adding edges to blocks
/// already in the connected CFG.  Constant-target jumps are left for Phase 3.
/// Returns the number of jumps lowered.
unsigned lowerJumpsEarly(llvm::Function &F) {
  // Find all CFG-reachable blocks from the entry via actual graph traversal.
  llvm::DenseSet<llvm::BasicBlock *> reachable;
  {
    llvm::SmallVector<llvm::BasicBlock *, 64> worklist;
    worklist.push_back(&F.getEntryBlock());
    reachable.insert(&F.getEntryBlock());
    while (!worklist.empty()) {
      auto *BB = worklist.pop_back_val();
      for (auto *succ : llvm::successors(BB)) {
        if (reachable.insert(succ).second)
          worklist.push_back(succ);
      }
    }
  }

  // Find all named blocks (including disconnected jump table targets).
  auto named_pcs = collectBlockPCMap(F);

  // Identify disconnected blocks: named but not reachable from entry.
  llvm::SmallVector<std::pair<uint64_t, llvm::BasicBlock *>, 32> jt_targets;
  for (auto &[pc, BB] : named_pcs) {
    if (!reachable.count(BB))
      jt_targets.push_back({pc, BB});
  }

  if (jt_targets.empty())
    return 0;

  // Collect __remill_jump calls with non-constant targets.
  // Constant-target jumps are left for Phase 3 LowerJump.
  llvm::SmallVector<llvm::CallInst *, 8> jump_calls;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (auto *callee = CI->getCalledFunction())
          if (callee->getName() == "__remill_jump" &&
              !llvm::isa<llvm::ConstantInt>(CI->getArgOperand(1)))
            jump_calls.push_back(CI);

  if (jump_calls.empty())
    return 0;

  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty = llvm::FunctionType::get(
      mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);
  auto &M = *F.getParent();

  unsigned lowered = 0;
  for (auto *CI : jump_calls) {
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(llvm::successors(BB));

    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::IRBuilder<> Builder(CI);

    auto *fallback_bb = llvm::BasicBlock::Create(
        Ctx, "jump_dispatch_fallback", &F);
    {
      llvm::IRBuilder<> FBBuilder(fallback_bb);
      auto dispatcher =
          M.getOrInsertFunction("__omill_dispatch_jump", lifted_fn_ty);
      auto *result =
          FBBuilder.CreateCall(dispatcher, {state, target_pc, mem});
      FBBuilder.CreateRet(result);
    }

    auto *sw = Builder.CreateSwitch(target_pc, fallback_bb,
                                     jt_targets.size());
    for (auto &[pc, target_bb] : jt_targets)
      sw->addCase(llvm::ConstantInt::get(i64_ty, pc), target_bb);

    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();

    // Erase dead instructions between the new terminator and the old one.
    while (&BB->back() != sw) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Fix PHI nodes for predecessors that are no longer successors.
    llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
        llvm::successors(BB).begin(), llvm::successors(BB).end());
    for (auto *old_succ : old_succs)
      if (!new_succs.count(old_succ))
        old_succ->removePredecessor(BB);

    ++lowered;
  }

  return lowered;
}

/// After inlining a callee that had __remill_function_return, those calls
/// are now in the middle of the caller (not at function exit).  Replace
/// them with their Memory* argument so that Phase 3 LowerReturn doesn't
/// erroneously create a `ret` in the middle of the caller.
void neutralizeInlinedReturns(llvm::Function &F) {
  llvm::SmallVector<llvm::CallInst *, 4> to_neutralize;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee || callee->getName() != "__remill_function_return")
        continue;

      // Check if this return call is NOT followed by a ret instruction.
      // If it IS followed by ret, it's an original return (not inlined).
      auto *term = BB.getTerminator();
      if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(term)) {
        // Check if the ret uses this call's result (directly or via
        // instructions in between).
        if (RI->getReturnValue() == CI)
          continue;  // Original return — keep for Phase 3.
      }

      // Inlined return: replace with Memory* argument (arg 2).
      to_neutralize.push_back(CI);
    }
  }

  for (auto *CI : to_neutralize) {
    llvm::Value *mem = CI->getArgOperand(2);
    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();
  }
}

}  // namespace

llvm::PreservedAnalyses
InlineJumpTargetsPass::run(llvm::Module &M,
                           llvm::ModuleAnalysisManager &MAM) {
  // Step 1: Build VA → defined lifted function map.
  llvm::DenseMap<uint64_t, llvm::Function *> va_to_def;
  for (auto &F : M) {
    if (!isLiftedFunction(F))
      continue;
    uint64_t va = extractEntryVA(F.getName());
    if (va == 0)
      continue;
    va_to_def[va] = &F;
  }

  if (va_to_def.empty())
    return llvm::PreservedAnalyses::all();

  // Step 2: Resolve declared stubs to their implementations.
  // e.g. declare @sub_1800600b0 → define @sub_1800600b0.2
  llvm::SmallVector<llvm::Function *, 4> stubs_to_erase;
  bool changed = false;

  for (auto &F : llvm::make_early_inc_range(M)) {
    if (!F.isDeclaration() || !hasLiftedSignature(F))
      continue;
    if (!F.getName().starts_with("sub_"))
      continue;

    uint64_t va = extractEntryVA(F.getName());
    if (va == 0)
      continue;

    auto it = va_to_def.find(va);
    if (it == va_to_def.end())
      continue;

    llvm::Function *def = it->second;
    if (&F == def)
      continue;

    F.replaceAllUsesWith(def);
    stubs_to_erase.push_back(&F);
    changed = true;
  }

  for (auto *stub : stubs_to_erase)
    stub->eraseFromParent();

  // Step 3: Lower __remill_jump calls to br selector switches.
  // Creates a switch over disconnected block PCs (from jump table analysis),
  // enabling dispatch to jump table targets lifted by TraceLifter.
  // Must run BEFORE inlining so the switches are present in the inlined copies.
  llvm::SmallPtrSet<llvm::Function *, 4> jump_lowered_fns;
  for (auto &F : M) {
    if (!isLiftedFunction(F))
      continue;
    if (lowerJumpsEarly(F)) {
      jump_lowered_fns.insert(&F);
      changed = true;
    }
  }

  // Step 4: Inline callee traces into the main function.
  // Inline callees that either contain __remill_jump (original behavior) or
  // had their jumps lowered to switches by Step 3 (CFF dispatch callees).
  auto shouldInlineCallee = [&](const llvm::Function *callee) {
    return containsRemillJump(*callee) || jump_lowered_fns.count(callee);
  };

  bool did_inline = true;
  while (did_inline) {
    did_inline = false;
    for (auto &F : M) {
      if (!isLiftedFunction(F))
        continue;

      bool inlined_this_function = false;
      llvm::SmallVector<llvm::CallInst *, 8> calls_to_inline;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI)
            continue;
          auto *callee = CI->getCalledFunction();
          if (!callee || callee == &F || !isLiftedFunction(*callee))
            continue;
          if (!shouldInlineCallee(callee))
            continue;
          calls_to_inline.push_back(CI);
        }
      }

      for (auto *CI : calls_to_inline) {
        llvm::InlineFunctionInfo IFI;
        auto result = llvm::InlineFunction(*CI, IFI);
        if (result.isSuccess()) {
          did_inline = true;
          inlined_this_function = true;
          changed = true;
        }
      }

      // Neutralize __remill_function_return calls that ended up in the
      // middle of the function after inlining.
      if (inlined_this_function)
        neutralizeInlinedReturns(F);
    }
  }

  // Step 5: Remove unreachable blocks left over from TraceLifter's jump table
  // target lifting.  These disconnected blocks confuse later passes (SROA,
  // PromoteStateToSSA) and can cause SEH crashes.
  for (auto &F : M) {
    if (!isLiftedFunction(F))
      continue;
    if (llvm::EliminateUnreachableBlocks(F))
      changed = true;
  }

  if (!changed)
    return llvm::PreservedAnalyses::all();

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

#include "omill/Passes/ResolveDispatchTargets.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

namespace {

llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "block_%llx", (unsigned long long)pc);
  for (auto &BB : F)
    if (BB.getName() == buf)
      return &BB;

  snprintf(buf, sizeof(buf), "block_%lx", (unsigned long)pc);
  for (auto &BB : F)
    if (BB.getName() == buf)
      return &BB;

  return nullptr;
}

llvm::Function *findLiftedFunction(llvm::Module &M, uint64_t target_pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "sub_%llx", (unsigned long long)target_pc);
  if (auto *F = M.getFunction(buf))
    return F;

  snprintf(buf, sizeof(buf), "sub_%lx", (unsigned long)target_pc);
  if (auto *F = M.getFunction(buf))
    return F;

  return nullptr;
}

/// Check if a dispatch_call's target is already a ptrtoint(@func) — meaning
/// it was already resolved by ResolveIATCalls or a prior iteration.
bool isAlreadyResolved(llvm::Value *target) {
  if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target))
    if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
      return true;
  return false;
}

}  // namespace

llvm::PreservedAnalyses ResolveDispatchTargetsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());

  auto &M = *F.getParent();
  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  bool changed = false;

  // --- Resolve dispatch_call targets ---
  {
    llvm::SmallVector<llvm::CallInst *, 4> candidates;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->getName() != "__omill_dispatch_call")
          continue;
        if (call->arg_size() < 3)
          continue;

        auto *target = call->getArgOperand(1);
        if (isAlreadyResolved(target))
          continue;

        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(target);
        if (!ci)
          continue;

        candidates.push_back(call);
      }
    }

    for (auto *call : candidates) {
      auto *ci = llvm::cast<llvm::ConstantInt>(call->getArgOperand(1));
      uint64_t target_pc = ci->getZExtValue();

      // Priority 1: IAT import lookup.
      if (map && map->hasImports()) {
        if (auto *imp = map->lookupImport(target_pc)) {
          auto *fn_type =
              llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
          auto fn_callee = M.getOrInsertFunction(imp->function, fn_type);
          auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
          if (fn) {
            fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
            llvm::IRBuilder<> Builder(call);
            auto *fn_addr = Builder.CreatePtrToInt(fn, i64_ty,
                                                    imp->function + ".addr");
            call->setArgOperand(1, fn_addr);
            changed = true;
            continue;
          }
        }
      }

      // Priority 2: Direct call to lifted function.
      if (auto *target_fn = findLiftedFunction(M, target_pc)) {
        llvm::IRBuilder<> Builder(call);
        auto *direct_call = Builder.CreateCall(
            target_fn, {call->getArgOperand(0), ci, call->getArgOperand(2)});
        call->replaceAllUsesWith(direct_call);
        call->eraseFromParent();
        changed = true;
      }
    }
  }

  // --- Resolve dispatch_jump targets ---
  {
    struct JumpCandidate {
      llvm::CallInst *call;
      llvm::ReturnInst *ret;
      uint64_t target_pc;
    };
    llvm::SmallVector<JumpCandidate, 4> candidates;

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->getName() != "__omill_dispatch_jump")
          continue;
        if (call->arg_size() < 3)
          continue;

        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!ci)
          continue;

        // dispatch_jump should be followed by a ret instruction.
        auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
        if (!ret)
          continue;

        candidates.push_back({call, ret, ci->getZExtValue()});
      }
    }

    for (auto &[call, ret, target_pc] : candidates) {
      auto *BB = call->getParent();
      llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

      // Priority 1: Intra-function branch.
      if (auto *target_bb = findBlockForPC(F, target_pc)) {
        llvm::IRBuilder<> Builder(call);
        auto *br = Builder.CreateBr(target_bb);

        // Replace uses and erase dead instructions.
        call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
        ret->eraseFromParent();
        call->eraseFromParent();

        // Erase dead instructions after br.
        while (&BB->back() != br) {
          auto &dead = BB->back();
          if (!dead.use_empty())
            dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
          dead.eraseFromParent();
        }

        // Update PHI nodes.
        llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
            successors(BB).begin(), successors(BB).end());
        for (auto *old_succ : old_succs)
          if (!new_succs.count(old_succ))
            old_succ->removePredecessor(BB);

        changed = true;
        continue;
      }

      // Priority 2: Inter-function tail call.
      if (auto *target_fn = findLiftedFunction(M, target_pc)) {
        llvm::IRBuilder<> Builder(call);
        auto *state = call->getArgOperand(0);
        auto *pc_val = call->getArgOperand(1);
        auto *mem = call->getArgOperand(2);

        auto *tail_call = Builder.CreateCall(target_fn, {state, pc_val, mem});
        tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
        auto *new_ret = Builder.CreateRet(tail_call);

        call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
        ret->eraseFromParent();
        call->eraseFromParent();

        while (&BB->back() != new_ret) {
          auto &dead = BB->back();
          if (!dead.use_empty())
            dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
          dead.eraseFromParent();
        }

        llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
            successors(BB).begin(), successors(BB).end());
        for (auto *old_succ : old_succs)
          if (!new_succs.count(old_succ))
            old_succ->removePredecessor(BB);

        changed = true;
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

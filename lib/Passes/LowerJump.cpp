#include "omill/Passes/LowerJump.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

namespace {

/// Try to find a basic block within this function that corresponds to a
/// given PC. Remill names blocks by their PC address.
llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "block_%llx", (unsigned long long)pc);
  for (auto &BB : F) {
    if (BB.getName() == buf) return &BB;
  }

  snprintf(buf, sizeof(buf), "block_%lx", (unsigned long)pc);
  for (auto &BB : F) {
    if (BB.getName() == buf) return &BB;
  }

  return nullptr;
}

/// Try to find a lifted function for an inter-function jump target.
llvm::Function *findLiftedFunction(llvm::Module &M, uint64_t target_pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "sub_%llx", (unsigned long long)target_pc);
  if (auto *F = M.getFunction(buf)) return F;

  snprintf(buf, sizeof(buf), "sub_%lx", (unsigned long)target_pc);
  if (auto *F = M.getFunction(buf)) return F;

  return nullptr;
}

}  // namespace

llvm::PreservedAnalyses LowerJumpPass::run(llvm::Function &F,
                                           llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  llvm::SmallVector<llvm::CallInst *, 8> jump_calls;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      if (table.classifyCall(CI) == IntrinsicKind::kJump) {
        jump_calls.push_back(CI);
      }
    }
  }

  if (jump_calls.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty =
      llvm::FunctionType::get(mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);

  for (auto *CI : jump_calls) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();

    // Save old successors before we replace the terminator.
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    // __remill_jump(State&, addr_t target_pc, Memory*)
    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::Instruction *new_term = nullptr;

    if (auto *const_pc = llvm::dyn_cast<llvm::ConstantInt>(target_pc)) {
      uint64_t pc_val = const_pc->getZExtValue();

      // Case 1: Intra-function jump to a known block
      if (auto *target_bb = findBlockForPC(F, pc_val)) {
        new_term = Builder.CreateBr(target_bb);
      }

      // Case 2: Inter-function jump (tail call)
      if (!new_term) {
        if (auto *target_fn = findLiftedFunction(M, pc_val)) {
          auto *tail_call =
              Builder.CreateCall(target_fn, {state, target_pc, mem});
          tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
          new_term = Builder.CreateRet(tail_call);
        }
      }
    }

    // Case 3: Dynamic or unresolved jump — dispatch
    if (!new_term) {
      auto dispatcher =
          M.getOrInsertFunction("__omill_dispatch_jump", lifted_fn_ty);
      auto *result = Builder.CreateCall(dispatcher, {state, target_pc, mem});
      new_term = Builder.CreateRet(result);
    }

    // Replace uses and erase the call.
    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    // Erase all dead instructions after the new terminator.
    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Update PHI nodes in blocks that lost this predecessor.
    llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(successors(BB).begin(),
                                                        successors(BB).end());
    for (auto *old_succ : old_succs)
      if (!new_succs.count(old_succ))
        old_succ->removePredecessor(BB);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

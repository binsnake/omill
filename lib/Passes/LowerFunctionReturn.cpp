#include "omill/Passes/LowerFunctionReturn.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::PreservedAnalyses LowerFunctionReturnPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  llvm::SmallVector<llvm::CallInst *, 4> return_calls;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      if (table.classifyCall(CI) == IntrinsicKind::kFunctionReturn) {
        return_calls.push_back(CI);
      }
    }
  }

  if (return_calls.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto *CI : return_calls) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();

    // Save old successors before we replace the terminator.
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    // __remill_function_return(State&, addr_t ret_pc, Memory*)
    // Create a ret that returns the Memory* argument to satisfy
    // the return type, or void if the function returns void.
    llvm::Instruction *new_term;
    if (F.getReturnType()->isVoidTy()) {
      new_term = Builder.CreateRetVoid();
    } else {
      new_term = Builder.CreateRet(CI->getArgOperand(2));
    }

    // Replace uses and erase the call.
    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    // Erase all dead instructions after the new terminator (old ret, etc.)
    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Update PHI nodes: ret has no successors, so all old successors lost
    // this block as a predecessor.
    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

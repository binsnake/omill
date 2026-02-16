#include "omill/Passes/LowerErrorAndMissing.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::PreservedAnalyses LowerErrorAndMissingPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 4> pending;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      auto kind = table.classifyCall(CI);
      if (kind == IntrinsicKind::kError || kind == IntrinsicKind::kMissingBlock) {
        pending.push_back({CI, kind});
      }
    }
  }

  if (pending.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  // Declare runtime handlers
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);

  auto error_handler = M.getOrInsertFunction("__omill_error_handler", handler_ty);
  auto missing_handler =
      M.getOrInsertFunction("__omill_missing_block_handler", handler_ty);

  // Do NOT mark handlers as noreturn.  If every path through a lifted function
  // ends with an error/missing handler (common when the trace lifter stops at
  // indirect jumps or unreachable code), marking the handlers noreturn lets
  // LLVM deduce the *entire* function is noreturn, which causes it to
  // aggressively eliminate all continuation code after intra-function calls
  // as dead.  Keeping the handlers as normal calls preserves the code.

  for (auto &[CI, kind] : pending) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();

    // Save old successors before we replace the terminator.
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    // arg0 = State&, arg1 = addr_t (PC at the error), arg2 = Memory*
    llvm::Value *pc = CI->getArgOperand(1);

    if (kind == IntrinsicKind::kError) {
      Builder.CreateCall(error_handler, {pc});
    } else {
      Builder.CreateCall(missing_handler, {pc});
    }

    // Return poison — the handler never returns at runtime, but we must
    // keep a 'ret' so that LLVM sees a valid return path and does not
    // eliminate live code in other branches as dead.
    llvm::Value *ret_val = llvm::PoisonValue::get(F.getReturnType());
    auto *new_term = Builder.CreateRet(ret_val);

    // Replace Memory* return with poison.
    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    // Erase all dead instructions after the new terminator.
    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Update PHI nodes: ret has no successors, so all old successors
    // lost this block as a predecessor.
    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

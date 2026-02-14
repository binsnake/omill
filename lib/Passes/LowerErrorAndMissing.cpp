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

  // Mark handlers as noreturn
  if (auto *F = llvm::dyn_cast<llvm::Function>(error_handler.getCallee())) {
    F->addFnAttr(llvm::Attribute::NoReturn);
  }
  if (auto *F = llvm::dyn_cast<llvm::Function>(missing_handler.getCallee())) {
    F->addFnAttr(llvm::Attribute::NoReturn);
  }

  for (auto &[CI, kind] : pending) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();

    // arg0 = State&, arg1 = addr_t (PC at the error), arg2 = Memory*
    llvm::Value *pc = CI->getArgOperand(1);

    if (kind == IntrinsicKind::kError) {
      Builder.CreateCall(error_handler, {pc});
    } else {
      Builder.CreateCall(missing_handler, {pc});
    }
    auto *new_term = Builder.CreateUnreachable();

    // Replace Memory* return with poison (dead code after unreachable)
    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    // Erase all dead instructions after the new terminator.
    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

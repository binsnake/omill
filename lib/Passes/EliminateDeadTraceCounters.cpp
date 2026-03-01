#include "omill/Passes/EliminateDeadTraceCounters.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Local.h>

namespace omill {

llvm::PreservedAnalyses EliminateDeadTraceCountersPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &) {
  bool Changed = false;

  // Phase 1: Find calls to __omill_error_handler.
  llvm::SmallVector<llvm::CallInst *, 8> ErrorCalls;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *Callee = CI->getCalledFunction();
      if (!Callee || Callee->getName() != "__omill_error_handler")
        continue;
      ErrorCalls.push_back(CI);
    }
  }

  if (ErrorCalls.empty())
    return llvm::PreservedAnalyses::all();

  // Phase 2: For each error_handler call, sever the link to successor blocks
  // properly (updating successor PHIs), then replace remainder with
  // unreachable.
  for (auto *CI : ErrorCalls) {
    auto *BB = CI->getParent();
    auto *Term = BB->getTerminator();

    // Remove this block as a predecessor from all successor blocks.
    // This properly removes PHI entries.
    for (auto *Succ : llvm::successors(BB)) {
      Succ->removePredecessor(BB, /*KeepOneInputPHIs=*/true);
    }

    // Erase everything after (and including) the call.
    // First erase the terminator, then the call.
    if (Term && Term != CI)
      Term->eraseFromParent();

    // Erase any instructions between the call and the (now removed) terminator.
    while (&BB->back() != CI) {
      auto &Last = BB->back();
      if (!Last.use_empty())
        Last.replaceAllUsesWith(llvm::UndefValue::get(Last.getType()));
      Last.eraseFromParent();
    }

    // Replace the call with unreachable.
    llvm::IRBuilder<> Builder(CI);
    Builder.CreateUnreachable();
    CI->eraseFromParent();
    Changed = true;
  }

  if (!Changed)
    return llvm::PreservedAnalyses::all();

  // Phase 3: Remove now-unreachable blocks and clean up dead instructions.
  llvm::removeUnreachableBlocks(F);

  // Iteratively delete trivially dead instructions (NEXT_PC chains etc.).
  bool Deleted = true;
  unsigned TotalDeleted = 0;
  while (Deleted) {
    Deleted = false;
    for (auto &BB : F) {
      for (auto It = BB.begin(); It != BB.end(); ) {
        auto &I = *It++;
        if (llvm::isInstructionTriviallyDead(&I)) {
          I.eraseFromParent();
          Deleted = true;
          ++TotalDeleted;
        }
      }
    }
  }

  llvm::errs() << "[EliminateDeadTraceCounters] Replaced "
               << ErrorCalls.size() << " error_handler calls with unreachable, "
               << "deleted " << TotalDeleted << " dead instructions\n";
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

#include "omill/Passes/CFGRecovery.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Local.h>

namespace omill {

llvm::PreservedAnalyses CFGRecoveryPass::run(llvm::Function &F,
                                             llvm::FunctionAnalysisManager &AM) {
  bool changed = false;

  // Pass 1: Remove unreachable blocks (from __remill_error lowering).
  // Collect blocks that are unreachable from the entry.
  {
    llvm::SmallPtrSet<llvm::BasicBlock *, 32> reachable;
    llvm::SmallVector<llvm::BasicBlock *, 16> worklist;
    worklist.push_back(&F.getEntryBlock());
    reachable.insert(&F.getEntryBlock());

    while (!worklist.empty()) {
      auto *BB = worklist.pop_back_val();
      for (auto *succ : llvm::successors(BB)) {
        if (reachable.insert(succ).second) {
          worklist.push_back(succ);
        }
      }
    }

    llvm::SmallVector<llvm::BasicBlock *, 8> unreachable_blocks;
    for (auto &BB : F) {
      if (!reachable.count(&BB)) {
        unreachable_blocks.push_back(&BB);
      }
    }

    for (auto *BB : unreachable_blocks) {
      // Remove all uses of this block's values
      BB->dropAllReferences();
    }
    for (auto *BB : unreachable_blocks) {
      BB->eraseFromParent();
      changed = true;
    }
  }

  // Pass 2: Merge single-successor/single-predecessor blocks.
  // Remill creates one block per instruction, so there are many chains
  // of blocks with single edges.
  {
    bool merged = true;
    while (merged) {
      merged = false;
      for (auto &BB : F) {
        // Skip entry block — don't merge into it
        if (&BB == &F.getEntryBlock()) continue;

        // If BB has a single predecessor, and that predecessor has a single
        // successor (which is BB), merge them.
        if (auto *pred = BB.getSinglePredecessor()) {
          if (pred->getSingleSuccessor() == &BB) {
            if (llvm::MergeBlockIntoPredecessor(&BB)) {
              merged = true;
              changed = true;
              break;  // Iterator invalidated, restart
            }
          }
        }
      }
    }
  }

  // Pass 3: Fold constant conditional branches.
  for (auto &BB : F) {
    auto *BI = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
    if (!BI || !BI->isConditional()) continue;

    auto *cond = llvm::dyn_cast<llvm::ConstantInt>(BI->getCondition());
    if (!cond) continue;

    // Replace conditional branch with unconditional branch to the taken target.
    llvm::BasicBlock *taken =
        cond->isOne() ? BI->getSuccessor(0) : BI->getSuccessor(1);
    llvm::BasicBlock *not_taken =
        cond->isOne() ? BI->getSuccessor(1) : BI->getSuccessor(0);

    llvm::BranchInst::Create(taken, &BB);
    BI->eraseFromParent();

    // Remove BB from not_taken's predecessor list
    not_taken->removePredecessor(&BB);

    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

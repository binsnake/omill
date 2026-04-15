#include "omill/BC/LiftingArtifactFixes.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>

namespace omill {

void repairMalformedPHIs(llvm::Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;

    auto *entry = &F.getEntryBlock();
    if (!llvm::pred_empty(entry)) {
      auto *new_entry = llvm::BasicBlock::Create(F.getContext(), "entry.fix",
                                                  &F, entry);
      llvm::IRBuilder<> ir(new_entry);
      ir.CreateBr(entry);
      for (auto &I : *entry) {
        auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
        if (!phi)
          break;
        phi->addIncoming(llvm::PoisonValue::get(phi->getType()), new_entry);
      }
    }

    for (auto &BB : F) {
      // Count how many edges each predecessor has to this block.
      llvm::DenseMap<llvm::BasicBlock *, unsigned> pred_edge_count;
      for (auto *P : llvm::predecessors(&BB))
        ++pred_edge_count[P];

      for (auto &I : llvm::make_early_inc_range(BB)) {
        auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
        if (!phi)
          break;

        // Remove entries from non-predecessors.
        for (unsigned i = phi->getNumIncomingValues(); i-- > 0;) {
          if (!pred_edge_count.count(phi->getIncomingBlock(i)))
            phi->removeIncomingValue(i, /*DeletePHIIfEmpty=*/false);
        }

        // Count current entries per predecessor.
        llvm::DenseMap<llvm::BasicBlock *, unsigned> phi_count;
        for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i)
          ++phi_count[phi->getIncomingBlock(i)];

        // Add missing duplicate entries for multi-edge predecessors.
        for (auto &[pred, needed] : pred_edge_count) {
          unsigned have = phi_count.lookup(pred);
          if (have == 0)
            continue;  // No entry at all — can't invent a value.
          for (unsigned j = have; j < needed; ++j) {
            llvm::Value *val = phi->getIncomingValueForBlock(pred);
            phi->addIncoming(val, pred);
          }
        }

        if (phi->getNumIncomingValues() == 0) {
          phi->replaceAllUsesWith(llvm::PoisonValue::get(phi->getType()));
          phi->eraseFromParent();
        }
      }
    }
  }
}

}  // namespace omill

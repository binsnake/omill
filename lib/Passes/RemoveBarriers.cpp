#include "omill/Passes/RemoveBarriers.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::PreservedAnalyses RemoveBarriersPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  llvm::SmallVector<llvm::CallInst *, 32> to_remove;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      // Case 1: Empty inline asm with side effects (volatile separators).
      // Remill inserts these between State struct fields to prevent
      // LLVM from coalescing loads/stores across field boundaries.
      if (CI->isInlineAsm()) {
        if (auto *IA =
                llvm::dyn_cast<llvm::InlineAsm>(CI->getCalledOperand())) {
          if (IA->getAsmString().empty() && IA->hasSideEffects()) {
            to_remove.push_back(CI);
          }
        }
        continue;
      }

      // Case 2: Barrier intrinsics.
      auto kind = table.classifyCall(CI);
      switch (kind) {
        case IntrinsicKind::kBarrierLoadLoad:
        case IntrinsicKind::kBarrierLoadStore:
        case IntrinsicKind::kBarrierStoreLoad:
        case IntrinsicKind::kBarrierStoreStore:
        case IntrinsicKind::kDelaySlotBegin:
        case IntrinsicKind::kDelaySlotEnd:
          to_remove.push_back(CI);
          break;
        default:
          break;
      }
    }
  }

  if (to_remove.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto *CI : to_remove) {
    // Barrier intrinsics take Memory* and return Memory*.
    // Replace uses of the returned Memory* with the input Memory*.
    if (!CI->getType()->isVoidTy() && CI->arg_size() > 0) {
      CI->replaceAllUsesWith(CI->getArgOperand(0));
    }
    CI->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

#include "omill/Passes/DeadStateStoreElimination.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

namespace omill {

namespace {

int64_t resolveStateOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }
  return -1;
}

}  // namespace

llvm::PreservedAnalyses DeadStateStoreEliminationPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &DL = F.getParent()->getDataLayout();

  // Local DSE: within each basic block, find stores to the same State offset
  // that are overwritten before being read.
  llvm::SmallVector<llvm::Instruction *, 32> dead_stores;

  for (auto &BB : F) {
    // Last store to each State offset in this block (not yet read).
    llvm::DenseMap<unsigned, llvm::StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          // Load consumes the value — previous store is live.
          last_store.erase(static_cast<unsigned>(off));
        }
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u_off = static_cast<unsigned>(off);
          auto it = last_store.find(u_off);
          if (it != last_store.end()) {
            // Previous store was never read — it's dead.
            dead_stores.push_back(it->second);
          }
          last_store[u_off] = SI;
        }
      }

      // Calls may read/write State through the pointer. Be conservative.
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (!CI->isInlineAsm() && !llvm::isa<llvm::IntrinsicInst>(CI)) {
          last_store.clear();
        }
      }
    }
  }

  if (dead_stores.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto *I : dead_stores) {
    I->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

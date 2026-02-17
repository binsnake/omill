#include "omill/Passes/DeadStateFlagElimination.h"

#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

/// Resolve a pointer to its State byte offset. Returns -1 if not resolvable.
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

/// Check if an offset corresponds to a flag field.
bool isFlagOffset(unsigned offset, const StateFieldMap &field_map) {
  if (auto field = field_map.fieldAtOffset(offset)) {
    return field->category == StateFieldCategory::kFlag;
  }
  return false;
}

}  // namespace

llvm::PreservedAnalyses DeadStateFlagEliminationPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &DL = F.getParent()->getDataLayout();
  StateFieldMap field_map(*F.getParent());

  // Single-pass: for each basic block, track last store per flag offset.
  // When a store is superseded by another store to the same flag without
  // an intervening load, mark the earlier store as dead.
  llvm::SmallVector<llvm::Instruction *, 16> dead_stores;

  for (auto &BB : F) {
    llvm::DenseMap<unsigned, llvm::StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0 && isFlagOffset(static_cast<unsigned>(off), field_map)) {
          last_store.erase(static_cast<unsigned>(off));
        }
        continue;
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0 && isFlagOffset(static_cast<unsigned>(off), field_map)) {
          unsigned u_off = static_cast<unsigned>(off);
          auto it = last_store.find(u_off);
          if (it != last_store.end()) {
            dead_stores.push_back(it->second);
          }
          last_store[u_off] = SI;
        }
        continue;
      }

      // Calls may read flags through the State pointer — conservatively
      // clear the last_store map at calls.
      if (llvm::isa<llvm::CallInst>(&I) && !llvm::isa<llvm::IntrinsicInst>(&I)) {
        last_store.clear();
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

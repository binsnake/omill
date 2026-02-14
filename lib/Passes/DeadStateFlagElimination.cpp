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

  // Collect all stores and loads to flag fields.
  struct FlagAccess {
    llvm::Instruction *inst;
    unsigned offset;
    bool is_store;
  };

  llvm::SmallVector<FlagAccess, 64> flag_accesses;

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0 && isFlagOffset(static_cast<unsigned>(off), field_map)) {
          flag_accesses.push_back(
              {SI, static_cast<unsigned>(off), /*is_store=*/true});
        }
      }
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0 && isFlagOffset(static_cast<unsigned>(off), field_map)) {
          flag_accesses.push_back(
              {LI, static_cast<unsigned>(off), /*is_store=*/false});
        }
      }
    }
  }

  if (flag_accesses.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  // Per basic block: for each flag field, find stores that are followed by
  // another store to the same field without an intervening load.
  // This is a simple local (intra-block) dead store elimination.
  // A more sophisticated version would use dominators for cross-block DSE.

  llvm::SmallVector<llvm::Instruction *, 16> dead_stores;

  for (auto &BB : F) {
    // Track the last store to each flag field in this block.
    llvm::DenseMap<unsigned, llvm::StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0 && isFlagOffset(static_cast<unsigned>(off), field_map)) {
          // This load reads the flag — the last store is NOT dead.
          last_store.erase(static_cast<unsigned>(off));
        }
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0 && isFlagOffset(static_cast<unsigned>(off), field_map)) {
          unsigned u_off = static_cast<unsigned>(off);
          // If there's already an unread store to this flag, it's dead.
          auto it = last_store.find(u_off);
          if (it != last_store.end()) {
            dead_stores.push_back(it->second);
          }
          last_store[u_off] = SI;
        }
      }

      // Calls may read flags through the State pointer — conservatively
      // clear the last_store map at calls.
      if (llvm::isa<llvm::CallInst>(&I) && !llvm::isa<llvm::IntrinsicInst>(&I)) {
        last_store.clear();
      }
    }

    // At block end: don't eliminate the last store because it may be
    // live-out to successor blocks. A cross-block analysis would refine this.
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

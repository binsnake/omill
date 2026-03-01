#include "IfConversion.h"
#include "PassFilter.h"

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Return true if \p I is safe to speculatively execute (no traps, no
/// side-effects).
static bool isSafeToSpeculate(const llvm::Instruction &I) {
  // PHI nodes / terminators handled separately.
  if (llvm::isa<llvm::PHINode>(I) || I.isTerminator())
    return false;

  switch (I.getOpcode()) {
  // Integer binary ops (excluding div/rem — potential division by zero).
  case llvm::Instruction::Add:
  case llvm::Instruction::Sub:
  case llvm::Instruction::Mul:
  case llvm::Instruction::Xor:
  case llvm::Instruction::And:
  case llvm::Instruction::Or:
  case llvm::Instruction::Shl:
  case llvm::Instruction::LShr:
  case llvm::Instruction::AShr:
  // Float binary ops (won't trap in default FP env).
  case llvm::Instruction::FAdd:
  case llvm::Instruction::FSub:
  case llvm::Instruction::FMul:
  // Casts.
  case llvm::Instruction::BitCast:
  case llvm::Instruction::Trunc:
  case llvm::Instruction::ZExt:
  case llvm::Instruction::SExt:
  case llvm::Instruction::PtrToInt:
  case llvm::Instruction::IntToPtr:
  // Comparisons.
  case llvm::Instruction::ICmp:
  case llvm::Instruction::FCmp:
  // Select is side-effect-free.
  case llvm::Instruction::Select:
  // Freeze is side-effect-free.
  case llvm::Instruction::Freeze:
    return true;
  default:
    return false;
  }
}

/// Return true if every non-PHI, non-terminator instruction in \p BB is safe
/// to speculatively execute.
static bool allSafeToSpeculate(const llvm::BasicBlock &BB) {
  for (const auto &I : BB) {
    if (llvm::isa<llvm::PHINode>(I) || I.isTerminator())
      continue;
    if (!isSafeToSpeculate(I))
      return false;
  }
  return true;
}

/// Try to if-convert one diamond rooted at the conditional branch in \p BB.
/// Returns true if conversion happened.
static bool tryConvertDiamond(llvm::BasicBlock &BB) {
  auto *CondBr = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
  if (!CondBr || !CondBr->isConditional())
    return false;

  llvm::BasicBlock *TrueBB = CondBr->getSuccessor(0);
  llvm::BasicBlock *FalseBB = CondBr->getSuccessor(1);

  // Both arms must have exactly one predecessor (BB).
  if (TrueBB->getSinglePredecessor() != &BB ||
      FalseBB->getSinglePredecessor() != &BB)
    return false;

  // Both arms must end with unconditional branch.
  auto *TrueBr = llvm::dyn_cast<llvm::BranchInst>(TrueBB->getTerminator());
  auto *FalseBr = llvm::dyn_cast<llvm::BranchInst>(FalseBB->getTerminator());
  if (!TrueBr || TrueBr->isConditional() || !FalseBr || FalseBr->isConditional())
    return false;

  // Both must branch to the same merge block.
  llvm::BasicBlock *MergeBB = TrueBr->getSuccessor(0);
  if (FalseBr->getSuccessor(0) != MergeBB)
    return false;

  // All instructions in both arms must be safe to speculate.
  if (!allSafeToSpeculate(*TrueBB) || !allSafeToSpeculate(*FalseBB))
    return false;

  // Validate PHI nodes in MergeBB: every PHI must reference exactly TrueBB
  // and FalseBB — no other predecessors allowed in the PHI.
  for (auto &I : *MergeBB) {
    auto *Phi = llvm::dyn_cast<llvm::PHINode>(&I);
    if (!Phi)
      break;
    if (Phi->getNumIncomingValues() != 2)
      return false;
    bool hasTrueArm = false, hasFalseArm = false;
    for (unsigned i = 0; i < 2; ++i) {
      if (Phi->getIncomingBlock(i) == TrueBB) hasTrueArm = true;
      if (Phi->getIncomingBlock(i) == FalseBB) hasFalseArm = true;
    }
    if (!hasTrueArm || !hasFalseArm)
      return false;
  }

  // --- Perform the conversion. ---

  llvm::Value *Cond = CondBr->getCondition();

  // Hoist instructions from TrueBB and FalseBB into BB, before the
  // terminator. Collect them first to avoid iterator invalidation.
  auto hoistInstructions = [&](llvm::BasicBlock *Src) {
    std::vector<llvm::Instruction *> toMove;
    for (auto &I : *Src) {
      if (llvm::isa<llvm::PHINode>(I) || I.isTerminator())
        continue;
      toMove.push_back(&I);
    }
    for (auto *I : toMove)
      I->moveBefore(CondBr->getIterator());
  };

  hoistInstructions(TrueBB);
  hoistInstructions(FalseBB);

  // Replace each PHI in MergeBB with a select.
  std::vector<llvm::PHINode *> phis;
  for (auto &I : *MergeBB) {
    if (auto *Phi = llvm::dyn_cast<llvm::PHINode>(&I))
      phis.push_back(Phi);
    else
      break;
  }

  for (auto *Phi : phis) {
    llvm::Value *TrueVal = Phi->getIncomingValueForBlock(TrueBB);
    llvm::Value *FalseVal = Phi->getIncomingValueForBlock(FalseBB);
    auto *Sel = llvm::SelectInst::Create(Cond, TrueVal, FalseVal, "",
                                         CondBr->getIterator());
    Phi->replaceAllUsesWith(Sel);
    Phi->eraseFromParent();
  }

  // Replace conditional branch with unconditional branch to MergeBB.
  llvm::BranchInst::Create(MergeBB, CondBr->getIterator());
  CondBr->eraseFromParent();

  // Remove edges from TrueBB and FalseBB to MergeBB then delete the blocks.
  TrueBr->eraseFromParent();
  FalseBr->eraseFromParent();
  TrueBB->eraseFromParent();
  FalseBB->eraseFromParent();

  return true;
}

static void ifConvertFunction(llvm::Function &F, std::mt19937 &rng,
                              const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  // Collect basic blocks upfront — conversion modifies the CFG.
  std::vector<llvm::BasicBlock *> worklist;
  for (auto &BB : F)
    worklist.push_back(&BB);

  llvm::SmallPtrSet<llvm::BasicBlock *, 16> deleted;

  for (auto *BB : worklist) {
    if (deleted.count(BB))
      continue;

    if (!shouldTransform(rng, cfg))
      continue;

    // Record which blocks will be deleted if conversion succeeds.
    auto *CondBr = llvm::dyn_cast<llvm::BranchInst>(BB->getTerminator());
    if (!CondBr || !CondBr->isConditional())
      continue;
    llvm::BasicBlock *TrueBB = CondBr->getSuccessor(0);
    llvm::BasicBlock *FalseBB = CondBr->getSuccessor(1);

    if (tryConvertDiamond(*BB)) {
      deleted.insert(TrueBB);
      deleted.insert(FalseBB);
    }
  }
}

void ifConvertModule(llvm::Module &M, uint32_t seed,
                     const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M)
    ifConvertFunction(F, rng, cfg);
}

}  // namespace ollvm

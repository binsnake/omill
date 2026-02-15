#include "omill/Passes/EliminateDeadPaths.h"

#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/KnownBits.h>

namespace omill {

namespace {

using namespace llvm::PatternMatch;

/// Try to evaluate an icmp with KnownBits analysis.
/// Returns std::nullopt if the result can't be determined.
std::optional<bool> evaluateICmpWithKnownBits(
    llvm::ICmpInst *ICI, const llvm::DataLayout &DL,
    llvm::AssumptionCache *AC, const llvm::DominatorTree *DT) {
  auto *LHS = ICI->getOperand(0);
  auto *RHS = ICI->getOperand(1);

  llvm::KnownBits KnownLHS = llvm::computeKnownBits(LHS, DL, AC, ICI, DT);
  llvm::KnownBits KnownRHS = llvm::computeKnownBits(RHS, DL, AC, ICI, DT);

  auto pred = ICI->getPredicate();

  // If both are fully known, just compare.
  if (KnownLHS.isConstant() && KnownRHS.isConstant()) {
    auto lval = KnownLHS.getConstant();
    auto rval = KnownRHS.getConstant();
    return llvm::ICmpInst::compare(lval, rval, pred);
  }

  // Range-based analysis using KnownBits.
  auto LHSRange = llvm::ConstantRange::fromKnownBits(KnownLHS,
      llvm::ICmpInst::isSigned(pred));
  auto RHSRange = llvm::ConstantRange::fromKnownBits(KnownRHS,
      llvm::ICmpInst::isSigned(pred));

  // icmp returns true when predicate holds for ALL value pairs in the ranges.
  if (LHSRange.icmp(pred, RHSRange))
    return true;
  // Check the inverse: if the inverse predicate holds for all pairs,
  // then the original is always false.
  if (LHSRange.icmp(llvm::ICmpInst::getInversePredicate(pred), RHSRange))
    return false;

  return std::nullopt;
}

/// Match number-theoretic opaque predicate patterns.
/// Returns true/false if the icmp is provably constant, nullopt otherwise.
std::optional<bool> matchOpaquePredicatePattern(llvm::ICmpInst *ICI) {
  auto pred = ICI->getPredicate();
  auto *LHS = ICI->getOperand(0);
  auto *RHS = ICI->getOperand(1);

  // Pattern: X | ~X == -1  (tautology: or of value and its complement)
  {
    llvm::Value *X, *Y;
    llvm::ConstantInt *C;
    if (match(LHS, m_Or(m_Value(X), m_Value(Y))) &&
        match(RHS, m_ConstantInt(C))) {
      bool is_complement = false;
      if (match(Y, m_Not(m_Specific(X))))
        is_complement = true;
      else if (match(X, m_Not(m_Specific(Y))))
        is_complement = true;

      if (is_complement && C->isAllOnesValue()) {
        if (pred == llvm::ICmpInst::ICMP_EQ)
          return true;   // always true
        if (pred == llvm::ICmpInst::ICMP_NE)
          return false;  // always false
      }
    }
  }

  // Pattern: (X * (X + 1)) & 1 == 0  (product of consecutive integers is even)
  {
    llvm::Value *MulResult;
    llvm::ConstantInt *Mask, *CmpVal;
    if (match(LHS, m_And(m_Value(MulResult), m_ConstantInt(Mask))) &&
        match(RHS, m_ConstantInt(CmpVal))) {
      if (Mask->isOne()) {
        llvm::Value *A, *B;
        if (match(MulResult, m_Mul(m_Value(A), m_Value(B)))) {
          // Check if B = A + 1 or A = B + 1.
          llvm::ConstantInt *One;
          bool consecutive = false;
          if (match(B, m_Add(m_Specific(A), m_ConstantInt(One))) &&
              One->isOne())
            consecutive = true;
          if (match(A, m_Add(m_Specific(B), m_ConstantInt(One))) &&
              One->isOne())
            consecutive = true;

          if (consecutive) {
            // (X * (X+1)) & 1 is always 0.
            if (CmpVal->isZero()) {
              if (pred == llvm::ICmpInst::ICMP_EQ)
                return true;
              if (pred == llvm::ICmpInst::ICMP_NE)
                return false;
            }
            if (CmpVal->isOne()) {
              if (pred == llvm::ICmpInst::ICMP_EQ)
                return false;
              if (pred == llvm::ICmpInst::ICMP_NE)
                return true;
            }
          }
        }
      }
    }
  }

  return std::nullopt;
}

/// Try to fold a branch condition to a constant.
std::optional<bool> tryFoldCondition(llvm::BranchInst *BI,
                                      const llvm::DataLayout &DL,
                                      llvm::AssumptionCache *AC,
                                      const llvm::DominatorTree *DT) {
  if (!BI->isConditional())
    return std::nullopt;

  auto *cond = BI->getCondition();

  // Already constant.
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(cond))
    return !CI->isZero();

  auto *ICI = llvm::dyn_cast<llvm::ICmpInst>(cond);
  if (!ICI)
    return std::nullopt;

  // Layer 1: KnownBits.
  if (auto result = evaluateICmpWithKnownBits(ICI, DL, AC, DT))
    return result;

  // Layer 2: Number-theoretic opaque predicates.
  if (auto result = matchOpaquePredicatePattern(ICI))
    return result;

  return std::nullopt;
}

}  // namespace

llvm::PreservedAnalyses EliminateDeadPathsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  const auto &DL = F.getDataLayout();
  auto *DT = AM.getCachedResult<llvm::DominatorTreeAnalysis>(F);
  auto *AC = AM.getCachedResult<llvm::AssumptionAnalysis>(F);
  bool changed = false;

  // Collect conditional branches to fold (avoid iterator invalidation).
  llvm::SmallVector<llvm::BranchInst *, 8> branches;
  for (auto &BB : F) {
    auto *BI = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
    if (BI && BI->isConditional())
      branches.push_back(BI);
  }

  for (auto *BI : branches) {
    auto result = tryFoldCondition(BI, DL, AC, DT);
    if (!result)
      continue;

    auto *BB = BI->getParent();
    auto *taken = BI->getSuccessor(*result ? 0 : 1);
    auto *dead = BI->getSuccessor(*result ? 1 : 0);

    // Replace conditional branch with unconditional.
    llvm::BranchInst::Create(taken, BB);
    BI->eraseFromParent();

    // Remove BB as predecessor of dead successor (unless taken == dead).
    if (dead != taken)
      dead->removePredecessor(BB);

    changed = true;
  }

  // Remove unreachable blocks.
  if (changed) {
    bool removed = true;
    while (removed) {
      removed = false;
      for (auto it = F.begin(); it != F.end();) {
        auto *BB = &*it++;
        if (BB == &F.getEntryBlock())
          continue;
        if (pred_empty(BB)) {
          // Remove this block as predecessor from its successors.
          for (auto *succ : successors(BB))
            succ->removePredecessor(BB);
          BB->dropAllReferences();
          BB->eraseFromParent();
          removed = true;
        }
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

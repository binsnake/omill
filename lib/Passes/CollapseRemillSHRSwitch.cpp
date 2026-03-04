#include "omill/Passes/CollapseRemillSHRSwitch.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/Debug.h>
#include <llvm/Transforms/Utils/Local.h>

#define DEBUG_TYPE "collapse-remill-shr"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace omill {

/// Match: trunc(lshr(V, 60)) to i8.  Returns V if matched.
static Value *matchSHRSwitchCondition(SwitchInst *SW) {
  Value *cond = SW->getCondition();
  Value *shift_amt_i64 = nullptr;
  if (!match(cond, m_Trunc(m_Value(shift_amt_i64))))
    return nullptr;

  Value *V = nullptr;
  uint64_t shift_const = 0;
  if (!match(shift_amt_i64, m_LShr(m_Value(V), m_ConstantInt(shift_const))))
    return nullptr;
  return shift_const == 60 ? V : nullptr;
}

/// Verify the switch has exactly cases [i8 0, i8 1] + default.
static bool verifyCaseStructure(SwitchInst *SW) {
  if (SW->getNumCases() != 2)
    return false;
  bool has_0 = false, has_1 = false;
  for (auto &C : SW->cases()) {
    int64_t val = C.getCaseValue()->getSExtValue();
    if (val == 0) has_0 = true;
    else if (val == 1) has_1 = true;
  }
  return has_0 && has_1;
}

/// Find `lshr i64 %V, 32` in the given basic block.
static Value *findBaseShiftInBlock(BasicBlock *BB, Value *V) {
  for (auto &I : *BB) {
    Value *op = nullptr;
    uint64_t c = 0;
    if (match(&I, m_LShr(m_Value(op), m_ConstantInt(c))) && op == V && c == 32)
      return &I;
  }
  return nullptr;
}

/// Find `lshr i64 %V, 32` by walking up the dominator tree from BB.
static Value *findBaseShift(BasicBlock *BB, Value *V, DominatorTree *DT) {
  // First check the local block (fast path).
  if (Value *bs = findBaseShiftInBlock(BB, V))
    return bs;

  // If no dominator tree available, fall back to local-only.
  if (!DT)
    return nullptr;

  // Walk dominator tree upward.
  auto *node = DT->getNode(BB);
  if (!node)
    return nullptr;
  for (auto *idom = node->getIDom(); idom; idom = idom->getIDom()) {
    if (Value *bs = findBaseShiftInBlock(idom->getBlock(), V))
      return bs;
  }
  return nullptr;
}

/// Follow a basic block to its single unconditional-branch target.
static BasicBlock *followUnconditionalBranch(BasicBlock *BB) {
  auto *br = dyn_cast<BranchInst>(BB->getTerminator());
  if (br && br->isUnconditional())
    return br->getSuccessor(0);
  return nullptr;
}

/// Verify case1/default paths reach the merge block.
static bool verifyCasesReachMerge(BasicBlock *case1BB, BasicBlock *defaultBB,
                                  BasicBlock *merge) {
  if (case1BB == merge)
    return true;
  if (BasicBlock *t = followUnconditionalBranch(case1BB))
    if (t == merge)
      return true;

  // default → intermediate → merge
  if (BasicBlock *defTarget = followUnconditionalBranch(defaultBB)) {
    if (defTarget == merge)
      return true;
    if (BasicBlock *t = followUnconditionalBranch(defTarget))
      if (t == merge)
        return true;
  }
  return false;
}

/// Pattern A: byte reconstruction from phis.
///   or disjoint i64 %phi_high, zext(or(shl(byte1,8), and(byte0,255)))
static Instruction *findByteReconstruction(BasicBlock *MergeBB) {
  SmallVector<PHINode *, 4> phis;
  for (auto &I : *MergeBB) {
    if (auto *phi = dyn_cast<PHINode>(&I))
      phis.push_back(phi);
    else
      break;
  }
  if (phis.size() < 2)
    return nullptr;

  for (auto *phi : phis) {
    for (auto *U : phi->users()) {
      auto *orInst = dyn_cast<Instruction>(U);
      if (!orInst || orInst->getOpcode() != Instruction::Or)
        continue;
      if (!orInst->getType()->isIntegerTy(64))
        continue;

      Value *zext_op = nullptr;
      if (isa<PHINode>(orInst->getOperand(0)) &&
          isa<ZExtInst>(orInst->getOperand(1)))
        zext_op = orInst->getOperand(1);
      else if (isa<ZExtInst>(orInst->getOperand(0)) &&
               isa<PHINode>(orInst->getOperand(1)))
        zext_op = orInst->getOperand(0);
      else
        continue;

      auto *zextInst = cast<ZExtInst>(zext_op);
      auto *lowOr = dyn_cast<Instruction>(zextInst->getOperand(0));
      if (!lowOr || lowOr->getOpcode() != Instruction::Or)
        continue;
      if (!lowOr->getType()->isIntegerTy(32))
        continue;

      bool has_shl8 = false, has_and255 = false;
      for (unsigned i = 0; i < 2; ++i) {
        auto *op = dyn_cast<Instruction>(lowOr->getOperand(i));
        if (!op) continue;
        uint64_t c;
        if (match(op, m_Shl(m_Value(), m_ConstantInt(c))) && c == 8)
          has_shl8 = true;
        if (match(op, m_And(m_Value(), m_ConstantInt(c))) && c == 255)
          has_and255 = true;
      }
      if (has_shl8 && has_and255)
        return orInst;
    }
  }
  return nullptr;
}

/// Pattern B/C: the merge has a single i64 phi with 2 incoming values,
/// one from the case0 path (the "no-shift" result).
static Instruction *findResultPhi(BasicBlock *MergeBB, BasicBlock *case0Pred) {
  for (auto &I : *MergeBB) {
    auto *phi = dyn_cast<PHINode>(&I);
    if (!phi)
      break;
    if (!phi->getType()->isIntegerTy(64))
      continue;
    if (phi->getNumIncomingValues() != 2)
      continue;
    if (phi->getBasicBlockIndex(case0Pred) >= 0)
      return phi;
  }
  return nullptr;
}

/// Pattern D (post-ABI): the phi feeds into a truncation sequence:
///   %trunc = lshr i64 %phi, 1
///   %result = and i64 %trunc, 4294967295
/// or just:
///   %result = and i64 %phi, 4294967295
/// Returns the outermost instruction in the chain to RAUW.
static Instruction *findPostABITruncation(BasicBlock *MergeBB,
                                           BasicBlock *case0Pred) {
  for (auto &I : *MergeBB) {
    auto *phi = dyn_cast<PHINode>(&I);
    if (!phi)
      break;
    if (!phi->getType()->isIntegerTy(64))
      continue;
    if (phi->getNumIncomingValues() != 2)
      continue;
    if (phi->getBasicBlockIndex(case0Pred) < 0)
      continue;

    // Check single use chain: phi → (optional lshr by 1) → and with 0xFFFFFFFF
    for (auto *U : phi->users()) {
      auto *user = dyn_cast<Instruction>(U);
      if (!user)
        continue;

      // Direct: and(phi, 0xFFFFFFFF)
      uint64_t and_c = 0;
      if (match(user, m_And(m_Specific(phi), m_ConstantInt(and_c))) &&
          and_c == 0xFFFFFFFFULL)
        return user;

      // Via shift: lshr(phi, 1) → and(..., 0xFFFFFFFF)
      uint64_t shr_c = 0;
      if (match(user, m_LShr(m_Specific(phi), m_ConstantInt(shr_c)))) {
        for (auto *U2 : user->users()) {
          auto *user2 = dyn_cast<Instruction>(U2);
          if (!user2)
            continue;
          if (match(user2, m_And(m_Specific(user), m_ConstantInt(and_c))) &&
              and_c == 0xFFFFFFFFULL)
            return user2;
        }
      }
    }
  }
  return nullptr;
}

/// Main analysis: find the instruction to replace with lshr(lshr(V,32), lshr(V,60)).
///
/// Returns the instruction to RAUW, or nullptr.
static Instruction *analyzeSwitch(SwitchInst *SW, Value *V) {
  BasicBlock *switchBB = SW->getParent();
  BasicBlock *case0BB = nullptr;
  BasicBlock *case1BB = nullptr;
  BasicBlock *defaultBB = SW->getDefaultDest();

  for (auto &C : SW->cases()) {
    if (C.getCaseValue()->isZero())
      case0BB = C.getCaseSuccessor();
    else
      case1BB = C.getCaseSuccessor();
  }
  if (!case0BB || !case1BB)
    return nullptr;

  // Determine merge block and case0 predecessor of merge.
  BasicBlock *merge = nullptr;
  BasicBlock *case0Pred = nullptr;

  if (isa<PHINode>(case0BB->front())) {
    // case0 goes directly to a phi-bearing block (that block IS the merge).
    merge = case0BB;
    case0Pred = switchBB;
  } else if (BasicBlock *target = followUnconditionalBranch(case0BB)) {
    // case0 → intermediate → merge
    merge = target;
    case0Pred = case0BB;
  }

  if (!merge || !isa<PHINode>(merge->front()))
    return nullptr;

  if (!verifyCasesReachMerge(case1BB, defaultBB, merge))
    return nullptr;

  // Try Pattern A first: byte reconstruction or disjoint i64 in merge block.
  if (Instruction *recon = findByteReconstruction(merge))
    return recon;

  // Try Pattern B/C: single i64 phi in merge from case0 path.
  if (Instruction *phi = findResultPhi(merge, case0Pred))
    return phi;

  // Try Pattern D: post-ABI truncation (phi → lshr/and → i32 range).
  if (Instruction *trunc = findPostABITruncation(merge, case0Pred))
    return trunc;

  return nullptr;
}

llvm::PreservedAnalyses CollapseRemillSHRSwitchPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto name = F.getName();
  if (name.starts_with("_ZN") || name.starts_with("__remill_"))
    return PreservedAnalyses::all();

  // Get dominator tree for cross-block lshr(V, 32) search.
  auto *DT = AM.getCachedResult<DominatorTreeAnalysis>(F);
  // Lazily compute if not cached — needed for dominator walk.
  DominatorTree localDT;
  if (!DT) {
    localDT.recalculate(F);
    DT = &localDT;
  }

  bool changed = false;

  struct Match {
    Value *V;
    Value *baseShift;
    Instruction *target;
  };
  SmallVector<Match, 16> matches;

  for (auto &BB : F) {
    auto *SW = dyn_cast<SwitchInst>(BB.getTerminator());
    if (!SW)
      continue;

    Value *V = matchSHRSwitchCondition(SW);
    if (!V)
      continue;
    if (!verifyCaseStructure(SW))
      continue;

    Value *baseShift = findBaseShift(&BB, V, DT);
    if (!baseShift)
      continue;

    Instruction *target = analyzeSwitch(SW, V);
    if (!target)
      continue;

    matches.push_back({V, baseShift, target});
  }

  if (matches.empty())
    return PreservedAnalyses::all();

  for (auto &m : matches) {
    // Insert at the first valid point in the target's block (after phis).
    BasicBlock *targetBB = m.target->getParent();
    Instruction *insertPt = &*targetBB->getFirstInsertionPt();
    IRBuilder<> B(insertPt);
    Value *shift_amt = B.CreateLShr(m.V, uint64_t(60), "hash.shift");
    Value *result = B.CreateLShr(m.baseShift, shift_amt, "hash.shr");

    m.target->replaceAllUsesWith(result);
    changed = true;
  }

  return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

}  // namespace omill

#include "omill/Passes/MergeBytePhis.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;
using namespace llvm::PatternMatch;

namespace omill {

namespace {

struct ByteSlot {
  PHINode *Phi = nullptr;
  unsigned ShiftAmount = 0;
  uint64_t Mask = ~0ULL;
};

/// Walk an OR tree collecting byte-slot contributions.
/// Depth-limited to prevent stack overflow on complex IR.
bool collectOrTree(Value *V, SmallVectorImpl<ByteSlot> &Slots,
                   BasicBlock *PhiBB,
                   SmallDenseSet<Value *, 16> &Visited,
                   unsigned Depth = 0) {
  if (Depth > 16 || !Visited.insert(V).second)
    return false;

  // Only follow OR chains within the same block.
  auto *I = dyn_cast<Instruction>(V);
  if (!I || I->getParent() != PhiBB) {
    // Could still be a PHI in PhiBB.
    if (auto *Phi = dyn_cast<PHINode>(V)) {
      if (Phi->getParent() == PhiBB) {
        ByteSlot Slot;
        Slot.Phi = Phi;
        Slot.ShiftAmount = 0;
        Slot.Mask = ~0ULL;
        Slots.push_back(Slot);
        return true;
      }
    }
    return false;
  }

  // Recurse into OR trees.
  if (auto *BO = dyn_cast<BinaryOperator>(I)) {
    if (BO->getOpcode() == Instruction::Or) {
      return collectOrTree(BO->getOperand(0), Slots, PhiBB, Visited, Depth+1) &&
             collectOrTree(BO->getOperand(1), Slots, PhiBB, Visited, Depth+1);
    }
  }

  // Leaf: unpack shl/and/zext/trunc wrapping a PHI.
  Value *Cur = V;
  uint64_t ShiftAmt = 0;
  uint64_t MaskVal = ~0ULL;

  // Match and(X, mask)
  const APInt *MaskAP;
  Value *Inner;
  if (match(Cur, m_And(m_Value(Inner), m_APInt(MaskAP)))) {
    MaskVal = MaskAP->getZExtValue();
    Cur = Inner;
  }

  // Match shl(X, C)
  const APInt *ShiftAP;
  if (match(Cur, m_Shl(m_Value(Inner), m_APInt(ShiftAP)))) {
    ShiftAmt = ShiftAP->getZExtValue();
    Cur = Inner;
  }

  // Match zext
  if (auto *ZI = dyn_cast<ZExtInst>(Cur))
    Cur = ZI->getOperand(0);

  // Match trunc
  if (auto *TI = dyn_cast<TruncInst>(Cur))
    Cur = TI->getOperand(0);

  auto *Phi = dyn_cast<PHINode>(Cur);
  if (!Phi || Phi->getParent() != PhiBB)
    return false;

  ByteSlot Slot;
  Slot.Phi = Phi;
  Slot.ShiftAmount = ShiftAmt;
  Slot.Mask = MaskVal;
  Slots.push_back(Slot);
  return true;
}

PHINode *tryCreateMergedPhi(SmallVectorImpl<ByteSlot> &Slots,
                            BasicBlock *PhiBB, Type *ResultTy) {
  if (Slots.empty())
    return nullptr;

  unsigned NumPreds = Slots[0].Phi->getNumIncomingValues();

  // All component PHIs must have the same predecessor list.
  for (auto &S : Slots) {
    if (S.Phi->getNumIncomingValues() != NumPreds)
      return nullptr;
    for (unsigned i = 0; i < NumPreds; ++i) {
      if (S.Phi->getIncomingBlock(i) != Slots[0].Phi->getIncomingBlock(i))
        return nullptr;
    }
  }

  // Validate predecessor count matches actual block predecessors.
  unsigned ActualPreds = 0;
  for ([[maybe_unused]] auto *P : predecessors(PhiBB))
    ++ActualPreds;
  if (ActualPreds != NumPreds)
    return nullptr;

  llvm::sort(Slots, [](const ByteSlot &A, const ByteSlot &B) {
    return A.ShiftAmount < B.ShiftAmount;
  });

  auto *MergedPhi = PHINode::Create(ResultTy, NumPreds, "merged.phi");
  MergedPhi->insertBefore(PhiBB->begin());

  for (unsigned i = 0; i < NumPreds; ++i) {
    auto *PredBB = Slots[0].Phi->getIncomingBlock(i);
    auto *Term = PredBB->getTerminator();
    IRBuilder<> Builder(Term);

    Value *Assembled = ConstantInt::get(ResultTy, 0);
    for (auto &S : Slots) {
      Value *V = S.Phi->getIncomingValue(i);
      if (V->getType() != ResultTy) {
        unsigned SrcBits = V->getType()->getScalarSizeInBits();
        unsigned DstBits = ResultTy->getScalarSizeInBits();
        if (SrcBits < DstBits)
          V = Builder.CreateZExt(V, ResultTy);
        else
          V = Builder.CreateTrunc(V, ResultTy);
      }
      if (S.ShiftAmount > 0)
        V = Builder.CreateShl(V, S.ShiftAmount);
      if (S.Mask != ~0ULL)
        V = Builder.CreateAnd(V, S.Mask);
      Assembled = Builder.CreateOr(Assembled, V);
    }
    MergedPhi->addIncoming(Assembled, PredBB);
  }

  return MergedPhi;
}

}  // anonymous namespace

PreservedAnalyses MergeBytePhisPass::run(Function &F,
                                         FunctionAnalysisManager &) {
  // Only run on native wrapper functions — ISEL stubs have massive OR trees
  // that blow the stack.
  if (!F.getName().ends_with("_native"))
    return PreservedAnalyses::all();

  bool Changed = false;
  unsigned Merged = 0;
  for (auto &BB : F) {
    SmallVector<Instruction *, 8> Worklist;
    for (auto &I : BB) {
      auto *BO = dyn_cast<BinaryOperator>(&I);
      if (!BO || BO->getOpcode() != Instruction::Or)
        continue;

      // Only consider root ORs (not consumed by another OR in same BB).
      bool IsRoot = true;
      for (auto *U : BO->users()) {
        if (auto *UBO = dyn_cast<BinaryOperator>(U)) {
          if (UBO->getOpcode() == Instruction::Or &&
              UBO->getParent() == &BB) {
            IsRoot = false;
            break;
          }
        }
      }
      if (IsRoot)
        Worklist.push_back(BO);
    }

    for (auto *OrRoot : Worklist) {
      SmallVector<ByteSlot, 8> Slots;
      SmallDenseSet<Value *, 16> Visited;
      BasicBlock *PhiBB = OrRoot->getParent();

      if (!collectOrTree(OrRoot, Slots, PhiBB, Visited))
        continue;
      if (Slots.size() < 2)
        continue;

      // All PHIs must be distinct.
      SmallDenseSet<PHINode *, 8> Seen;
      bool Unique = true;
      for (auto &S : Slots) {
        if (!Seen.insert(S.Phi).second) {
          Unique = false;
          break;
        }
      }
      if (!Unique)
        continue;

      auto *MergedPhi = tryCreateMergedPhi(Slots, PhiBB, OrRoot->getType());
      if (!MergedPhi)
        continue;

      OrRoot->replaceAllUsesWith(MergedPhi);
      Changed = true;
      ++Merged;
    }
  }

  if (!Changed)
    return PreservedAnalyses::all();

  // Clean up dead instructions.
  bool Deleted = true;
  unsigned TotalDeleted = 0;
  while (Deleted) {
    Deleted = false;
    for (auto &BB : F) {
      for (auto It = BB.begin(); It != BB.end(); ) {
        auto &I = *It++;
        if (isa<PHINode>(&I))
          continue;
        if (I.use_empty() && !I.isTerminator() && !I.mayHaveSideEffects()) {
          I.eraseFromParent();
          Deleted = true;
          ++TotalDeleted;
        }
      }
    }
  }

  llvm::errs() << "[MergeBytePhis] Merged " << Merged << " or-trees, "
               << "deleted " << TotalDeleted << " dead instructions\n";
  return PreservedAnalyses::none();
}

}  // namespace omill

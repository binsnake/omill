#include "omill/Passes/TypeRecovery.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PatternMatch.h>

namespace omill {
namespace {

using namespace llvm::PatternMatch;

/// Try to decompose an integer value into (pointer_base, byte_offset).
/// Returns true if the value is derived from a ptrtoint with constant offset
/// arithmetic.  Offset may be zero (pure ptrtoint case).
bool decomposePointerArith(llvm::Value *V, llvm::Value *&Base,
                           int64_t &Offset) {
  // Direct ptrtoint.
  if (auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(V)) {
    Base = PTI->getPointerOperand();
    Offset = 0;
    return true;
  }

  // add(X, const) or add(const, X) — recurse on the non-constant operand.
  llvm::Value *LHS = nullptr;
  llvm::Value *RHS = nullptr;
  if (match(V, m_Add(m_Value(LHS), m_Value(RHS)))) {
    auto *CI = llvm::dyn_cast<llvm::ConstantInt>(RHS);
    if (!CI)
      CI = llvm::dyn_cast<llvm::ConstantInt>(LHS);
    llvm::Value *Other = CI == RHS ? LHS : (CI ? RHS : nullptr);
    if (CI && Other) {
      if (decomposePointerArith(Other, Base, Offset)) {
        Offset += CI->getSExtValue();
        return true;
      }
    }
  }

  // sub(X, const) — recurse on X.
  if (match(V, m_Sub(m_Value(LHS), m_Value(RHS)))) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(RHS)) {
      if (decomposePointerArith(LHS, Base, Offset)) {
        Offset -= CI->getSExtValue();
        return true;
      }
    }
  }

  // or(X, const) where const bits don't overlap X's known bits — common
  // pattern from alignment masking that's effectively add.
  if (match(V, m_Or(m_Value(LHS), m_Value(RHS)))) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(RHS)) {
      if (decomposePointerArith(LHS, Base, Offset)) {
        // Only safe when or is effectively add (disjoint bits).
        // Conservatively handle small offsets from alignment (0-7).
        int64_t val = CI->getSExtValue();
        if (val >= 0 && val < 8) {
          Offset += val;
          return true;
        }
      }
    }
  }

  return false;
}

/// Fold ptrtoint(inttoptr(x)) → x.
bool foldPtrToIntOfIntToPtr(
    llvm::Function &F,
    llvm::SmallVectorImpl<llvm::Instruction *> &Dead) {
  bool changed = false;
  for (auto it = llvm::inst_begin(F), end = llvm::inst_end(F); it != end;
       ++it) {
    auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(&*it);
    if (!PTI)
      continue;

    auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(PTI->getOperand(0));
    if (!ITP)
      continue;

    auto *intVal = ITP->getOperand(0);
    if (intVal->getType() == PTI->getType()) {
      PTI->replaceAllUsesWith(intVal);
      Dead.push_back(PTI);
      if (ITP->use_empty())
        Dead.push_back(ITP);
      changed = true;
    }
  }
  return changed;
}

/// Fold inttoptr(ptrtoint(x)) → x.
bool foldIntToPtrOfPtrToInt(
    llvm::Function &F,
    llvm::SmallVectorImpl<llvm::Instruction *> &Dead) {
  bool changed = false;
  for (auto it = llvm::inst_begin(F), end = llvm::inst_end(F); it != end;
       ++it) {
    auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&*it);
    if (!ITP)
      continue;

    auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(ITP->getOperand(0));
    if (!PTI)
      continue;

    auto *origPtr = PTI->getPointerOperand();
    if (origPtr->getType() == ITP->getType()) {
      ITP->replaceAllUsesWith(origPtr);
      Dead.push_back(ITP);
      if (PTI->use_empty())
        Dead.push_back(PTI);
      changed = true;
    }
  }
  return changed;
}

/// Fold inttoptr(add(ptrtoint(p), const)) → GEP i8, p, const.
/// Handles multi-layer add/sub chains via decomposePointerArith.
bool foldPointerArithToGEP(
    llvm::Function &F,
    llvm::SmallVectorImpl<llvm::Instruction *> &Dead) {
  bool changed = false;
  for (auto it = llvm::inst_begin(F), end = llvm::inst_end(F); it != end;
       ++it) {
    auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&*it);
    if (!ITP)
      continue;

    // Skip if already handled by simple round-trip fold.
    if (llvm::isa<llvm::PtrToIntInst>(ITP->getOperand(0)))
      continue;

    llvm::Value *base = nullptr;
    int64_t offset = 0;
    if (!decomposePointerArith(ITP->getOperand(0), base, offset))
      continue;

    // Build GEP i8, base, offset.
    llvm::IRBuilder<> B(ITP);
    llvm::Value *result;
    if (offset == 0) {
      result = base;
    } else {
      result = B.CreateGEP(B.getInt8Ty(), base, B.getInt64(offset),
                           "ptr.recover");
    }
    if (result->getType() != ITP->getType())
      continue;

    ITP->replaceAllUsesWith(result);
    Dead.push_back(ITP);
    changed = true;
  }
  return changed;
}

/// Erase dead instructions in reverse order, skipping any already erased.
void eraseDeadInstructions(
    llvm::SmallVectorImpl<llvm::Instruction *> &Dead) {
  // Reverse to avoid use-before-erase.
  for (auto it = Dead.rbegin(); it != Dead.rend(); ++it) {
    auto *I = *it;
    if (I->use_empty()) {
      I->eraseFromParent();
    }
  }
  Dead.clear();
}

}  // namespace

llvm::PreservedAnalyses TypeRecoveryPass::run(llvm::Function &F,
                                              llvm::FunctionAnalysisManager &) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  bool changed = false;
  llvm::SmallVector<llvm::Instruction *, 16> dead;

  // Iterate to fixpoint — folding one layer may expose another.
  for (unsigned iter = 0; iter < 8; ++iter) {
    bool progress = false;
    progress |= foldPtrToIntOfIntToPtr(F, dead);
    progress |= foldIntToPtrOfPtrToInt(F, dead);
    progress |= foldPointerArithToGEP(F, dead);
    eraseDeadInstructions(dead);

    if (!progress)
      break;
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

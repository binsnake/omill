#include "omill/Passes/FoldConstantVectorChains.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Debug.h>

#define DEBUG_TYPE "fold-const-vec"

namespace omill {

namespace {

/// Trace a single element of a vector value through nested shufflevectors
/// and insertelement chains to find the ultimate constant source.
/// Returns the constant value for that element, or nullptr if non-constant.
llvm::Constant *traceElement(llvm::Value *V, unsigned idx, unsigned depth) {
  if (depth > 16)
    return nullptr;

  // Already a constant vector — extract the element.
  if (auto *C = llvm::dyn_cast<llvm::Constant>(V)) {
    auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(V->getType());
    if (!VTy)
      return nullptr;

    if (auto *CV = llvm::dyn_cast<llvm::ConstantVector>(C))
      return CV->getAggregateElement(idx);
    if (auto *CDV = llvm::dyn_cast<llvm::ConstantDataVector>(C))
      return CDV->getElementAsConstant(idx);
    if (llvm::isa<llvm::ConstantAggregateZero>(C))
      return llvm::Constant::getNullValue(VTy->getElementType());
    if (llvm::isa<llvm::PoisonValue>(C))
      return llvm::PoisonValue::get(VTy->getElementType());
    if (llvm::isa<llvm::UndefValue>(C))
      return llvm::UndefValue::get(VTy->getElementType());
    return nullptr;
  }

  // Trace through shufflevector.
  if (auto *SV = llvm::dyn_cast<llvm::ShuffleVectorInst>(V)) {
    auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(V->getType());
    if (!VTy)
      return nullptr;

    int mask = SV->getMaskValue(idx);
    if (mask < 0)
      return llvm::PoisonValue::get(VTy->getElementType());

    auto *SrcTy =
        llvm::cast<llvm::FixedVectorType>(SV->getOperand(0)->getType());
    unsigned num = SrcTy->getNumElements();

    if (static_cast<unsigned>(mask) < num)
      return traceElement(SV->getOperand(0), mask, depth + 1);
    else
      return traceElement(SV->getOperand(1), mask - num, depth + 1);
  }

  // Trace through insertelement.
  if (auto *IE = llvm::dyn_cast<llvm::InsertElementInst>(V)) {
    auto *idx_val = llvm::dyn_cast<llvm::ConstantInt>(IE->getOperand(2));
    if (!idx_val)
      return nullptr;

    if (idx_val->getZExtValue() == idx) {
      // This element was inserted — check if it's a constant.
      if (auto *C = llvm::dyn_cast<llvm::Constant>(IE->getOperand(1)))
        return C;
      return nullptr;
    }
    // Not this element — trace through to the base vector.
    return traceElement(IE->getOperand(0), idx, depth + 1);
  }

  // Non-constant / unhandled instruction.
  return nullptr;
}

}  // namespace

llvm::PreservedAnalyses FoldConstantVectorChainsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end();) {
      auto *I = &*it++;

      // Only try to fold shufflevector and insertelement.
      if (!llvm::isa<llvm::ShuffleVectorInst>(I) &&
          !llvm::isa<llvm::InsertElementInst>(I))
        continue;

      auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(I->getType());
      if (!VTy)
        continue;

      unsigned num_elems = VTy->getNumElements();
      llvm::SmallVector<llvm::Constant *, 16> elements;
      bool all_const = true;

      for (unsigned i = 0; i < num_elems; ++i) {
        auto *elem = traceElement(I, i, 0);
        if (!elem) {
          all_const = false;
          break;
        }
        elements.push_back(elem);
      }

      if (!all_const)
        continue;

      LLVM_DEBUG(llvm::dbgs() << "[FoldConstVec] folding: " << *I << "\n");

      auto *folded = llvm::ConstantVector::get(elements);
      I->replaceAllUsesWith(folded);
      I->eraseFromParent();
      changed = true;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

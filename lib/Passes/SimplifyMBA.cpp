#include "omill/Passes/SimplifyMBA.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Transforms/Utils/Local.h>

#include "omill/Simplifier/LLVMTranslator.h"

#define DEBUG_TYPE "simplify-mba"

namespace omill {

/// Returns true if V is part of an expression interior (BinaryOperator or
/// integer CastInst).
static bool isExprInterior(llvm::Value *V) {
  if (llvm::isa<llvm::BinaryOperator>(V))
    return true;
  if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V))
    return CI->getType()->isIntegerTy() && CI->getOperand(0)->getType()->isIntegerTy();
  return false;
}

/// Returns true if this instruction is an expression root: an integer
/// BinaryOperator where at least one user is NOT an expression interior.
static bool isExprRoot(llvm::Instruction &I) {
  if (!llvm::isa<llvm::BinaryOperator>(I))
    return false;
  if (!I.getType()->isIntegerTy())
    return false;

  for (auto *U : I.users()) {
    if (!isExprInterior(U))
      return true;
  }
  return false;
}

llvm::PreservedAnalyses SimplifyMBAPass::run(llvm::Function &F,
                                              llvm::FunctionAnalysisManager &AM) {
  bool changed = false;
  LLVMTranslator translator;
  llvm::SmallVector<llvm::Instruction *, 16> dead;

  // Collect roots first (avoid iterator invalidation).
  llvm::SmallVector<llvm::Instruction *, 32> roots;
  for (auto &BB : F)
    for (auto &I : BB)
      if (isExprRoot(I))
        roots.push_back(&I);

  for (auto *root : roots) {
    llvm::IRBuilder<> B(root);
    llvm::Value *simplified = translator.simplify(root, B);
    if (simplified) {
      root->replaceAllUsesWith(simplified);
      dead.push_back(root);
      changed = true;
    }
    translator.reset();
  }

  for (auto *I : dead)
    llvm::RecursivelyDeleteTriviallyDeadInstructions(I);

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#include "omill/Passes/SimplifyMBA.h"

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Debug.h>
#include <llvm/Transforms/Utils/Local.h>

#include "omill/Simplifier/LLVMTranslator.h"

#define DEBUG_TYPE "simplify-mba"

namespace omill {

/// Minimum number of expression-tree nodes required for an MBA candidate.
static constexpr unsigned kMinMBANodes = 3;

/// Returns true if V is part of an expression interior (BinaryOperator or
/// integer CastInst).
static bool isExprInterior(llvm::Value *V) {
  if (llvm::isa<llvm::BinaryOperator>(V))
    return true;
  if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V))
    return CI->getType()->isIntegerTy() &&
           CI->getOperand(0)->getType()->isIntegerTy();
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

/// Walk the expression tree rooted at V and check whether it looks like an MBA
/// candidate: has both arithmetic (add/sub/mul) and bitwise (and/or/xor) ops,
/// and is large enough to justify the EqSat FFI overhead.
///
/// Pure-arithmetic or pure-bitwise trees are left for InstCombine/GVN.
static bool isMBACandidate(llvm::Value *root) {
  unsigned count = 0;
  bool has_arith = false;
  bool has_bitwise = false;

  llvm::SmallVector<llvm::Value *, 16> worklist;
  llvm::SmallPtrSet<llvm::Value *, 16> visited;
  worklist.push_back(root);

  while (!worklist.empty()) {
    llvm::Value *V = worklist.pop_back_val();
    if (!visited.insert(V).second)
      continue;

    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
      ++count;
      switch (BO->getOpcode()) {
      case llvm::Instruction::Add:
      case llvm::Instruction::Sub:
      case llvm::Instruction::Mul:
        has_arith = true;
        break;
      case llvm::Instruction::And:
      case llvm::Instruction::Or:
      case llvm::Instruction::Xor:
        has_bitwise = true;
        break;
      default:
        break;
      }
      for (auto &Op : BO->operands())
        if (isExprInterior(Op.get()))
          worklist.push_back(Op.get());
    } else if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V)) {
      if (CI->getType()->isIntegerTy() &&
          CI->getOperand(0)->getType()->isIntegerTy()) {
        ++count;
        if (isExprInterior(CI->getOperand(0)))
          worklist.push_back(CI->getOperand(0));
      }
    }

    // Early-out: once we know it's mixed and large enough, no need to keep
    // walking.
    if (has_arith && has_bitwise && count >= kMinMBANodes)
      return true;
  }

  return has_arith && has_bitwise && count >= kMinMBANodes;
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
      if (isExprRoot(I) && isMBACandidate(&I))
        roots.push_back(&I);

  LLVM_DEBUG(llvm::dbgs() << "SimplifyMBA: " << roots.size()
                          << " MBA candidates in " << F.getName() << "\n");

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

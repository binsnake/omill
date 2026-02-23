#include "omill/Passes/SynthesizeFlags.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>

namespace omill {

namespace {

/// Check if a value transitively traces back to a given instruction
/// within a bounded depth (for verifying that two flag operands derive
/// from the same arithmetic operation).
bool tracesTo(llvm::Value *V, llvm::Instruction *target, unsigned depth = 0) {
  if (depth > 12)
    return false;
  if (V == target)
    return true;
  auto *I = llvm::dyn_cast<llvm::Instruction>(V);
  if (!I)
    return false;
  for (auto &op : I->operands())
    if (tracesTo(op.get(), target, depth + 1))
      return true;
  return false;
}

/// Match the sign flag pattern: icmp slt (sub L, R), 0
///
/// Returns the sub instruction, or nullptr if no match.
/// On match, lhs and rhs are set to the sub's operands.
llvm::BinaryOperator *matchSignFlag(llvm::Value *V, llvm::Value *&lhs,
                                    llvm::Value *&rhs) {
  auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(V);
  if (!cmp || cmp->getPredicate() != llvm::CmpInst::ICMP_SLT)
    return nullptr;
  auto *zero = llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(1));
  if (!zero || !zero->isZero())
    return nullptr;
  auto *sub = llvm::dyn_cast<llvm::BinaryOperator>(cmp->getOperand(0));
  if (!sub || sub->getOpcode() != llvm::Instruction::Sub)
    return nullptr;
  lhs = sub->getOperand(0);
  rhs = sub->getOperand(1);
  return sub;
}

/// Try to synthesize a signed comparison from xor(SF, OF).
///
/// Pattern: xor i1 %sf, %of
///   where %sf = icmp slt (sub %lhs, %rhs), 0    [sign flag]
///   and   %of traces back to the same sub         [overflow flag]
///
/// Result: icmp slt %lhs, %rhs
bool trySynthesizeSignedLessThan(llvm::BinaryOperator *xorInst,
                                 llvm::SmallVectorImpl<llvm::Instruction *>
                                     &to_erase) {
  if (xorInst->getOpcode() != llvm::Instruction::Xor)
    return false;
  if (!xorInst->getType()->isIntegerTy(1))
    return false;

  llvm::Value *lhs = nullptr, *rhs = nullptr;
  llvm::BinaryOperator *sub = nullptr;
  llvm::Value *other = nullptr;

  // Try both operand orderings for the sign flag.
  sub = matchSignFlag(xorInst->getOperand(0), lhs, rhs);
  other = xorInst->getOperand(1);
  if (!sub) {
    sub = matchSignFlag(xorInst->getOperand(1), lhs, rhs);
    other = xorInst->getOperand(0);
  }
  if (!sub)
    return false;

  // Verify the other operand (overflow flag) traces to the same sub.
  // The overflow formula for subtraction uses lhs, rhs, and res (the sub
  // result) via shift/xor/add chains.  A depth-limited trace check is
  // sufficient to confirm derivation from the same arithmetic op.
  if (!tracesTo(other, sub))
    return false;

  // Replace xor(SF, OF) with icmp slt lhs, rhs.
  llvm::IRBuilder<> B(xorInst);
  auto *newCmp = B.CreateICmpSLT(lhs, rhs, "slt.synth");
  xorInst->replaceAllUsesWith(newCmp);
  to_erase.push_back(xorInst);
  return true;
}

}  // namespace

llvm::PreservedAnalyses SynthesizeFlagsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &FAM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  bool changed = false;
  llvm::SmallVector<llvm::Instruction *, 16> to_erase;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!binOp)
        continue;

      if (trySynthesizeSignedLessThan(binOp, to_erase))
        changed = true;
    }
  }

  for (auto *I : to_erase)
    I->eraseFromParent();

  if (!changed)
    return llvm::PreservedAnalyses::all();
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

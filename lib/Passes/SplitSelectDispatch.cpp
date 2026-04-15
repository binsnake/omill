#include "omill/Passes/SplitSelectDispatch.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Check if a CallInst is a dispatch intrinsic (dispatch_call or dispatch_jump).
bool isDispatchIntrinsic(llvm::CallInst *CI) {
  auto *callee = CI->getCalledFunction();
  if (!callee)
    return false;
  return isDispatchCallName(callee->getName()) ||
         isDispatchJumpName(callee->getName());
}

/// Try to split dispatch_call/dispatch_jump(select(cond, A, B)) where both
/// arms are ConstantInt.  Returns true if a split was performed.
bool trySplitSelectDispatch(llvm::CallInst *CI) {
  auto *sel = llvm::dyn_cast<llvm::SelectInst>(CI->getArgOperand(1));
  if (!sel)
    return false;

  auto *true_val = llvm::dyn_cast<llvm::ConstantInt>(sel->getTrueValue());
  auto *false_val = llvm::dyn_cast<llvm::ConstantInt>(sel->getFalseValue());
  if (!true_val || !false_val)
    return false;

  // Don't split if both arms are the same constant — just replace.
  if (true_val->getValue() == false_val->getValue()) {
    CI->setArgOperand(1, true_val);
    return true;
  }

  auto *BB = CI->getParent();
  auto *F = BB->getParent();
  auto &Ctx = F->getContext();

  // Split the block: everything before CI stays in BB, CI and after go to a
  // new "tail" block.  We then replace the tail with two dispatch blocks.
  auto *cond = sel->getCondition();

  // Create two new blocks for the true/false dispatch paths.
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "select.true", F);
  auto *false_bb = llvm::BasicBlock::Create(Ctx, "select.false", F);

  // Split BB right before CI.
  auto *tail = BB->splitBasicBlock(CI->getIterator(), "select.split");

  // Replace the unconditional branch that splitBasicBlock created with
  // a conditional branch on the select condition.
  BB->getTerminator()->eraseFromParent();
  llvm::BranchInst::Create(true_bb, false_bb, cond, BB);

  // Clone the dispatch call into each branch with the constant target.
  for (auto &[target_bb, target_val] :
       {std::pair<llvm::BasicBlock *, llvm::ConstantInt *>{true_bb, true_val},
        {false_bb, false_val}}) {
    llvm::IRBuilder<> Builder(target_bb);
    llvm::SmallVector<llvm::Value *, 4> args;
    for (unsigned i = 0; i < CI->arg_size(); ++i) {
      if (i == 1)
        args.push_back(target_val);
      else
        args.push_back(CI->getArgOperand(i));
    }
    auto *new_call =
        Builder.CreateCall(CI->getCalledFunction(), args);
    new_call->setTailCallKind(CI->getTailCallKind());
    // Copy metadata.
    llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 4> mds;
    CI->getAllMetadata(mds);
    for (auto &[kind, md] : mds)
      new_call->setMetadata(kind, md);

    // If the original call had uses (dispatch_call returns Memory*), we
    // need a PHI to merge.  For now, branch to the original tail which
    // will be cleaned up by SimplifyCFG.
    Builder.CreateBr(tail);
  }

  // Fix up the original tail block: if the dispatch call had users,
  // create a PHI to merge the results from both paths.
  if (!CI->use_empty()) {
    auto *phi = llvm::PHINode::Create(CI->getType(), 2, "select.result");
    phi->insertBefore(tail->begin());
    // Find the call in each predecessor.
    for (auto *pred : llvm::predecessors(tail)) {
      llvm::CallInst *pred_call = nullptr;
      for (auto &I : *pred)
        if (auto *c = llvm::dyn_cast<llvm::CallInst>(&I))
          pred_call = c;
      phi->addIncoming(pred_call ? (llvm::Value *)pred_call
                                 : llvm::UndefValue::get(CI->getType()),
                       pred);
    }
    CI->replaceAllUsesWith(phi);
  }
  CI->eraseFromParent();

  return true;
}

/// Try to split dispatch on a PHINode with N <= 8 constant incoming values.
/// Creates a switch instruction on the PHI value.
bool trySplitPHIDispatch(llvm::CallInst *CI) {
  auto *phi = llvm::dyn_cast<llvm::PHINode>(CI->getArgOperand(1));
  if (!phi)
    return false;

  unsigned N = phi->getNumIncomingValues();
  if (N < 2 || N > 8)
    return false;

  // All incoming values must be distinct ConstantInt.
  llvm::SmallVector<llvm::ConstantInt *, 8> vals;
  llvm::SmallDenseSet<uint64_t, 8> seen;
  for (unsigned i = 0; i < N; ++i) {
    auto *ci = llvm::dyn_cast<llvm::ConstantInt>(phi->getIncomingValue(i));
    if (!ci)
      return false;
    vals.push_back(ci);
    seen.insert(ci->getZExtValue());
  }

  // If all arms are the same constant, just replace directly.
  if (seen.size() == 1) {
    CI->setArgOperand(1, vals[0]);
    return true;
  }

  auto *BB = CI->getParent();
  auto *F = BB->getParent();
  auto &Ctx = F->getContext();

  // Create switch on the PHI value.
  auto *tail = BB->splitBasicBlock(CI->getIterator(), "phi.split");
  BB->getTerminator()->eraseFromParent();

  // Default case goes to tail (retains original dispatch as fallback).
  auto *sw = llvm::SwitchInst::Create(phi, tail, seen.size(), BB);

  // Create one case block per unique constant value.
  llvm::DenseMap<uint64_t, llvm::BasicBlock *> case_blocks;
  for (uint64_t v : seen) {
    auto *case_bb = llvm::BasicBlock::Create(
        Ctx, "phi.case." + llvm::Twine::utohexstr(v), F);
    llvm::IRBuilder<> Builder(case_bb);

    auto *target_val = llvm::ConstantInt::get(phi->getType(), v);
    llvm::SmallVector<llvm::Value *, 4> args;
    for (unsigned i = 0; i < CI->arg_size(); ++i) {
      if (i == 1)
        args.push_back(target_val);
      else
        args.push_back(CI->getArgOperand(i));
    }
    auto *new_call = Builder.CreateCall(CI->getCalledFunction(), args);
    new_call->setTailCallKind(CI->getTailCallKind());
    Builder.CreateBr(tail);

    sw->addCase(llvm::cast<llvm::ConstantInt>(
                    llvm::ConstantInt::get(phi->getType(), v)),
                case_bb);
    case_blocks[v] = case_bb;
  }

  // Replace uses of the original dispatch call with a PHI merging all paths.
  if (!CI->use_empty()) {
    auto *merge_phi =
        llvm::PHINode::Create(CI->getType(), case_blocks.size() + 1,
                              "phi.dispatch.result");
    merge_phi->insertBefore(tail->begin());
    for (auto *pred : llvm::predecessors(tail)) {
      llvm::CallInst *pred_call = nullptr;
      for (auto &I : *pred)
        if (auto *c = llvm::dyn_cast<llvm::CallInst>(&I))
          pred_call = c;
      merge_phi->addIncoming(
          pred_call ? (llvm::Value *)pred_call
                    : llvm::UndefValue::get(CI->getType()),
          pred);
    }
    CI->replaceAllUsesWith(merge_phi);
  }
  CI->eraseFromParent();

  return true;
}

}  // namespace

llvm::PreservedAnalyses SplitSelectDispatchPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  // Collect candidates first to avoid iterator invalidation.
  llvm::SmallVector<llvm::CallInst *, 8> candidates;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (isDispatchIntrinsic(CI))
          candidates.push_back(CI);

  for (auto *CI : candidates) {
    // Skip if already resolved to a constant.
    if (llvm::isa<llvm::ConstantInt>(CI->getArgOperand(1)))
      continue;

    changed |= trySplitSelectDispatch(CI);
    // If select split didn't apply, try PHI split.
    // (The CI may have been erased by the select split, so check parent.)
    if (!changed || CI->getParent())
      changed |= trySplitPHIDispatch(CI);
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

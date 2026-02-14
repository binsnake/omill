#include "omill/Passes/ResolveLazyImports.h"

#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/ValueHandle.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

namespace omill {

namespace {

/// x86-64 State struct RAX offset (GPRs start at 2208, RAX is at +8).
static constexpr unsigned kRAXOffset = 2216;

/// Walk up the loop nest to find the outermost loop.
llvm::Loop *getOutermostLoop(llvm::Loop *L) {
  while (L->getParentLoop())
    L = L->getParentLoop();
  return L;
}

/// Find an __omill_dispatch_call in the given block.
llvm::CallInst *findDispatchCall(llvm::BasicBlock *BB) {
  for (auto &I : *BB) {
    if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
      auto *callee = call->getCalledFunction();
      if (callee && callee->getName() == "__omill_dispatch_call")
        return call;
    }
  }
  return nullptr;
}

/// Check if a store's pointer operand is a GEP to State+offset.
bool isStoreToStateOffset(llvm::StoreInst *store, llvm::Value *state_ptr,
                          unsigned offset) {
  auto *gep = llvm::dyn_cast<llvm::GEPOperator>(store->getPointerOperand());
  if (!gep || gep->getPointerOperand() != state_ptr)
    return false;
  if (gep->getNumIndices() != 1)
    return false;
  auto *idx = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(1));
  return idx && idx->getZExtValue() == offset;
}

}  // namespace

llvm::PreservedAnalyses ResolveLazyImportsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  if (F.arg_size() == 0)
    return llvm::PreservedAnalyses::all();

  // Collect annotated icmps using WeakVH so handles become null if
  // instructions are deleted by EliminateUnreachableBlocks in a prior
  // iteration (multi-import functions).
  llvm::SmallVector<llvm::WeakVH, 4> annotated_vhs;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        if (icmp->getMetadata("omill.resolved_import"))
          annotated_vhs.push_back(icmp);
      }
    }
  }

  if (annotated_vhs.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &vh : annotated_vhs) {
    llvm::Value *v = vh;
    if (!v)
      continue;  // Deleted by a prior iteration
    auto *icmp = llvm::cast<llvm::ICmpInst>(v);

    auto *md = icmp->getMetadata("omill.resolved_import");
    if (!md || md->getNumOperands() < 2)
      continue;
    auto *fn_str = llvm::dyn_cast<llvm::MDString>(md->getOperand(1));
    if (!fn_str)
      continue;
    llvm::StringRef func_name = fn_str->getString();

    // Declare the resolved function as dllimport external.
    auto *fn_type = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
    auto fn_callee = M.getOrInsertFunction(func_name, fn_type);
    auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
    if (!fn)
      continue;
    fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);

    // Check if the icmp directly controls a conditional branch whose
    // true-successor contains an __omill_dispatch_call.  This means the
    // resolved import is actually CALLED (not just its address returned).
    llvm::BasicBlock *icmp_bb = icmp->getParent();
    auto *br = llvm::dyn_cast<llvm::BranchInst>(icmp_bb->getTerminator());
    llvm::CallInst *dispatch = nullptr;
    if (br && br->isConditional() && br->getCondition() == icmp) {
      dispatch = findDispatchCall(br->getSuccessor(0));
    }

    if (dispatch) {
      // === Import is called via __omill_dispatch_call ===
      //
      // Replace the dispatch_call's target address with the resolved import
      // and fold the hash comparison to true.  The PEB-walking loop becomes
      // single-iteration and LLVM will optimize it away.
      //
      // Also fix any subsequent stores to State+RAX in the same block:
      // the dispatch_call writes the call's return value to State+RAX
      // through the opaque state pointer, but the exit block's explicit
      // State stores may overwrite it with a stale value (from ordinal
      // resolution).  We insert a load of State+RAX right after the
      // dispatch_call and patch any later RAX stores to use that value.
      llvm::IRBuilder<> Builder(dispatch);
      auto *fn_addr = Builder.CreatePtrToInt(fn, Builder.getInt64Ty(),
                                             func_name.str() + ".addr");
      dispatch->setArgOperand(1, fn_addr);

      // Insert a load of State+RAX right after the dispatch_call to
      // capture its return value before it gets overwritten.
      auto *state_ptr = F.getArg(0);
      Builder.SetInsertPoint(dispatch->getNextNode());
      auto *rax_gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                        Builder.getInt64(kRAXOffset),
                                        "rax.gep.post.call");
      auto *rax_result = Builder.CreateLoad(Builder.getInt64Ty(), rax_gep,
                                            "rax.after.call");

      // Replace any subsequent stores to State+RAX in this block.
      llvm::BasicBlock *dispatch_bb = dispatch->getParent();
      bool past_load = false;
      for (auto &I : *dispatch_bb) {
        if (&I == rax_result) {
          past_load = true;
          continue;
        }
        if (!past_load)
          continue;
        if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (isStoreToStateOffset(store, state_ptr, kRAXOffset)) {
            store->setOperand(0, rax_result);
          }
        }
      }

      icmp->replaceAllUsesWith(llvm::ConstantInt::getTrue(Ctx));
      icmp->eraseFromParent();
      changed = true;
    } else {
      // === Terminal import (address resolved but not called) ===
      //
      // Create a fresh shortcut block that stores the resolved import
      // address to State+RAX and returns.  We bypass both the PEB-walking
      // loop AND its exit block (which contains ordinal/flag computations
      // that would reference now-undefined loop values).
      llvm::DominatorTree DT(F);
      llvm::LoopInfo LI(DT);

      llvm::Loop *inner_loop = LI.getLoopFor(icmp_bb);
      if (!inner_loop) {
        icmp->replaceAllUsesWith(llvm::ConstantInt::getTrue(Ctx));
        icmp->eraseFromParent();
        changed = true;
        continue;
      }

      llvm::Loop *outer_loop = getOutermostLoop(inner_loop);
      llvm::BasicBlock *preheader = outer_loop->getLoopPreheader();
      if (!preheader) {
        icmp->replaceAllUsesWith(llvm::ConstantInt::getTrue(Ctx));
        icmp->eraseFromParent();
        changed = true;
        continue;
      }

      auto *shortcut = llvm::BasicBlock::Create(Ctx, "resolved", &F);
      {
        llvm::IRBuilder<> Builder(shortcut);
        auto *state_ptr = F.getArg(0);
        auto *rax_gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                          Builder.getInt64(kRAXOffset));
        auto *fn_addr = Builder.CreatePtrToInt(fn, Builder.getInt64Ty(),
                                               func_name.str() + ".addr");
        Builder.CreateStore(fn_addr, rax_gep);
        Builder.CreateRet(llvm::PoisonValue::get(F.getReturnType()));
      }

      preheader->getTerminator()->eraseFromParent();
      llvm::BranchInst::Create(shortcut, preheader);
      llvm::EliminateUnreachableBlocks(F);
      changed = true;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

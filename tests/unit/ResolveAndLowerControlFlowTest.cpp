#include "omill/Passes/ResolveAndLowerControlFlow.h"

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

class ResolveAndLowerControlFlowTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  llvm::Function *createDispatchCallDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_call", M);
  }

  llvm::Function *createDispatchJumpDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_jump", M);
  }

  void runResolvePass(llvm::Module *M) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass([] { return omill::BinaryMemoryAnalysis(); });
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    (void)MAM.getResult<omill::BinaryMemoryAnalysis>(*M);
    (void)MAM.getResult<omill::LiftedFunctionAnalysis>(*M);

    llvm::ModulePassManager MPM;
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(
        omill::ResolveAndLowerControlFlowPass(
            omill::ResolvePhases::ResolveTargets)));
    MPM.run(*M, MAM);
  }

  bool hasDirectCallTo(llvm::Function *F, llvm::StringRef fn_name) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == fn_name)
          return true;
      }
    }
    return false;
  }

  unsigned countDispatchCalls(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_call")
          ++count;
      }
    }
    return count;
  }

  unsigned countDispatchJumps(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_jump")
          ++count;
      }
    }
    return count;
  }

  bool hasBranchTo(llvm::Function *F, llvm::StringRef block_name) {
    for (auto &BB : *F) {
      auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
      if (!br || br->isConditional())
        continue;
      if (br->getSuccessor(0)->getName() == block_name)
        return true;
    }
    return false;
  }
};

// dispatch_call with constant PC matching a lifted function → direct call.
TEST_F(ResolveAndLowerControlFlowTest, ConstantDispatchCall_Resolved) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Target lifted function at 0x402000.
  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_402000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Caller with dispatch_call(state, 0x402000, mem).
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), B.getInt64(0x402000), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchCalls(F));

  runResolvePass(M.get());

  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_TRUE(hasDirectCallTo(F, "sub_402000"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// dispatch_jump with constant PC matching a BB in the same function → branch.
TEST_F(ResolveAndLowerControlFlowTest, ConstantDispatchJump_BecomesBranch) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchJumpDecl(*M);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *target_bb = llvm::BasicBlock::Create(Ctx, "block_401020", F);

  // Target block returns.
  llvm::IRBuilder<>(target_bb).CreateRet(F->getArg(2));

  // Entry: dispatch_jump(state, 0x401020, mem) + ret.
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), B.getInt64(0x401020), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchJumps(F));

  runResolvePass(M.get());

  EXPECT_EQ(0u, countDispatchJumps(F));
  EXPECT_TRUE(hasBranchTo(F, "block_401020"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveAndLowerControlFlowTest, PtrToIntDispatchJump_BecomesDirectCall) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchJumpDecl(*M);

  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::InternalLinkage,
                             "sub_402000__vm_1111", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  auto *F = llvm::Function::Create(liftedFnType(),
                                   llvm::Function::ExternalLinkage,
                                   "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  auto *target_ptr = B.CreatePtrToInt(target_fn, B.getInt64Ty());
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target_ptr, F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchJumps(F));

  runResolvePass(M.get());

  EXPECT_EQ(0u, countDispatchJumps(F));
  EXPECT_TRUE(hasDirectCallTo(F, "sub_402000__vm_1111"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}


// dispatch_jump with dynamic (non-constant) target → preserved.
TEST_F(ResolveAndLowerControlFlowTest, NonConstantDispatch_Preserved) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchJumpDecl(*M);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  // Target is a dynamic value (function arg), not a constant.
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), F->getArg(1), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchJumps(F));

  runResolvePass(M.get());

  // Dynamic target: unchanged.
  EXPECT_EQ(1u, countDispatchJumps(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// Declaration-only function → pass is a no-op (module adapter skips decls).
TEST_F(ResolveAndLowerControlFlowTest, DeclarationFunction_Skipped) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Function is declaration-only (no body).
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_401000", *M);

  EXPECT_TRUE(F->isDeclaration());

  runResolvePass(M.get());

  // Still a declaration, no crash.
  EXPECT_TRUE(F->isDeclaration());
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Function with no dispatch intrinsic calls → no change.
TEST_F(ResolveAndLowerControlFlowTest, NoDispatches_NoOp) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  // Just return mem directly — no dispatches.
  B.CreateRet(F->getArg(2));

  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_EQ(0u, countDispatchJumps(F));

  runResolvePass(M.get());

  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_EQ(0u, countDispatchJumps(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

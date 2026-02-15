#include "omill/Passes/LowerJump.h"

#include "omill/Analysis/LiftedFunctionMap.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerJumpTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerJumpPass());

    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    (void)MAM.getResult<omill::LiftedFunctionAnalysis>(*F->getParent());

    FPM.run(*F, FAM);
  }
};

TEST_F(LowerJumpTest, ConstantPCIntraFunctionBranch) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *lifted_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  // Declare __remill_jump
  M->getOrInsertFunction("__remill_jump", lifted_fn_ty);

  // Create lifted function with a target block
  auto *test_fn = llvm::Function::Create(
      lifted_fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  // Target block named with the PC address (remill convention)
  auto *target_bb =
      llvm::BasicBlock::Create(Ctx, "block_402000", test_fn);

  // Entry block: call __remill_jump with constant PC = 0x402000
  llvm::IRBuilder<> B(entry);
  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  auto *jump_fn = M->getFunction("__remill_jump");
  auto *result =
      B.CreateCall(jump_fn, {state, B.getInt64(0x402000), mem});
  B.CreateRet(result);

  // Target block just returns
  llvm::IRBuilder<> TB(target_bb);
  TB.CreateRet(test_fn->getArg(2));

  runPass(test_fn);

  // After: entry should contain a br to block_402000
  // (the old ret may still be present as dead code after the br)
  bool has_br_to_target = false;
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *br = llvm::dyn_cast<llvm::BranchInst>(&I)) {
      if (!br->isConditional() &&
          br->getSuccessor(0)->getName() == "block_402000")
        has_br_to_target = true;
    }
  }
  EXPECT_TRUE(has_br_to_target);

  // No more __remill_jump calls
  bool has_remill_jump = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__remill_jump")
          has_remill_jump = true;
  EXPECT_FALSE(has_remill_jump);
}

TEST_F(LowerJumpTest, DynamicJumpDispatcher) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *lifted_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  // Declare __remill_jump
  M->getOrInsertFunction("__remill_jump", lifted_fn_ty);

  // Create lifted function
  auto *test_fn = llvm::Function::Create(
      lifted_fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *pc = test_fn->getArg(1);  // dynamic PC
  auto *mem = test_fn->getArg(2);

  auto *jump_fn = M->getFunction("__remill_jump");
  auto *result = B.CreateCall(jump_fn, {state, pc, mem});
  B.CreateRet(result);

  runPass(test_fn);

  // After: should have __omill_dispatch_jump + ret
  bool has_dispatch = false;
  bool has_ret = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_dispatch_jump")
          has_dispatch = true;
      }
      if (llvm::isa<llvm::ReturnInst>(&I))
        has_ret = true;
    }
  }
  EXPECT_TRUE(has_dispatch);
  EXPECT_TRUE(has_ret);
}

}  // namespace

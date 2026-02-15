#include "omill/Passes/LowerFunctionCall.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>

namespace {

class LowerFunctionCallTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerFunctionCallPass());

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

    // Prime the analysis so getCachedResult works in the pass.
    (void)MAM.getResult<omill::LiftedFunctionAnalysis>(*F->getParent());

    FPM.run(*F, FAM);
  }
};

TEST_F(LowerFunctionCallTest, ConstantPCDirectCall) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *lifted_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  // Declare __remill_function_call
  M->getOrInsertFunction("__remill_function_call", lifted_fn_ty);

  // Create the target function: sub_401000
  auto *target_fn = llvm::Function::Create(
      lifted_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<> TB(target_entry);
  TB.CreateRet(target_fn->getArg(2));

  // Create the caller function
  auto *test_fn = llvm::Function::Create(
      lifted_fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Call __remill_function_call with constant PC = 0x401000
  auto *call_fn = M->getFunction("__remill_function_call");
  auto *result =
      B.CreateCall(call_fn, {state, B.getInt64(0x401000), mem});

  B.CreateRet(result);

  runPass(test_fn);

  // After: should have a direct call to sub_401000
  bool has_direct_call = false;
  bool has_remill_call = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction()) {
          if (CI->getCalledFunction()->getName() == "sub_401000")
            has_direct_call = true;
          if (CI->getCalledFunction()->getName() == "__remill_function_call")
            has_remill_call = true;
        }
      }
    }
  }
  EXPECT_TRUE(has_direct_call);
  EXPECT_FALSE(has_remill_call);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(LowerFunctionCallTest, DynamicPCDispatcher) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *lifted_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  // Declare __remill_function_call
  M->getOrInsertFunction("__remill_function_call", lifted_fn_ty);

  // Create the caller function
  auto *test_fn = llvm::Function::Create(
      lifted_fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *pc = test_fn->getArg(1);  // dynamic PC
  auto *mem = test_fn->getArg(2);

  // Call __remill_function_call with dynamic PC
  auto *call_fn = M->getFunction("__remill_function_call");
  auto *result = B.CreateCall(call_fn, {state, pc, mem});

  B.CreateRet(result);

  runPass(test_fn);

  // After: should have call to __omill_dispatch_call
  bool has_dispatch = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_dispatch_call")
          has_dispatch = true;
  EXPECT_TRUE(has_dispatch);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

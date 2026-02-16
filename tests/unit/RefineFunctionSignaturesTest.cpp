#include "omill/Passes/RefineFunctionSignatures.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class RefineFunctionSignaturesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");
    return M;
  }

  void runPass(llvm::Module &M) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::RefineFunctionSignaturesPass());
    MPM.run(M, MAM);
  }
};

TEST_F(RefineFunctionSignaturesTest, PointerParamRefined) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Create sub_401000_native(i64) -> i64
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000_native", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  // Use param as pointer: inttoptr → load.
  auto *ptr = B.CreateIntToPtr(fn->getArg(0), ptr_ty);
  auto *val = B.CreateLoad(i64_ty, ptr);
  B.CreateRet(val);

  EXPECT_FALSE(llvm::verifyFunction(*fn, &llvm::errs()));

  runPass(*M);

  // Function should now have ptr parameter.
  auto *refined = M->getFunction("sub_401000_native");
  ASSERT_NE(refined, nullptr);
  ASSERT_EQ(refined->arg_size(), 1u);
  EXPECT_TRUE(refined->getArg(0)->getType()->isPointerTy());
  EXPECT_FALSE(llvm::verifyFunction(*refined, &llvm::errs()));
}

TEST_F(RefineFunctionSignaturesTest, IntegerParamUnchanged) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000_native", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);
  // Simple arithmetic use — stays i64.
  auto *result = B.CreateAdd(fn->getArg(0), B.getInt64(1));
  B.CreateRet(result);

  runPass(*M);

  auto *refined = M->getFunction("sub_402000_native");
  ASSERT_NE(refined, nullptr);
  ASSERT_EQ(refined->arg_size(), 1u);
  EXPECT_TRUE(refined->getArg(0)->getType()->isIntegerTy(64));
}

TEST_F(RefineFunctionSignaturesTest, NonNativeFunctionSkipped) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // A function that's NOT named _native.
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);
  auto *ptr = B.CreateIntToPtr(fn->getArg(0), ptr_ty);
  auto *val = B.CreateLoad(i64_ty, ptr);
  B.CreateRet(val);

  runPass(*M);

  // Should NOT be modified.
  auto *same = M->getFunction("sub_401000");
  ASSERT_NE(same, nullptr);
  EXPECT_TRUE(same->getArg(0)->getType()->isIntegerTy(64));
}

TEST_F(RefineFunctionSignaturesTest, CallSitesUpdated) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Create callee: sub_402000_native(i64) -> i64
  auto *callee_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *callee = llvm::Function::Create(
      callee_ty, llvm::Function::ExternalLinkage, "sub_402000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", callee);
    llvm::IRBuilder<> B(entry);
    auto *ptr = B.CreateIntToPtr(callee->getArg(0), ptr_ty);
    auto *val = B.CreateLoad(i64_ty, ptr);
    B.CreateRet(val);
  }

  // Create caller that calls callee with an i64 argument.
  auto *caller_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *caller = llvm::Function::Create(
      caller_ty, llvm::Function::ExternalLinkage, "caller", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *result = B.CreateCall(callee, {caller->getArg(0)});
    B.CreateRet(result);
  }

  runPass(*M);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The callee should have a ptr parameter now.
  auto *refined = M->getFunction("sub_402000_native");
  ASSERT_NE(refined, nullptr);
  EXPECT_TRUE(refined->getArg(0)->getType()->isPointerTy());

  // The caller should have been updated to pass inttoptr conversion.
  bool found_call = false;
  for (auto &I : caller->getEntryBlock()) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (CI->getCalledFunction() == refined) {
        found_call = true;
        EXPECT_TRUE(CI->getArgOperand(0)->getType()->isPointerTy());
      }
    }
  }
  EXPECT_TRUE(found_call);
}

}  // namespace

#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerErrorAndMissingTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::ErrorMissing));

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

    FPM.run(*F, FAM);
  }

  std::unique_ptr<llvm::Module> createModuleWithIntrinsic(
      llvm::StringRef intrinsic_name) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

    // Declare the intrinsic: (State*, i64, Memory*) -> Memory*
    auto *intr_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    M->getOrInsertFunction(intrinsic_name, intr_ty);

    // Create lifted function
    auto *fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *pc = test_fn->getArg(1);
    auto *mem = test_fn->getArg(2);

    auto *intr_fn = M->getFunction(intrinsic_name);
    auto *result = B.CreateCall(intr_fn, {state, pc, mem});
    B.CreateRet(result);

    return M;
  }
};

TEST_F(LowerErrorAndMissingTest, ErrorBecomesHandlerAndRet) {
  auto M = createModuleWithIntrinsic("__remill_error");
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // After: should have call to __omill_error_handler + ret (not unreachable,
  // to prevent LLVM from deducing the function is noreturn and eliminating
  // live code in other branches).
  bool has_handler_call = false;
  bool has_ret = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_error_handler")
          has_handler_call = true;
      }
      if (llvm::isa<llvm::ReturnInst>(&I))
        has_ret = true;
    }
  }
  EXPECT_TRUE(has_handler_call);
  EXPECT_TRUE(has_ret);

  // No more remill error calls
  bool has_remill = false;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__remill_error")
          has_remill = true;
  EXPECT_FALSE(has_remill);
}

TEST_F(LowerErrorAndMissingTest, MissingBlockHandled) {
  auto M = createModuleWithIntrinsic("__remill_missing_block");
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // After: should have call to __omill_missing_block_handler + ret
  bool has_handler_call = false;
  bool has_ret = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() ==
                "__omill_missing_block_handler")
          has_handler_call = true;
      }
      if (llvm::isa<llvm::ReturnInst>(&I))
        has_ret = true;
    }
  }
  EXPECT_TRUE(has_handler_call);
  EXPECT_TRUE(has_ret);
}

}  // namespace

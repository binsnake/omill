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

class LowerFunctionReturnTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Declare __remill_function_return(State*, i64, Memory*) -> Memory*
    auto *ret_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    M->getOrInsertFunction("__remill_function_return", ret_ty);

    // Create lifted function
    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *pc = test_fn->getArg(1);
    auto *mem = test_fn->getArg(2);

    // Call __remill_function_return
    auto *ret_fn = M->getFunction("__remill_function_return");
    auto *result = B.CreateCall(ret_fn, {state, pc, mem});

    B.CreateRet(result);
    return M;
  }
};

TEST_F(LowerFunctionReturnTest, ReplacesIntrinsicWithNativeReturn) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Before: has a call to __remill_function_return.
  bool has_remill_return = false;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__remill_function_return")
          has_remill_return = true;
  EXPECT_TRUE(has_remill_return);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Return));

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

  // After: no more __remill_function_return calls.
  has_remill_return = false;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__remill_function_return")
          has_remill_return = true;
  EXPECT_FALSE(has_remill_return);

  // Should have a native return instruction.
  bool has_ret = false;
  for (auto &BB : *F)
    if (llvm::isa<llvm::ReturnInst>(BB.getTerminator()))
      has_ret = true;
  EXPECT_TRUE(has_ret);
}

}  // namespace

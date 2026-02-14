#include "omill/Passes/LowerFlagIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerFlagIntrinsicsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a flag computation intrinsic call.
  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);

    auto *i1_ty = llvm::Type::getInt1Ty(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Declare __remill_flag_computation_zero(bool, ...)
    auto *flag_fn_ty = llvm::FunctionType::get(i1_ty, {i1_ty}, true);
    auto flag_fn =
        M->getOrInsertFunction("__remill_flag_computation_zero", flag_fn_ty);

    // Create a test function
    auto *fn_ty = llvm::FunctionType::get(
        ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> Builder(entry);

    // Simulate: bool result = (some_val == 0);
    //           bool flag = __remill_flag_computation_zero(result, some_val)
    auto *some_val = Builder.getInt64(42);
    auto *cmp_result = Builder.CreateICmpEQ(some_val, Builder.getInt64(0));

    auto *flag_call = Builder.CreateCall(
        flag_fn, {cmp_result, some_val});

    // Use the flag in a branch
    auto *then_bb = llvm::BasicBlock::Create(Ctx, "then", test_fn);
    auto *else_bb = llvm::BasicBlock::Create(Ctx, "else", test_fn);
    Builder.CreateCondBr(flag_call, then_bb, else_bb);

    Builder.SetInsertPoint(then_bb);
    Builder.CreateRet(test_fn->getArg(2));

    Builder.SetInsertPoint(else_bb);
    Builder.CreateRet(test_fn->getArg(2));

    return M;
  }
};

TEST_F(LowerFlagIntrinsicsTest, RemovesFlagComputationCalls) {
  auto M = createTestModule();

  // Verify the intrinsic call exists before lowering.
  auto *test_fn = M->getFunction("test_func");
  ASSERT_NE(test_fn, nullptr);

  unsigned call_count = 0;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() ==
                "__remill_flag_computation_zero") {
          call_count++;
        }
      }
    }
  }
  EXPECT_EQ(call_count, 1u);

  // Run the pass.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::LowerFlagIntrinsicsPass());

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

  FPM.run(*test_fn, FAM);

  // Verify no more flag computation calls.
  call_count = 0;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with(
                "__remill_flag_computation")) {
          call_count++;
        }
      }
    }
  }
  EXPECT_EQ(call_count, 0u);

  // Verify the module is still valid.
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

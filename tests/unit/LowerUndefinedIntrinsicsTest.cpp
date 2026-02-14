#include "omill/Passes/LowerUndefinedIntrinsics.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerUndefinedIntrinsicsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerUndefinedIntrinsicsPass());

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
};

TEST_F(LowerUndefinedIntrinsicsTest, UndefinedReplacedWithFreezePoison) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Declare __remill_undefined_64() -> i64
  auto *undef_ty = llvm::FunctionType::get(i64_ty, {}, false);
  M->getOrInsertFunction("__remill_undefined_64", undef_ty);

  // Create lifted function
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  // val = __remill_undefined_64()
  auto *undef_fn = M->getFunction("__remill_undefined_64");
  auto *val = B.CreateCall(undef_fn, {});

  // Use the value in an add to keep it alive
  auto *result = B.CreateAdd(val, B.getInt64(1));
  (void)result;
  B.CreateRet(test_fn->getArg(2));

  // Before: should have a call to __remill_undefined_64
  bool has_undef_call = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__remill_undefined_64")
          has_undef_call = true;
  EXPECT_TRUE(has_undef_call);

  runPass(test_fn);

  // After: no more undefined calls
  has_undef_call = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with(
                "__remill_undefined"))
          has_undef_call = true;
  EXPECT_FALSE(has_undef_call);

  // Should have a freeze instruction (freeze of poison)
  bool has_freeze = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::FreezeInst>(&I))
        has_freeze = true;
  EXPECT_TRUE(has_freeze);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

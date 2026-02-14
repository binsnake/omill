#include "omill/Passes/MemoryPointerElimination.h"

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

class MemoryPointerEliminationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::MemoryPointerEliminationPass());

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

TEST_F(MemoryPointerEliminationTest, MemArgReplacedWithPoison) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *mem = test_fn->getArg(2);

  // Use Memory* in a return (simulating remaining use after lowering)
  B.CreateRet(mem);

  // Before: arg2 (Memory*) has uses
  EXPECT_FALSE(test_fn->getArg(2)->use_empty());

  runPass(test_fn);

  // After: arg2 should have no uses (replaced with poison)
  EXPECT_TRUE(test_fn->getArg(2)->use_empty());

  // The return should now return poison
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::PoisonValue>(ret->getReturnValue()));

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

#include "omill/Passes/FoldConstantVectorChains.h"

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

class FoldConstantVectorChainsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::FoldConstantVectorChainsPass());

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

    FPM.run(F, FAM);
  }
};

TEST_F(FoldConstantVectorChainsTest, ShuffleOfConstantsFolded) {
  // shufflevector(<4 x i32> <1,2,3,4>, <4 x i32> <5,6,7,8>, <4,0,5,1>)
  // → <4 x i32> <5,1,6,2>
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *c1 = llvm::ConstantVector::get({
      llvm::ConstantInt::get(i32_ty, 1),
      llvm::ConstantInt::get(i32_ty, 2),
      llvm::ConstantInt::get(i32_ty, 3),
      llvm::ConstantInt::get(i32_ty, 4),
  });
  auto *c2 = llvm::ConstantVector::get({
      llvm::ConstantInt::get(i32_ty, 5),
      llvm::ConstantInt::get(i32_ty, 6),
      llvm::ConstantInt::get(i32_ty, 7),
      llvm::ConstantInt::get(i32_ty, 8),
  });

  auto *shuffled = B.CreateShuffleVector(c1, c2, {4, 0, 5, 1}, "shuffled");
  B.CreateRet(shuffled);

  runPass(*test_fn);

  // After: the shufflevector should be folded to a constant.
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::Constant>(ret->getReturnValue()));

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(FoldConstantVectorChainsTest, InsertExtractChainFolded) {
  // insertelement(zeroinitializer, constant, 0) → constant vector.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  // Start from zeroinitializer, insert 42 at index 2.
  auto *zero_vec = llvm::ConstantAggregateZero::get(v4i32_ty);
  auto *inserted = B.CreateInsertElement(
      zero_vec, llvm::ConstantInt::get(i32_ty, 42), B.getInt64(2), "ins");

  B.CreateRet(inserted);

  runPass(*test_fn);

  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::Constant>(ret->getReturnValue()));

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(FoldConstantVectorChainsTest, NonConstantNotFolded) {
  // shufflevector with a non-constant input — should not be folded.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {v4i32_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *input = test_fn->getArg(0);  // non-constant
  auto *c = llvm::ConstantVector::get({
      llvm::ConstantInt::get(i32_ty, 1),
      llvm::ConstantInt::get(i32_ty, 2),
      llvm::ConstantInt::get(i32_ty, 3),
      llvm::ConstantInt::get(i32_ty, 4),
  });

  // Shuffle with non-constant first operand.
  auto *shuffled = B.CreateShuffleVector(input, c, {4, 0, 5, 1}, "shuffled");
  B.CreateRet(shuffled);

  runPass(*test_fn);

  // The shufflevector should remain (non-constant input).
  bool has_shuffle = false;
  for (auto &I : test_fn->getEntryBlock())
    if (llvm::isa<llvm::ShuffleVectorInst>(&I))
      has_shuffle = true;

  EXPECT_TRUE(has_shuffle);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(FoldConstantVectorChainsTest, CascadedShufflesFolded) {
  // Two cascaded shufflevectors, both from constants.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *c1 = llvm::ConstantVector::get({
      llvm::ConstantInt::get(i32_ty, 10),
      llvm::ConstantInt::get(i32_ty, 20),
      llvm::ConstantInt::get(i32_ty, 30),
      llvm::ConstantInt::get(i32_ty, 40),
  });
  auto *c2 = llvm::ConstantVector::get({
      llvm::ConstantInt::get(i32_ty, 50),
      llvm::ConstantInt::get(i32_ty, 60),
      llvm::ConstantInt::get(i32_ty, 70),
      llvm::ConstantInt::get(i32_ty, 80),
  });

  auto *inner = B.CreateShuffleVector(c1, c2, {0, 4, 1, 5}, "inner");
  auto *outer = B.CreateShuffleVector(inner, c1, {0, 1, 4, 5}, "outer");
  B.CreateRet(outer);

  runPass(*test_fn);

  // Both shufflevectors should be folded.
  bool has_shuffle = false;
  for (auto &I : test_fn->getEntryBlock())
    if (llvm::isa<llvm::ShuffleVectorInst>(&I))
      has_shuffle = true;

  EXPECT_FALSE(has_shuffle);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

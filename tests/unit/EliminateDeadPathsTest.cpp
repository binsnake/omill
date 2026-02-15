#include "omill/Passes/EliminateDeadPaths.h"

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

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

class EliminateDeadPathsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::EliminateDeadPathsPass());

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

  unsigned countBlocks(llvm::Function *F) {
    return std::distance(F->begin(), F->end());
  }

  bool hasBlock(llvm::Function *F, llvm::StringRef name) {
    for (auto &BB : *F)
      if (BB.getName() == name)
        return true;
    return false;
  }
};

TEST_F(EliminateDeadPathsTest, EliminatesOrNotTautology) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "true_bb", F);
  auto *dead_bb = llvm::BasicBlock::Create(Ctx, "dead_bb", F);

  // entry: x | ~x == -1 → always true
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *not_x = B.CreateNot(x, "not_x");
  auto *or_val = B.CreateOr(x, not_x, "or");
  auto *cmp = B.CreateICmpEQ(or_val, llvm::ConstantInt::get(i64_ty, -1));
  B.CreateCondBr(cmp, true_bb, dead_bb);

  B.SetInsertPoint(true_bb);
  B.CreateRetVoid();

  B.SetInsertPoint(dead_bb);
  B.CreateRetVoid();

  EXPECT_EQ(countBlocks(F), 3u);

  runPass(F);

  // dead_bb should be removed.
  EXPECT_FALSE(hasBlock(F, "dead_bb"));
  EXPECT_TRUE(hasBlock(F, "true_bb"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(EliminateDeadPathsTest, EliminatesEvenProduct) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *even_bb = llvm::BasicBlock::Create(Ctx, "even_bb", F);
  auto *odd_bb = llvm::BasicBlock::Create(Ctx, "odd_bb", F);

  // (x * (x + 1)) & 1 == 0 → always true
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *x_plus_1 = B.CreateAdd(x, llvm::ConstantInt::get(i64_ty, 1));
  auto *product = B.CreateMul(x, x_plus_1);
  auto *low_bit = B.CreateAnd(product, llvm::ConstantInt::get(i64_ty, 1));
  auto *cmp = B.CreateICmpEQ(low_bit, llvm::ConstantInt::get(i64_ty, 0));
  B.CreateCondBr(cmp, even_bb, odd_bb);

  B.SetInsertPoint(even_bb);
  B.CreateRetVoid();

  B.SetInsertPoint(odd_bb);
  B.CreateRetVoid();

  runPass(F);

  // odd_bb should be removed (product of consecutive ints is always even).
  EXPECT_FALSE(hasBlock(F, "odd_bb"));
  EXPECT_TRUE(hasBlock(F, "even_bb"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(EliminateDeadPathsTest, PreservesNonOpaqueCondition) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "true_bb", F);
  auto *false_bb = llvm::BasicBlock::Create(Ctx, "false_bb", F);

  // x > 5 with unknown x → should NOT be folded.
  llvm::IRBuilder<> B(entry);
  auto *cmp = B.CreateICmpUGT(F->getArg(0), llvm::ConstantInt::get(i64_ty, 5));
  B.CreateCondBr(cmp, true_bb, false_bb);

  B.SetInsertPoint(true_bb);
  B.CreateRetVoid();

  B.SetInsertPoint(false_bb);
  B.CreateRetVoid();

  EXPECT_EQ(countBlocks(F), 3u);

  runPass(F);

  // Both blocks should remain.
  EXPECT_EQ(countBlocks(F), 3u);
  EXPECT_TRUE(hasBlock(F, "true_bb"));
  EXPECT_TRUE(hasBlock(F, "false_bb"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(EliminateDeadPathsTest, KnownBitsRangeElimination) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "true_bb", F);
  auto *false_bb = llvm::BasicBlock::Create(Ctx, "false_bb", F);

  // (x & 0xFF) > 300 → always false (max value is 255)
  llvm::IRBuilder<> B(entry);
  auto *masked = B.CreateAnd(F->getArg(0), llvm::ConstantInt::get(i64_ty, 0xFF));
  auto *cmp = B.CreateICmpUGT(masked, llvm::ConstantInt::get(i64_ty, 300));
  B.CreateCondBr(cmp, true_bb, false_bb);

  B.SetInsertPoint(true_bb);
  B.CreateRetVoid();

  B.SetInsertPoint(false_bb);
  B.CreateRetVoid();

  runPass(F);

  // true_bb should be removed (condition always false).
  EXPECT_FALSE(hasBlock(F, "true_bb"));
  EXPECT_TRUE(hasBlock(F, "false_bb"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(EliminateDeadPathsTest, ChainedDeadBlocks) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *live_bb = llvm::BasicBlock::Create(Ctx, "live_bb", F);
  auto *dead1 = llvm::BasicBlock::Create(Ctx, "dead1", F);
  auto *dead2 = llvm::BasicBlock::Create(Ctx, "dead2", F);

  // (x & 0xFF) > 300 → always false, dead1 is unreachable.
  // dead1 branches to dead2, so both should be removed.
  llvm::IRBuilder<> B(entry);
  auto *masked = B.CreateAnd(F->getArg(0), llvm::ConstantInt::get(i64_ty, 0xFF));
  auto *cmp = B.CreateICmpUGT(masked, llvm::ConstantInt::get(i64_ty, 300));
  B.CreateCondBr(cmp, dead1, live_bb);

  B.SetInsertPoint(dead1);
  B.CreateBr(dead2);

  B.SetInsertPoint(dead2);
  B.CreateRetVoid();

  B.SetInsertPoint(live_bb);
  B.CreateRetVoid();

  EXPECT_EQ(countBlocks(F), 4u);

  runPass(F);

  // Both dead blocks removed.
  EXPECT_FALSE(hasBlock(F, "dead1"));
  EXPECT_FALSE(hasBlock(F, "dead2"));
  EXPECT_EQ(countBlocks(F), 2u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(EliminateDeadPathsTest, PHINodeUpdate) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *dead_path = llvm::BasicBlock::Create(Ctx, "dead_path", F);
  auto *live_path = llvm::BasicBlock::Create(Ctx, "live_path", F);
  auto *merge = llvm::BasicBlock::Create(Ctx, "merge", F);

  // Use x | ~x == -1: always true, so true-successor is live, false is dead.
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *not_x = B.CreateNot(x);
  auto *or_val = B.CreateOr(x, not_x);
  auto *cmp = B.CreateICmpEQ(or_val, llvm::ConstantInt::get(i64_ty, -1));
  B.CreateCondBr(cmp, live_path, dead_path);

  B.SetInsertPoint(dead_path);
  B.CreateBr(merge);

  B.SetInsertPoint(live_path);
  B.CreateBr(merge);

  B.SetInsertPoint(merge);
  auto *phi = B.CreatePHI(i64_ty, 2, "result");
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 42), dead_path);
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 99), live_path);
  B.CreateRet(phi);

  runPass(F);

  // dead_path should be removed.
  EXPECT_FALSE(hasBlock(F, "dead_path"));
  EXPECT_TRUE(hasBlock(F, "live_path"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

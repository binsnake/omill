#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Include the implementation directly (same pattern as other obf tests).
#include "../../tools/ollvm-obf/IfConversion.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class IfConversionObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_ifconv", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function with a diamond-shaped CFG:
  ///   entry: br i1 %cond, %bb_true, %bb_false
  ///   bb_true:  %t = add %a, 1 ; br %merge
  ///   bb_false: %f = add %a, 2 ; br %merge
  ///   merge:    %phi = phi [%t, %bb_true], [%f, %bb_false] ; ret %phi
  llvm::Function *createDiamond(llvm::Module &M, const std::string &name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *i1 = llvm::Type::getInt1Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32, {i1, i32}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);

    auto *Entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *TrueBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *FalseBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *MergeBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> B(Entry);
    B.CreateCondBr(F->getArg(0), TrueBB, FalseBB);

    B.SetInsertPoint(TrueBB);
    auto *TrueVal = B.CreateAdd(F->getArg(1),
                                llvm::ConstantInt::get(i32, 1), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(FalseBB);
    auto *FalseVal = B.CreateAdd(F->getArg(1),
                                 llvm::ConstantInt::get(i32, 2), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(MergeBB);
    auto *Phi = B.CreatePHI(i32, 2, "");
    Phi->addIncoming(TrueVal, TrueBB);
    Phi->addIncoming(FalseVal, FalseBB);
    B.CreateRet(Phi);

    return F;
  }

  /// Diamond where one arm has a store (side effect).
  llvm::Function *createDiamondWithStore(llvm::Module &M,
                                         const std::string &name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *i1 = llvm::Type::getInt1Ty(Ctx);
    auto *ptr = llvm::PointerType::get(Ctx, 0);
    auto *fnTy = llvm::FunctionType::get(i32, {i1, i32, ptr}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);

    auto *Entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *TrueBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *FalseBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *MergeBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> B(Entry);
    B.CreateCondBr(F->getArg(0), TrueBB, FalseBB);

    B.SetInsertPoint(TrueBB);
    auto *TrueVal = B.CreateAdd(F->getArg(1),
                                llvm::ConstantInt::get(i32, 1), "");
    B.CreateStore(TrueVal, F->getArg(2));  // side effect!
    B.CreateBr(MergeBB);

    B.SetInsertPoint(FalseBB);
    auto *FalseVal = B.CreateAdd(F->getArg(1),
                                 llvm::ConstantInt::get(i32, 2), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(MergeBB);
    auto *Phi = B.CreatePHI(i32, 2, "");
    Phi->addIncoming(TrueVal, TrueBB);
    Phi->addIncoming(FalseVal, FalseBB);
    B.CreateRet(Phi);

    return F;
  }

  /// Diamond where one arm has a udiv (could trap on division by zero).
  llvm::Function *createDiamondWithDiv(llvm::Module &M,
                                       const std::string &name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *i1 = llvm::Type::getInt1Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32, {i1, i32, i32}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);

    auto *Entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *TrueBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *FalseBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *MergeBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> B(Entry);
    B.CreateCondBr(F->getArg(0), TrueBB, FalseBB);

    B.SetInsertPoint(TrueBB);
    auto *TrueVal = B.CreateUDiv(F->getArg(1), F->getArg(2), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(FalseBB);
    auto *FalseVal = B.CreateAdd(F->getArg(1),
                                 llvm::ConstantInt::get(i32, 2), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(MergeBB);
    auto *Phi = B.CreatePHI(i32, 2, "");
    Phi->addIncoming(TrueVal, TrueBB);
    Phi->addIncoming(FalseVal, FalseBB);
    B.CreateRet(Phi);

    return F;
  }

  /// Diamond with two PHI nodes in the merge block.
  llvm::Function *createDiamondMultiPHI(llvm::Module &M,
                                        const std::string &name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *i1 = llvm::Type::getInt1Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32, {i1, i32}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);

    auto *Entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *TrueBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *FalseBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *MergeBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> B(Entry);
    B.CreateCondBr(F->getArg(0), TrueBB, FalseBB);

    B.SetInsertPoint(TrueBB);
    auto *T1 = B.CreateAdd(F->getArg(1), llvm::ConstantInt::get(i32, 1), "");
    auto *T2 = B.CreateSub(F->getArg(1), llvm::ConstantInt::get(i32, 1), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(FalseBB);
    auto *F1 = B.CreateAdd(F->getArg(1), llvm::ConstantInt::get(i32, 2), "");
    auto *F2 = B.CreateSub(F->getArg(1), llvm::ConstantInt::get(i32, 2), "");
    B.CreateBr(MergeBB);

    B.SetInsertPoint(MergeBB);
    auto *Phi1 = B.CreatePHI(i32, 2, "");
    Phi1->addIncoming(T1, TrueBB);
    Phi1->addIncoming(F1, FalseBB);
    auto *Phi2 = B.CreatePHI(i32, 2, "");
    Phi2->addIncoming(T2, TrueBB);
    Phi2->addIncoming(F2, FalseBB);
    auto *Sum = B.CreateAdd(Phi1, Phi2, "");
    B.CreateRet(Sum);

    return F;
  }

  /// Non-diamond: true/false branches go to different merge blocks.
  llvm::Function *createNonDiamond(llvm::Module &M, const std::string &name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *i1 = llvm::Type::getInt1Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32, {i1, i32}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);

    auto *Entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *TrueBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *FalseBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> B(Entry);
    B.CreateCondBr(F->getArg(0), TrueBB, FalseBB);

    B.SetInsertPoint(TrueBB);
    auto *TrueVal = B.CreateAdd(F->getArg(1),
                                llvm::ConstantInt::get(i32, 1), "");
    B.CreateRet(TrueVal);

    B.SetInsertPoint(FalseBB);
    auto *FalseVal = B.CreateAdd(F->getArg(1),
                                 llvm::ConstantInt::get(i32, 2), "");
    B.CreateRet(FalseVal);

    return F;
  }

  ollvm::FilterConfig fullCfg() {
    return {0, false, 100};
  }

  unsigned countOpcode(llvm::Function &F, unsigned opcode) {
    unsigned n = 0;
    for (auto &BB : F)
      for (auto &I : BB)
        if (I.getOpcode() == opcode) ++n;
    return n;
  }

  unsigned countBlocks(llvm::Function &F) {
    unsigned n = 0;
    for (auto &BB : F)
      (void)BB, ++n;
    return n;
  }
};

// ─── BasicDiamond: simple diamond converted to select ───────────────────

TEST_F(IfConversionObfTest, BasicDiamond) {
  auto M = createModule();
  auto *F = createDiamond(*M, "basic_diamond");
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Before: 4 blocks, has PHI, no select.
  EXPECT_EQ(countBlocks(*F), 4u);
  EXPECT_GT(countOpcode(*F, llvm::Instruction::PHI), 0u);
  EXPECT_EQ(countOpcode(*F, llvm::Instruction::Select), 0u);

  ollvm::ifConvertModule(*M, 42, fullCfg());

  // After: 2 blocks (entry + merge), no PHI, has select.
  EXPECT_EQ(countBlocks(*F), 2u);
  EXPECT_EQ(countOpcode(*F, llvm::Instruction::PHI), 0u);
  EXPECT_GT(countOpcode(*F, llvm::Instruction::Select), 0u);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── NonDiamondSkipped: non-matching successors left alone ──────────────

TEST_F(IfConversionObfTest, NonDiamondSkipped) {
  auto M = createModule();
  auto *F = createNonDiamond(*M, "non_diamond");
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned blocksBefore = countBlocks(*F);
  ollvm::ifConvertModule(*M, 42, fullCfg());

  // Structure unchanged.
  EXPECT_EQ(countBlocks(*F), blocksBefore);
  EXPECT_EQ(countOpcode(*F, llvm::Instruction::Select), 0u);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── SideEffectsSkipped: diamond with store left alone ──────────────────

TEST_F(IfConversionObfTest, SideEffectsSkipped) {
  auto M = createModule();
  auto *F = createDiamondWithStore(*M, "side_effects");
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned blocksBefore = countBlocks(*F);
  ollvm::ifConvertModule(*M, 42, fullCfg());

  EXPECT_EQ(countBlocks(*F), blocksBefore);
  EXPECT_EQ(countOpcode(*F, llvm::Instruction::Select), 0u);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── DivisionSkipped: diamond with udiv left alone ──────────────────────

TEST_F(IfConversionObfTest, DivisionSkipped) {
  auto M = createModule();
  auto *F = createDiamondWithDiv(*M, "division");
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned blocksBefore = countBlocks(*F);
  ollvm::ifConvertModule(*M, 42, fullCfg());

  EXPECT_EQ(countBlocks(*F), blocksBefore);
  EXPECT_EQ(countOpcode(*F, llvm::Instruction::Select), 0u);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── MultiplePHIs: diamond with 2 PHI nodes → 2 selects ────────────────

TEST_F(IfConversionObfTest, MultiplePHIs) {
  auto M = createModule();
  auto *F = createDiamondMultiPHI(*M, "multi_phi");
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  EXPECT_EQ(countOpcode(*F, llvm::Instruction::PHI), 2u);

  ollvm::ifConvertModule(*M, 42, fullCfg());

  EXPECT_EQ(countOpcode(*F, llvm::Instruction::PHI), 0u);
  EXPECT_EQ(countOpcode(*F, llvm::Instruction::Select), 2u);
  EXPECT_EQ(countBlocks(*F), 2u);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── ModuleVerifies: verify module after transform across 10 seeds ──────

TEST_F(IfConversionObfTest, ModuleVerifies) {
  for (uint32_t seed = 0; seed < 10; ++seed) {
    auto M = createModule();
    createDiamond(*M, "d1");
    createDiamondMultiPHI(*M, "d2");
    createNonDiamond(*M, "nd");
    createDiamondWithStore(*M, "se");
    createDiamondWithDiv(*M, "dv");
    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    ollvm::ifConvertModule(*M, seed, fullCfg());

    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Verification failed for seed " << seed;
  }
}

// ─── DeclarationSkipped: function declaration left alone ────────────────

TEST_F(IfConversionObfTest, DeclarationSkipped) {
  auto M = createModule();
  auto *i32 = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32, {i32}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "decl_only", *M);
  (void)F;

  // Should not crash or modify anything.
  ollvm::ifConvertModule(*M, 42, fullCfg());
  EXPECT_TRUE(F->isDeclaration());
}

}  // namespace

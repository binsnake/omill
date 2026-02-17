#include "omill/Passes/CollapsePartialXMMWrites.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class CollapsePartialXMMWritesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::CollapsePartialXMMWritesPass());

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

TEST_F(CollapsePartialXMMWritesTest, ExtractFromUpperHalfRedirected) {
  // When extractelement goes through a shufflevector blend, and the lane maps
  // to operand 1 (the old value), the extract should be redirected.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {v16i8_ty, v16i8_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *new_lo = test_fn->getArg(0);  // new lower half
  auto *old = test_fn->getArg(1);     // old value

  // Blend mask: lower 8 from new_lo (0-7), upper 8 from old (16-23).
  llvm::SmallVector<int, 16> mask;
  for (int i = 0; i < 8; ++i) mask.push_back(i);         // new_lo[0..7]
  for (int i = 0; i < 8; ++i) mask.push_back(16 + i);    // old[0..7]

  auto *blended = B.CreateShuffleVector(new_lo, old, mask, "blended");

  // Extract from lane 10 — maps to old[2] via mask[10] = 18 → old[2].
  auto *extracted = B.CreateExtractElement(blended, B.getInt64(10), "byte");
  B.CreateRet(extracted);

  runPass(*test_fn);

  // After: the extract should be from 'old' at lane 2, not from 'blended'.
  bool found_direct_extract = false;
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&I)) {
      if (EE->getVectorOperand() == old) {
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand()))
          if (ci->getZExtValue() == 2)
            found_direct_extract = true;
      }
    }
  }
  EXPECT_TRUE(found_direct_extract);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CollapsePartialXMMWritesTest, ExtractFromLowerHalfRedirected) {
  // Extract from a lane that maps to operand 0 (the new value).
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {v16i8_ty, v16i8_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *new_lo = test_fn->getArg(0);
  auto *old = test_fn->getArg(1);

  // Blend: lower 8 from new_lo, upper 8 from old.
  llvm::SmallVector<int, 16> mask;
  for (int i = 0; i < 8; ++i) mask.push_back(i);
  for (int i = 0; i < 8; ++i) mask.push_back(16 + i);

  auto *blended = B.CreateShuffleVector(new_lo, old, mask, "blended");

  // Extract from lane 3 — maps to new_lo[3].
  auto *extracted = B.CreateExtractElement(blended, B.getInt64(3), "byte");
  B.CreateRet(extracted);

  runPass(*test_fn);

  // After: extract should be from new_lo at lane 3.
  bool found_direct_extract = false;
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&I)) {
      if (EE->getVectorOperand() == new_lo) {
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand()))
          if (ci->getZExtValue() == 3)
            found_direct_extract = true;
      }
    }
  }
  EXPECT_TRUE(found_direct_extract);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CollapsePartialXMMWritesTest, NonShuffleVectorNotTouched) {
  // Direct extractelement without shufflevector — left alone.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {v16i8_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *vec = test_fn->getArg(0);
  auto *extracted = B.CreateExtractElement(vec, B.getInt64(5), "byte");
  B.CreateRet(extracted);

  unsigned inst_count_before = 0;
  for (auto &I : test_fn->getEntryBlock()) inst_count_before++;

  runPass(*test_fn);

  unsigned inst_count_after = 0;
  for (auto &I : test_fn->getEntryBlock()) inst_count_after++;

  EXPECT_EQ(inst_count_before, inst_count_after);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

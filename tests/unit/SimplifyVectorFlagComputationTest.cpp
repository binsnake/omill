#include "omill/Passes/SimplifyVectorFlagComputation.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class SimplifyVectorFlagComputationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::SimplifyVectorFlagComputationPass());

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

TEST_F(SimplifyVectorFlagComputationTest, ScalarizesExtractFromSext) {
  // extractelement(sext <16 x i1> to <16 x i8>, 5)
  //   → sext(extractelement(<16 x i1>, 5)) to i8
  // The pass scalarizes the vector sext into a scalar sext from i1.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i1_v16_ty = llvm::FixedVectorType::get(llvm::Type::getInt1Ty(Ctx), 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {i1_v16_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *cmp_result = test_fn->getArg(0);  // <16 x i1>

  // sext <16 x i1> to <16 x i8>
  auto *i8_v16_ty = llvm::FixedVectorType::get(i8_ty, 16);
  auto *sext = B.CreateSExt(cmp_result, i8_v16_ty, "sext");

  // extractelement at index 5
  auto *extract = B.CreateExtractElement(sext, B.getInt64(5), "byte");

  B.CreateRet(extract);

  runPass(*test_fn);

  // After: the vector extractelement(sext <16 x i8>) should be replaced with
  // a scalar sext(extractelement(<16 x i1>, 5)) to i8.
  // Check for: extractelement from <16 x i1> + scalar sext to i8.
  bool found_scalar_sext = false;
  bool found_i1_extract = false;
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *SE = llvm::dyn_cast<llvm::SExtInst>(&I)) {
      if (SE->getOperand(0)->getType()->isIntegerTy(1) &&
          SE->getType()->isIntegerTy(8))
        found_scalar_sext = true;
    }
    if (auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&I)) {
      if (auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(
              EE->getVectorOperand()->getType())) {
        if (VTy->getElementType()->isIntegerTy(1))
          found_i1_extract = true;
      }
    }
  }
  EXPECT_TRUE(found_i1_extract);
  EXPECT_TRUE(found_scalar_sext);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(SimplifyVectorFlagComputationTest, AndMaskWithBitcastFolded) {
  // Test the and-mask pattern with bitcast (the real-world pattern):
  // and(extractelement(bitcast(sext <4 x i1> to <4 x i32>) to <2 x i64>), mask)
  // This uses a different element size through bitcast, exercising the global_bit
  // lane computation.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1_v4_ty = llvm::FixedVectorType::get(llvm::Type::getInt1Ty(Ctx), 4);
  auto *i32_v4_ty = llvm::FixedVectorType::get(llvm::Type::getInt32Ty(Ctx), 4);
  auto *i64_v2_ty = llvm::FixedVectorType::get(i64_ty, 2);

  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i1_v4_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *cmp_result = test_fn->getArg(0);  // <4 x i1>

  // sext <4 x i1> to <4 x i32>
  auto *sext = B.CreateSExt(cmp_result, i32_v4_ty, "sext");

  // bitcast <4 x i32> to <2 x i64>
  auto *bc = B.CreateBitCast(sext, i64_v2_ty, "bc");

  // extractelement at index 0 → i64
  auto *extract = B.CreateExtractElement(bc, B.getInt64(0), "elem");

  // and i64 %elem, 1 → extracts bit 0 (lane 0 of the original <4 x i1>)
  auto *masked = B.CreateAnd(extract, llvm::ConstantInt::get(i64_ty, 1), "bit");

  B.CreateRet(masked);

  runPass(*test_fn);

  // After: the and+extract should be replaced with
  //   zext(extractelement(<4 x i1>, 0)) to i64
  bool found_zext = false;
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *ZE = llvm::dyn_cast<llvm::ZExtInst>(&I)) {
      if (ZE->getOperand(0)->getType()->isIntegerTy(1) &&
          ZE->getType()->isIntegerTy(64))
        found_zext = true;
    }
  }
  EXPECT_TRUE(found_zext);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(SimplifyVectorFlagComputationTest, NonSextNotTouched) {
  // and(extractelement(<16 x i8>), 1) without sext origin — left alone.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i8_v16_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {i8_v16_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *vec = test_fn->getArg(0);  // <16 x i8>, not from sext

  auto *extract = B.CreateExtractElement(vec, B.getInt64(5), "byte");
  auto *masked = B.CreateAnd(extract, llvm::ConstantInt::get(i8_ty, 1), "bit");

  B.CreateRet(masked);

  // Count instructions before.
  unsigned inst_count_before = 0;
  for (auto &I : test_fn->getEntryBlock())
    inst_count_before++;

  runPass(*test_fn);

  // Count after — should be unchanged.
  unsigned inst_count_after = 0;
  for (auto &I : test_fn->getEntryBlock())
    inst_count_after++;

  EXPECT_EQ(inst_count_before, inst_count_after);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(SimplifyVectorFlagComputationTest, MultiLaneScalarized) {
  // Multiple extractelements from same sext → all scalarized.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i1_v16_ty = llvm::FixedVectorType::get(llvm::Type::getInt1Ty(Ctx), 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {i1_v16_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *cmp_result = test_fn->getArg(0);
  auto *i8_v16_ty = llvm::FixedVectorType::get(i8_ty, 16);
  auto *sext = B.CreateSExt(cmp_result, i8_v16_ty, "sext");

  // Extract lanes 0 and 7 directly (no and-mask).
  auto *e0 = B.CreateExtractElement(sext, B.getInt64(0), "byte0");
  auto *e7 = B.CreateExtractElement(sext, B.getInt64(7), "byte7");

  auto *combined = B.CreateOr(e0, e7, "combined");
  B.CreateRet(combined);

  runPass(*test_fn);

  // Should have 2 scalar sext instructions (from i1 to i8).
  unsigned scalar_sext_count = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (auto *SE = llvm::dyn_cast<llvm::SExtInst>(&I))
      if (SE->getOperand(0)->getType()->isIntegerTy(1))
        scalar_sext_count++;

  EXPECT_EQ(scalar_sext_count, 2u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

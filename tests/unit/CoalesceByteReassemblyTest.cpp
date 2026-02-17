#include "omill/Passes/CoalesceByteReassembly.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class CoalesceByteReassemblyTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::CoalesceByteReassemblyPass());

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

  /// Build a 2-piece reassembly: extract i32[0] and i32[1] from <4 x i32>,
  /// zext to i64, shift+OR → result i64.  This matches the exact pattern
  /// CoalesceByteReassembly looks for: `or disjoint` of zext+shl leaves.
  llvm::Function *buildTwoPieceReassembly(llvm::Module &M) {
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *v16i8_ty = llvm::FixedVectorType::get(llvm::Type::getInt8Ty(Ctx), 16);

    auto *fn_ty = llvm::FunctionType::get(i64_ty, {v16i8_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *src = test_fn->getArg(0);  // <16 x i8>

    // Bitcast to <4 x i32>
    auto *v4i32_ty = llvm::FixedVectorType::get(llvm::Type::getInt32Ty(Ctx), 4);
    auto *bc = B.CreateBitCast(src, v4i32_ty, "bc32");

    // Extract i32[0], zext to i64
    auto *lo32 = B.CreateExtractElement(bc, B.getInt64(0), "lo32");
    auto *lo64 = B.CreateZExt(lo32, i64_ty, "lo64");

    // Extract i32[1], zext to i64, shift left 32
    auto *hi32 = B.CreateExtractElement(bc, B.getInt64(1), "hi32");
    auto *hi64 = B.CreateZExt(hi32, i64_ty, "hi64");
    auto *hi_shifted = B.CreateShl(hi64, B.getInt64(32), "hi_shifted");

    // or disjoint
    auto *result = B.CreateOr(lo64, hi_shifted, "result");
    // Mark as disjoint.
    if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(result))
      BO->setIsDisjoint(true);

    B.CreateRet(result);
    return test_fn;
  }
};

TEST_F(CoalesceByteReassemblyTest, TwoPiecesToI64) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *test_fn = buildTwoPieceReassembly(*M);

  // Before: should have OR.
  bool has_or_before = false;
  for (auto &I : test_fn->getEntryBlock())
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I))
      if (BO->getOpcode() == llvm::Instruction::Or)
        has_or_before = true;
  ASSERT_TRUE(has_or_before);

  runPass(*test_fn);

  // After: the OR should be replaced with a single extractelement from
  // <2 x i64>.
  bool has_or_after = false;
  bool has_wide_extract = false;
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I))
      if (BO->getOpcode() == llvm::Instruction::Or)
        has_or_after = true;
    if (auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&I)) {
      if (auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(
              EE->getVectorOperand()->getType())) {
        if (VTy->getElementType()->isIntegerTy(64))
          has_wide_extract = true;
      }
    }
  }

  EXPECT_FALSE(has_or_after);
  EXPECT_TRUE(has_wide_extract);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CoalesceByteReassemblyTest, NonContiguousNotCoalesced) {
  // Extract i32[0] and i32[2] (skip i32[1]) — gap, can't coalesce.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(llvm::Type::getInt8Ty(Ctx), 16);

  auto *fn_ty = llvm::FunctionType::get(i64_ty, {v16i8_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *src = test_fn->getArg(0);
  auto *v4i32_ty = llvm::FixedVectorType::get(llvm::Type::getInt32Ty(Ctx), 4);
  auto *bc = B.CreateBitCast(src, v4i32_ty, "bc32");

  // i32[0] at byte 0
  auto *lo32 = B.CreateExtractElement(bc, B.getInt64(0), "lo32");
  auto *lo64 = B.CreateZExt(lo32, i64_ty, "lo64");

  // i32[2] at byte 8 → shifted to byte 4 position (shift 32)
  auto *hi32 = B.CreateExtractElement(bc, B.getInt64(2), "hi32");
  auto *hi64 = B.CreateZExt(hi32, i64_ty, "hi64");
  auto *hi_shifted = B.CreateShl(hi64, B.getInt64(32), "hi_shifted");

  auto *result = B.CreateOr(lo64, hi_shifted, "result");
  if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(result))
    BO->setIsDisjoint(true);

  B.CreateRet(result);

  // Count OR instructions before.
  unsigned or_count_before = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I))
      if (BO->getOpcode() == llvm::Instruction::Or)
        or_count_before++;

  runPass(*test_fn);

  // OR should remain — non-contiguous bytes can't be coalesced.
  unsigned or_count_after = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I))
      if (BO->getOpcode() == llvm::Instruction::Or)
        or_count_after++;

  EXPECT_EQ(or_count_before, or_count_after);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

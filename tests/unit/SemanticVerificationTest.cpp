#include "omill/Utils/TranslationValidator.h"

#include "omill/Passes/OptimizeState.h"
#include "omill/Passes/OutlineConstantStackData.h"
#include "omill/Passes/SimplifyVectorReassembly.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

#if OMILL_ENABLE_Z3

namespace {

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

class SemanticVerificationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  z3::context Z3Ctx;

  void setupAnalyses(llvm::PassBuilder &PB, llvm::LoopAnalysisManager &LAM,
                      llvm::FunctionAnalysisManager &FAM,
                      llvm::CGSCCAnalysisManager &CGAM,
                      llvm::ModuleAnalysisManager &MAM) {
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
  }

  template <typename PassT>
  void runPass(llvm::Function &F) {
    runPassImpl(F, PassT());
  }

  template <typename PassT>
  void runPassImpl(llvm::Function &F, PassT pass) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(std::move(pass));
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    setupAnalyses(PB, LAM, FAM, CGAM, MAM);
    FPM.run(F, FAM);
  }

  std::unique_ptr<llvm::Module> makeModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }
};

// ============================================================================
// CoalesceByteReassembly
// ============================================================================

TEST_F(SemanticVerificationTest, CoalesceByteReassembly_TwoPiece) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(llvm::Type::getInt8Ty(Ctx), 16);

  auto *fn_ty = llvm::FunctionType::get(i64_ty, {v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *src = F->getArg(0);
  auto *v4i32_ty = llvm::FixedVectorType::get(llvm::Type::getInt32Ty(Ctx), 4);
  auto *bc = B.CreateBitCast(src, v4i32_ty, "bc32");

  auto *lo32 = B.CreateExtractElement(bc, B.getInt64(0), "lo32");
  auto *lo64 = B.CreateZExt(lo32, i64_ty, "lo64");
  auto *hi32 = B.CreateExtractElement(bc, B.getInt64(1), "hi32");
  auto *hi64 = B.CreateZExt(hi32, i64_ty, "hi64");
  auto *hi_shifted = B.CreateShl(hi64, B.getInt64(32), "hi_shifted");
  auto *result = B.CreateOr(lo64, hi_shifted, "result");
  if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(result))
    BO->setIsDisjoint(true);
  B.CreateRet(result);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, CoalesceByteReassembly_FourByte) {
  auto M = makeModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i32_ty, {v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *src = F->getArg(0);

  // 4-byte reassembly from individual bytes.
  auto *b0 = B.CreateExtractElement(src, B.getInt64(0), "b0");
  auto *b1 = B.CreateExtractElement(src, B.getInt64(1), "b1");
  auto *b2 = B.CreateExtractElement(src, B.getInt64(2), "b2");
  auto *b3 = B.CreateExtractElement(src, B.getInt64(3), "b3");

  auto *z0 = B.CreateZExt(b0, i32_ty, "z0");
  auto *z1 = B.CreateZExt(b1, i32_ty, "z1");
  auto *z2 = B.CreateZExt(b2, i32_ty, "z2");
  auto *z3_ = B.CreateZExt(b3, i32_ty, "z3");

  auto *s1 = B.CreateShl(z1, B.getInt32(8), "s1");
  auto *s2 = B.CreateShl(z2, B.getInt32(16), "s2");
  auto *s3 = B.CreateShl(z3_, B.getInt32(24), "s3");

  auto *or1 = B.CreateOr(z0, s1, "or1");
  if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(or1))
    BO->setIsDisjoint(true);
  auto *or2 = B.CreateOr(or1, s2, "or2");
  if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(or2))
    BO->setIsDisjoint(true);
  auto *or3 = B.CreateOr(or2, s3, "or3");
  if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(or3))
    BO->setIsDisjoint(true);

  B.CreateRet(or3);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, CoalesceByteReassembly_Partial) {
  // Partial reassembly: only 2 of 4 bytes from different positions.
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i16_ty = llvm::Type::getInt16Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(llvm::Type::getInt8Ty(Ctx), 16);

  auto *fn_ty = llvm::FunctionType::get(i16_ty, {v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *src = F->getArg(0);
  auto *b0 = B.CreateExtractElement(src, B.getInt64(4), "b0");
  auto *b1 = B.CreateExtractElement(src, B.getInt64(5), "b1");
  auto *z0 = B.CreateZExt(b0, i16_ty, "z0");
  auto *z1 = B.CreateZExt(b1, i16_ty, "z1");
  auto *s1 = B.CreateShl(z1, B.getInt16(8), "s1");
  auto *or_val = B.CreateOr(z0, s1, "or");
  if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(or_val))
    BO->setIsDisjoint(true);
  B.CreateRet(or_val);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

// ============================================================================
// CollapsePartialXMMWrites
// ============================================================================

TEST_F(SemanticVerificationTest, CollapsePartialXMM_UpperHalf) {
  auto M = makeModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {v16i8_ty, v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *new_lo = F->getArg(0);
  auto *old = F->getArg(1);

  llvm::SmallVector<int, 16> mask;
  for (int i = 0; i < 8; ++i) mask.push_back(i);
  for (int i = 0; i < 8; ++i) mask.push_back(16 + i);

  auto *blended = B.CreateShuffleVector(new_lo, old, mask, "blended");
  auto *extracted = B.CreateExtractElement(blended, B.getInt64(10), "byte");
  B.CreateRet(extracted);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, CollapsePartialXMM_LowerHalf) {
  auto M = makeModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {v16i8_ty, v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *new_lo = F->getArg(0);
  auto *old = F->getArg(1);

  llvm::SmallVector<int, 16> mask;
  for (int i = 0; i < 8; ++i) mask.push_back(i);
  for (int i = 0; i < 8; ++i) mask.push_back(16 + i);

  auto *blended = B.CreateShuffleVector(new_lo, old, mask, "blended");
  auto *extracted = B.CreateExtractElement(blended, B.getInt64(3), "byte");
  B.CreateRet(extracted);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

// ============================================================================
// SimplifyVectorFlagComputation
// ============================================================================

TEST_F(SemanticVerificationTest, SimplifyVectorFlag_AndMask) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1_v4_ty = llvm::FixedVectorType::get(llvm::Type::getInt1Ty(Ctx), 4);
  auto *i32_v4_ty = llvm::FixedVectorType::get(llvm::Type::getInt32Ty(Ctx), 4);
  auto *i64_v2_ty = llvm::FixedVectorType::get(i64_ty, 2);

  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i1_v4_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *cmp = F->getArg(0);
  auto *sext = B.CreateSExt(cmp, i32_v4_ty, "sext");
  auto *bc = B.CreateBitCast(sext, i64_v2_ty, "bc");
  auto *elem = B.CreateExtractElement(bc, B.getInt64(0), "elem");
  auto *masked = B.CreateAnd(elem, llvm::ConstantInt::get(i64_ty, 1), "bit");
  B.CreateRet(masked);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, SimplifyVectorFlag_DirectExtract) {
  auto M = makeModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i1_v16_ty = llvm::FixedVectorType::get(llvm::Type::getInt1Ty(Ctx), 16);
  auto *i8_v16_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {i1_v16_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *cmp = F->getArg(0);
  auto *sext = B.CreateSExt(cmp, i8_v16_ty, "sext");
  auto *extract = B.CreateExtractElement(sext, B.getInt64(5), "byte");
  B.CreateRet(extract);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, SimplifyVectorFlag_Lshr) {
  // lshr(extractelement(bitcast(sext <8 x i1> to <8 x i16>) to <4 x i32>), shift)
  auto M = makeModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i1_v8_ty = llvm::FixedVectorType::get(llvm::Type::getInt1Ty(Ctx), 8);
  auto *i16_v8_ty = llvm::FixedVectorType::get(llvm::Type::getInt16Ty(Ctx), 8);
  auto *i32_v4_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(i32_ty, {i1_v8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *cmp = F->getArg(0);
  auto *sext = B.CreateSExt(cmp, i16_v8_ty, "sext");
  auto *bc = B.CreateBitCast(sext, i32_v4_ty, "bc");
  auto *elem = B.CreateExtractElement(bc, B.getInt64(1), "elem");
  // lshr by 16 to get the MSBs of the 3rd i16 element (lane 3)
  auto *shifted = B.CreateLShr(elem, B.getInt32(16), "shifted");
  B.CreateRet(shifted);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

// ============================================================================
// DeadStateRoundtripElimination
// ============================================================================

TEST_F(SemanticVerificationTest, DeadStateRoundtrip_Simple) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *callee = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "ptr1");
  B.CreateStore(B.getInt64(42), gep1);
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Roundtrip: load then store same offset.
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "ptr2");
  auto *reloaded = B.CreateLoad(i64_ty, gep2, "reloaded");
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "ptr3");
  B.CreateStore(reloaded, gep3);

  B.CreateRet(call);

  omill::TranslationValidator validator(Z3Ctx);
  validator.setCompareOffsets({16, 17, 18, 19, 20, 21, 22, 23});
  validator.snapshotBefore(*F);
  runPassImpl(*F, omill::OptimizeStatePass(omill::OptimizePhases::Roundtrip));

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, DeadStateRoundtrip_NonRoundtripPreserved) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *callee = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "ptr1");
  B.CreateStore(B.getInt64(42), gep1);
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Load, modify, store — not a roundtrip.
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "ptr2");
  auto *loaded = B.CreateLoad(i64_ty, gep2, "loaded");
  auto *modified = B.CreateAdd(loaded, B.getInt64(1), "modified");
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "ptr3");
  B.CreateStore(modified, gep3);

  B.CreateRet(call);

  omill::TranslationValidator validator(Z3Ctx);
  validator.setCompareOffsets({16, 17, 18, 19, 20, 21, 22, 23});
  validator.snapshotBefore(*F);
  runPassImpl(*F, omill::OptimizeStatePass(omill::OptimizePhases::Roundtrip));

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

// ============================================================================
// EliminateRedundantByteStores
// ============================================================================

TEST_F(SemanticVerificationTest, RedundantByteStore_Eliminated) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Wide store: i64 0 at offset 464.
  auto *gep_wide = B.CreateConstGEP1_64(B.getInt8Ty(), state, 464, "wide");
  B.CreateStore(B.getInt64(0), gep_wide);

  // Narrow store: i8 0 at offset 465 — redundant.
  auto *gep_narrow = B.CreateConstGEP1_64(B.getInt8Ty(), state, 465, "narrow");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, 0), gep_narrow);

  B.CreateRet(mem);

  omill::TranslationValidator validator(Z3Ctx);
  validator.setCompareOffsets(
      {464, 465, 466, 467, 468, 469, 470, 471});
  validator.snapshotBefore(*F);
  runPassImpl(*F, omill::OptimizeStatePass(omill::OptimizePhases::RedundantBytes));

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, RedundantByteStore_DifferentValuePreserved) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Wide store: i64 0 at offset 464.
  auto *gep_wide = B.CreateConstGEP1_64(B.getInt8Ty(), state, 464, "wide");
  B.CreateStore(B.getInt64(0), gep_wide);

  // Narrow store: i8 0xFF at offset 465 — different value, NOT redundant.
  auto *gep_narrow = B.CreateConstGEP1_64(B.getInt8Ty(), state, 465, "narrow");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, 0xFF), gep_narrow);

  B.CreateRet(mem);

  omill::TranslationValidator validator(Z3Ctx);
  validator.setCompareOffsets(
      {464, 465, 466, 467, 468, 469, 470, 471});
  validator.snapshotBefore(*F);
  runPassImpl(*F, omill::OptimizeStatePass(omill::OptimizePhases::RedundantBytes));

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

// ============================================================================
// FoldConstantVectorChains
// ============================================================================

TEST_F(SemanticVerificationTest, FoldConstantVector_Shuffle) {
  auto M = makeModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
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

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, FoldConstantVector_InsertChain) {
  auto M = makeModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *zero = llvm::ConstantAggregateZero::get(v4i32_ty);
  auto *ins1 = B.CreateInsertElement(
      zero, llvm::ConstantInt::get(i32_ty, 42), B.getInt64(0), "ins1");
  auto *ins2 = B.CreateInsertElement(
      ins1, llvm::ConstantInt::get(i32_ty, 99), B.getInt64(2), "ins2");
  B.CreateRet(ins2);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);
  runPass<omill::SimplifyVectorReassemblyPass>(*F);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

// ============================================================================
// OutlineConstantStackData
// ============================================================================

TEST_F(SemanticVerificationTest, OutlineConstantStack_SimpleAlloca) {
  auto M = makeModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);

  auto *fn_ty = llvm::FunctionType::get(i64_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 8));
  B.CreateStore(B.getInt32(0x41424344), alloca);
  auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 4);
  B.CreateStore(B.getInt32(0x45464748), gep);
  auto *val = B.CreateLoad(i64_ty, alloca);
  B.CreateRet(val);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);

  // OutlineConstantStackData takes Function* in its runPass.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::OutlineConstantStackDataPass());
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    setupAnalyses(PB, LAM, FAM, CGAM, MAM);
    FPM.run(*F, FAM);
  }

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

TEST_F(SemanticVerificationTest, OutlineConstantStack_NonConstPreserved) {
  auto M = makeModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);

  auto *fn_ty = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(i32_ty);
  B.CreateStore(F->getArg(0), alloca);  // non-constant
  auto *val = B.CreateLoad(i32_ty, alloca);
  B.CreateRet(val);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*F);

  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::OutlineConstantStackDataPass());
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    setupAnalyses(PB, LAM, FAM, CGAM, MAM);
    FPM.run(*F, FAM);
  }

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  auto res = validator.verify(*F);
  EXPECT_TRUE(res.equivalent) << "Counterexample: " << res.counterexample;
}

}  // namespace

#endif  // OMILL_ENABLE_Z3

#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <random>

// Header-only — just include directly.
#include "../../tools/ollvm-obf/PassFilter.h"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class PassFilterObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_passfilter", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a minimal function with N add instructions plus a ret.
  llvm::Function *createFunctionWithNInstructions(llvm::Module &M,
                                                  const std::string &name,
                                                  unsigned numInstructions) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    llvm::Value *val = F->getArg(0);
    // Each add is one instruction; the ret at the end is another.
    // So we emit (numInstructions - 1) adds + 1 ret = numInstructions total.
    for (unsigned i = 0; i + 1 < numInstructions; ++i)
      val = B.CreateAdd(val, llvm::ConstantInt::get(i32Ty, 1), "a");
    B.CreateRet(val);
    return F;
  }

  /// Create a function that contains an inline asm call.
  llvm::Function *createFunctionWithInlineAsm(llvm::Module &M,
                                              const std::string &name) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);

    auto *asmFnTy = llvm::FunctionType::get(voidTy, false);
    auto *inlineAsm =
        llvm::InlineAsm::get(asmFnTy, "nop", "", /*hasSideEffects=*/true);
    B.CreateCall(asmFnTy, inlineAsm);

    B.CreateRet(F->getArg(0));
    return F;
  }
};

// ---------------------------------------------------------------------------
// shouldSkipFunction tests
// ---------------------------------------------------------------------------

TEST_F(PassFilterObfTest, SkipsDeclaration) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "decl", *M);
  // No body — it's a declaration.
  (void)F;
  ollvm::FilterConfig cfg;
  EXPECT_TRUE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, SkipsNaked) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "naked_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateUnreachable();
  F->addFnAttr(llvm::Attribute::Naked);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  EXPECT_TRUE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, SkipsAvailableExternally) {
  auto M = createModule();
  auto *F = createFunctionWithNInstructions(*M, "avail_ext", 3);
  F->setLinkage(llvm::GlobalValue::AvailableExternallyLinkage);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  EXPECT_TRUE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, SkipsOllvmExclude) {
  auto M = createModule();
  auto *F = createFunctionWithNInstructions(*M, "excluded_fn", 5);
  F->addFnAttr("ollvm_exclude");
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  EXPECT_TRUE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, SkipsSmallFunction) {
  auto M = createModule();
  // 3 instructions: 2 adds + 1 ret.
  auto *F = createFunctionWithNInstructions(*M, "small_fn", 3);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  cfg.min_instructions = 10;
  EXPECT_TRUE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, PassesLargeFunction) {
  auto M = createModule();
  // 20 instructions: 19 adds + 1 ret.
  auto *F = createFunctionWithNInstructions(*M, "large_fn", 20);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  cfg.min_instructions = 10;
  EXPECT_FALSE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, SkipsInlineAsm) {
  auto M = createModule();
  auto *F = createFunctionWithInlineAsm(*M, "asm_fn");
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  cfg.skip_inline_asm = true;
  EXPECT_TRUE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, PassesInlineAsmWhenNotChecked) {
  auto M = createModule();
  auto *F = createFunctionWithInlineAsm(*M, "asm_fn2");
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  cfg.skip_inline_asm = false;
  EXPECT_FALSE(ollvm::shouldSkipFunction(*F, cfg));
}

TEST_F(PassFilterObfTest, PassesNormalFunction) {
  auto M = createModule();
  auto *F = createFunctionWithNInstructions(*M, "normal_fn", 5);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  ollvm::FilterConfig cfg;
  EXPECT_FALSE(ollvm::shouldSkipFunction(*F, cfg));
}

// ---------------------------------------------------------------------------
// shouldTransform tests
// ---------------------------------------------------------------------------

TEST_F(PassFilterObfTest, AlwaysTransformAt100) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  std::mt19937 rng(42);
  for (int i = 0; i < 100; ++i)
    EXPECT_TRUE(ollvm::shouldTransform(rng, cfg));
}

TEST_F(PassFilterObfTest, NeverTransformAt0) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 0;
  std::mt19937 rng(42);
  for (int i = 0; i < 100; ++i)
    EXPECT_FALSE(ollvm::shouldTransform(rng, cfg));
}

TEST_F(PassFilterObfTest, PartialTransform) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 50;
  std::mt19937 rng(123);
  unsigned trueCount = 0;
  constexpr unsigned N = 1000;
  for (unsigned i = 0; i < N; ++i)
    trueCount += ollvm::shouldTransform(rng, cfg) ? 1 : 0;
  // With 50%, expect roughly 500.  Allow a wide margin.
  EXPECT_GT(trueCount, 300u);
  EXPECT_LT(trueCount, 700u);
}

TEST_F(PassFilterObfTest, DeterministicWithSameSeed) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 50;
  constexpr unsigned N = 100;

  std::mt19937 rng1(999);
  std::vector<bool> seq1;
  seq1.reserve(N);
  for (unsigned i = 0; i < N; ++i)
    seq1.push_back(ollvm::shouldTransform(rng1, cfg));

  std::mt19937 rng2(999);
  std::vector<bool> seq2;
  seq2.reserve(N);
  for (unsigned i = 0; i < N; ++i)
    seq2.push_back(ollvm::shouldTransform(rng2, cfg));

  EXPECT_EQ(seq1, seq2);
}

}  // namespace

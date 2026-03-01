#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/TargetParser/Triple.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Include the implementation directly (same pattern as other obf tests).
#include "../../tools/ollvm-obf/BMIMutation.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

static const char *kBMIFeatures =
    "+bmi,+bmi2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3";

class BMIMutationObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_bmi", Ctx);
    M->setDataLayout(kDataLayout);
    M->setTargetTriple(llvm::Triple("x86_64-pc-windows-msvc"));
    return M;
  }

  /// Create a function with a single binary op: %r = OP i32 %a, %b; ret %r.
  /// Annotated with BMI1+BMI2 target features.
  llvm::Function *createBinOp(llvm::Module &M, const std::string &name,
                               llvm::Instruction::BinaryOps op) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32, {i32, i32}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    F->addFnAttr("target-features", kBMIFeatures);

    auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(BB);
    auto *r = B.CreateBinOp(op, F->getArg(0), F->getArg(1));
    B.CreateRet(r);
    return F;
  }

  /// Create: %r = and i32 %a, <constMask>; ret %r.
  llvm::Function *createAndConst(llvm::Module &M, const std::string &name,
                                  uint32_t mask) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32, {i32}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    F->addFnAttr("target-features", kBMIFeatures);

    auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(BB);
    auto *r = B.CreateAnd(F->getArg(0), llvm::ConstantInt::get(i32, mask));
    B.CreateRet(r);
    return F;
  }

  /// Create a function with a load → add → store chain (for identity testing).
  llvm::Function *createLoadAddStore(llvm::Module &M, const std::string &name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *i32Ptr = llvm::PointerType::get(Ctx, 0);
    auto *fnTy = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx),
                                         {i32Ptr}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    F->addFnAttr("target-features", kBMIFeatures);

    auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(BB);
    auto *val = B.CreateLoad(i32, F->getArg(0));
    auto *inc = B.CreateAdd(val, llvm::ConstantInt::get(i32, 1));
    B.CreateStore(inc, F->getArg(0));
    B.CreateRetVoid();
    return F;
  }

  ollvm::FilterConfig fullCfg() {
    return {0, false, 100};  // No filtering, 100% transform.
  }

  bool hasIntrinsicCall(llvm::Function &F, llvm::Intrinsic::ID id) {
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *Callee = CI->getCalledFunction())
            if (Callee->getIntrinsicID() == id)
              return true;
    return false;
  }

  unsigned countOpcode(llvm::Function &F, unsigned opcode) {
    unsigned n = 0;
    for (auto &BB : F)
      for (auto &I : BB)
        if (I.getOpcode() == opcode) ++n;
    return n;
  }

  bool hasOpcode(llvm::Function &F, unsigned opcode) {
    return countOpcode(F, opcode) > 0;
  }
};

// ─── XOR → ANDN pair ─────────────────────────────────────────────────

TEST_F(BMIMutationObfTest, XorToAndnPair) {
  auto M = createModule();
  auto *F = createBinOp(*M, "test_xor", llvm::Instruction::Xor);

  ASSERT_TRUE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));

  // XOR→ANDN introduces XOR-with-minus-one (NOT) + AND (ANDN pattern).
  // The original 2-operand XOR is gone; new XORs are all NOT patterns.
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::Or));
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::And));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── OR → De Morgan + ANDN ───────────────────────────────────────────

TEST_F(BMIMutationObfTest, OrToAndnDeMorgan) {
  auto M = createModule();
  auto *F = createBinOp(*M, "test_or", llvm::Instruction::Or);

  ASSERT_TRUE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));

  EXPECT_FALSE(hasOpcode(*F, llvm::Instruction::Or));
  // De Morgan: NOT + AND + NOT  →  XOR(-1) + AND + XOR(-1)
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::And));
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::Xor));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── AND → nested ANDN ───────────────────────────────────────────────

TEST_F(BMIMutationObfTest, AndToNestedAndn) {
  auto M = createModule();
  auto *F = createBinOp(*M, "test_and", llvm::Instruction::And);

  ASSERT_TRUE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));

  // The AND is replaced with nested ANDN (xor + and + xor + and).
  EXPECT_GE(countOpcode(*F, llvm::Instruction::And), 2u);
  EXPECT_GE(countOpcode(*F, llvm::Instruction::Xor), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── AND constant contiguous from bit 0 → BZHI ──────────────────────

TEST_F(BMIMutationObfTest, AndConstToBzhi) {
  auto M = createModule();
  auto *F = createAndConst(*M, "test_bzhi", 0xFF);  // 8 contiguous bits

  ASSERT_TRUE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));

  EXPECT_TRUE(hasIntrinsicCall(*F, llvm::Intrinsic::x86_bmi_bzhi_32));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── AND constant contiguous at offset → BEXTR ──────────────────────

TEST_F(BMIMutationObfTest, AndConstToBextr) {
  auto M = createModule();
  // Mask 0xFF00 = bits 8-15 = start=8, len=8.
  auto *F = createAndConst(*M, "test_bextr", 0xFF00);

  ASSERT_TRUE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));

  EXPECT_TRUE(hasIntrinsicCall(*F, llvm::Intrinsic::x86_bmi_bextr_32));
  // BEXTR shifts result down, so we need SHL to shift back.
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::Shl));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── AND constant 0xFFFF → BZHI(16) ─────────────────────────────────

TEST_F(BMIMutationObfTest, AndConst16BitMask) {
  auto M = createModule();
  auto *F = createAndConst(*M, "test_bzhi16", 0xFFFF);

  ASSERT_TRUE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));

  EXPECT_TRUE(hasIntrinsicCall(*F, llvm::Intrinsic::x86_bmi_bzhi_32));
  // No SHL needed — mask starts at bit 0.
  EXPECT_FALSE(hasOpcode(*F, llvm::Instruction::Shl));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ─── Identity: BLSI | BLSR ───────────────────────────────────────────

TEST_F(BMIMutationObfTest, IdentityBlsiBlsr) {
  // Try multiple seeds to find one that picks the BLSI|BLSR path (choice==0).
  bool found = false;
  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M = createModule();
    auto *F = createLoadAddStore(*M, "test_blsi_blsr");
    ollvm::bmiMutateFunction(*F, seed, fullCfg());
    if (hasOpcode(*F, llvm::Instruction::Sub) &&
        hasOpcode(*F, llvm::Instruction::And) &&
        hasOpcode(*F, llvm::Instruction::Or) &&
        !hasIntrinsicCall(*F, llvm::Intrinsic::x86_bmi_pdep_32)) {
      found = true;
      EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
      break;
    }
  }
  EXPECT_TRUE(found) << "No seed in [0,200) produced BLSI|BLSR identity";
}

// ─── Identity: PDEP/PEXT roundtrip ──────────────────────────────────

TEST_F(BMIMutationObfTest, IdentityPdepPext) {
  auto M = createModule();
  auto *F = createLoadAddStore(*M, "test_pdep_pext");

  // Force PDEP/PEXT path by trying multiple seeds until one picks choice==1.
  bool found_pdep = false;
  for (uint32_t seed = 0; seed < 100; ++seed) {
    auto M2 = createModule();
    auto *F2 = createLoadAddStore(*M2, "test_pdep_pext");
    ollvm::bmiMutateFunction(*F2, seed, fullCfg());
    if (hasIntrinsicCall(*F2, llvm::Intrinsic::x86_bmi_pdep_32)) {
      found_pdep = true;
      EXPECT_TRUE(hasIntrinsicCall(*F2, llvm::Intrinsic::x86_bmi_pext_32));
      EXPECT_FALSE(llvm::verifyFunction(*F2, &llvm::errs()));
      break;
    }
  }
  EXPECT_TRUE(found_pdep) << "No seed in [0,100) produced PDEP/PEXT identity";
}

// ─── No BMI features → no transformation ────────────────────────────

TEST_F(BMIMutationObfTest, NoBMIFeaturesSkips) {
  auto M = createModule();
  auto *i32 = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32, {i32, i32}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "no_bmi", *M);
  // No target-features attribute — no BMI.
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);
  B.CreateRet(B.CreateXor(F->getArg(0), F->getArg(1)));

  EXPECT_FALSE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));
}

// ─── Filter: shouldSkipFunction respected ────────────────────────────

TEST_F(BMIMutationObfTest, FilterMinInstructions) {
  auto M = createModule();
  auto *F = createBinOp(*M, "test_filtered", llvm::Instruction::Xor);

  // Require 1000 instructions — tiny function should be skipped.
  ollvm::FilterConfig cfg = {1000, false, 100};
  EXPECT_FALSE(ollvm::bmiMutateFunction(*F, 42, cfg));
}

// ─── XOR with -1 (NOT) is not transformed ────────────────────────────

TEST_F(BMIMutationObfTest, XorMinusOneUntouched) {
  auto M = createModule();
  auto *i32 = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32, {i32}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "test_not", *M);
  F->addFnAttr("target-features", kBMIFeatures);

  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);
  B.CreateRet(B.CreateXor(F->getArg(0),
                           llvm::ConstantInt::get(i32, -1)));

  // XOR with -1 is NOT — should not be transformed (it's an ANDN building block).
  // The function has no other candidates, so pass returns false.
  EXPECT_FALSE(ollvm::bmiMutateFunction(*F, 42, fullCfg()));
}

// ─── Module-level: multiple functions ────────────────────────────────

TEST_F(BMIMutationObfTest, ModuleLevelMultipleFunctions) {
  auto M = createModule();
  createBinOp(*M, "fn_xor", llvm::Instruction::Xor);
  createBinOp(*M, "fn_or", llvm::Instruction::Or);
  createAndConst(*M, "fn_and_mask", 0xFFF);

  ollvm::bmiMutateModule(*M, 42, fullCfg());

  // All functions should be transformed.
  auto *F1 = M->getFunction("fn_xor");
  auto *F2 = M->getFunction("fn_or");
  auto *F3 = M->getFunction("fn_and_mask");

  // XOR→ANDN adds NOT (XOR -1) so check for AND (ANDN pattern) instead.
  EXPECT_TRUE(hasOpcode(*F1, llvm::Instruction::And));
  EXPECT_TRUE(hasOpcode(*F1, llvm::Instruction::Or));
  // OR→De Morgan removes the original OR.
  EXPECT_FALSE(hasOpcode(*F2, llvm::Instruction::Or));
  EXPECT_TRUE(hasIntrinsicCall(*F3, llvm::Intrinsic::x86_bmi_bzhi_32));

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

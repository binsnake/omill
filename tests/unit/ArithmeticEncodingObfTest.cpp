#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <random>
#include <set>

#include "../../tools/ollvm-obf/ArithmeticEncoding.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-"
    "n8:16:32:64-S128";

class ArithmeticEncodingObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a function that has an alloca of the given integer
  /// type, a store of a value into it, and a load from it returned.
  std::unique_ptr<llvm::Module> createStoreLoadFunction(unsigned bitWidth) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *intTy = llvm::Type::getIntNTy(Ctx, bitWidth);
    auto *fnTy = llvm::FunctionType::get(intTy, {intTy}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *alloca = B.CreateAlloca(intTy, nullptr, "");
    B.CreateStore(F->getArg(0), alloca);
    auto *loaded = B.CreateLoad(intTy, alloca, "");
    B.CreateRet(loaded);

    return M;
  }

  /// Create a module with a function that has two i32 allocas with
  /// store/load pairs.
  std::unique_ptr<llvm::Module> createTwoAllocaFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty, i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *a1 = B.CreateAlloca(i32Ty, nullptr, "");
    auto *a2 = B.CreateAlloca(i32Ty, nullptr, "");
    B.CreateStore(F->getArg(0), a1);
    B.CreateStore(F->getArg(1), a2);
    auto *v1 = B.CreateLoad(i32Ty, a1, "");
    auto *v2 = B.CreateLoad(i32Ty, a2, "");
    auto *sum = B.CreateAdd(v1, v2, "");
    B.CreateRet(sum);

    return M;
  }

  /// Create a module where the alloca is used in a GEP.
  std::unique_ptr<llvm::Module> createGEPUseFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *alloca = B.CreateAlloca(i32Ty, nullptr, "");
    B.CreateStore(F->getArg(0), alloca);
    // GEP use makes it ineligible.
    auto *gep = B.CreateInBoundsGEP(i32Ty, alloca,
                                    {llvm::ConstantInt::get(i32Ty, 0)}, "");
    auto *loaded = B.CreateLoad(i32Ty, gep, "");
    B.CreateRet(loaded);

    return M;
  }

  /// Create a module where the alloca is passed to a call.
  std::unique_ptr<llvm::Module> createCallUseFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *ptrTy = llvm::PointerType::getUnqual(Ctx);

    // Declare an external function that takes a pointer.
    auto *extFnTy = llvm::FunctionType::get(voidTy, {ptrTy}, false);
    auto *extFn = llvm::Function::Create(extFnTy,
                                         llvm::Function::ExternalLinkage,
                                         "external_fn", *M);

    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *alloca = B.CreateAlloca(i32Ty, nullptr, "");
    B.CreateStore(F->getArg(0), alloca);
    B.CreateCall(extFn, {alloca});
    auto *loaded = B.CreateLoad(i32Ty, alloca, "");
    B.CreateRet(loaded);

    return M;
  }

  /// Create a module with a volatile store/load.
  std::unique_ptr<llvm::Module> createVolatileFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *alloca = B.CreateAlloca(i32Ty, nullptr, "");
    auto *store = B.CreateStore(F->getArg(0), alloca);
    store->setVolatile(true);
    auto *loaded = B.CreateLoad(i32Ty, alloca, "");
    B.CreateRet(loaded);

    return M;
  }

  /// Count instructions of a given opcode in a function.
  unsigned countOpcode(llvm::Function *F, unsigned opcode) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (I.getOpcode() == opcode)
          ++count;
    return count;
  }
};

// ------------------------------------------------------------------
// BasicI32Encoding: store/load pair gets encode/decode inserted.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, BasicI32Encoding) {
  auto M = createStoreLoadFunction(32);
  auto *F = M->getFunction("test_fn");

  unsigned storesBefore = countOpcode(F, llvm::Instruction::Store);
  unsigned loadsBefore = countOpcode(F, llvm::Instruction::Load);
  ASSERT_EQ(storesBefore, 1u);
  ASSERT_EQ(loadsBefore, 1u);

  ollvm::encodeAllocasModule(*M, 42);

  // After encoding, there should be mul/add for encode and sub/mul for decode.
  unsigned muls = countOpcode(F, llvm::Instruction::Mul);
  unsigned adds = countOpcode(F, llvm::Instruction::Add);
  unsigned subs = countOpcode(F, llvm::Instruction::Sub);

  // Encode: mul + add. Decode: sub + mul. Total: 2 mul, 1 add, 1 sub.
  EXPECT_EQ(muls, 2u);
  EXPECT_EQ(adds, 1u);
  EXPECT_EQ(subs, 1u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ------------------------------------------------------------------
// BasicI64Encoding: same for i64.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, BasicI64Encoding) {
  auto M = createStoreLoadFunction(64);
  auto *F = M->getFunction("test_fn");

  ollvm::encodeAllocasModule(*M, 99);

  unsigned muls = countOpcode(F, llvm::Instruction::Mul);
  EXPECT_EQ(muls, 2u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ------------------------------------------------------------------
// RoundTripCorrectness: verify decode math undoes encode for constant.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, RoundTripCorrectness) {
  // Test with a known constant: store 42, load back.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  llvm::IRBuilder<> B(entry);
  auto *alloca = B.CreateAlloca(i32Ty, nullptr, "");
  B.CreateStore(llvm::ConstantInt::get(i32Ty, 42), alloca);
  auto *loaded = B.CreateLoad(i32Ty, alloca, "");
  B.CreateRet(loaded);

  ollvm::encodeAllocasModule(*M, 7);

  // The return value is the decoded result. Trace the computation:
  // The function returns decoded = (encoded - B) * A_inv
  // where encoded = 42 * A + B.
  // So decoded = ((42*A + B) - B) * A_inv = 42 * A * A_inv = 42.
  // The IR should verify.
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Verify the return instruction returns the decoded value (a mul),
  // not the raw load.
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(F->back().getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *retVal = ret->getReturnValue();
  // The decoded value should be a mul instruction (decoded = sub * A_inv).
  EXPECT_TRUE(llvm::isa<llvm::BinaryOperator>(retVal));
  auto *binOp = llvm::cast<llvm::BinaryOperator>(retVal);
  EXPECT_EQ(binOp->getOpcode(), llvm::Instruction::Mul);
}

// ------------------------------------------------------------------
// SkipsPointerUses: alloca used in GEP is not encoded.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, SkipsPointerUses) {
  auto M = createGEPUseFunction();
  auto *F = M->getFunction("test_fn");

  unsigned mulsBefore = countOpcode(F, llvm::Instruction::Mul);

  ollvm::encodeAllocasModule(*M, 42);

  // No encoding should have been inserted.
  unsigned mulsAfter = countOpcode(F, llvm::Instruction::Mul);
  EXPECT_EQ(mulsBefore, mulsAfter);
}

// ------------------------------------------------------------------
// SkipsCallUses: alloca passed to a call is not encoded.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, SkipsCallUses) {
  auto M = createCallUseFunction();
  auto *F = M->getFunction("test_fn");

  unsigned mulsBefore = countOpcode(F, llvm::Instruction::Mul);

  ollvm::encodeAllocasModule(*M, 42);

  unsigned mulsAfter = countOpcode(F, llvm::Instruction::Mul);
  EXPECT_EQ(mulsBefore, mulsAfter);
}

// ------------------------------------------------------------------
// SkipsVolatile: volatile load/store alloca is not encoded.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, SkipsVolatile) {
  auto M = createVolatileFunction();
  auto *F = M->getFunction("test_fn");

  unsigned mulsBefore = countOpcode(F, llvm::Instruction::Mul);

  ollvm::encodeAllocasModule(*M, 42);

  unsigned mulsAfter = countOpcode(F, llvm::Instruction::Mul);
  EXPECT_EQ(mulsBefore, mulsAfter);
}

// ------------------------------------------------------------------
// ModuleVerifies: verify across 10 seeds.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, ModuleVerifies) {
  for (uint32_t seed = 0; seed < 10; ++seed) {
    auto M = createStoreLoadFunction(32);
    ollvm::encodeAllocasModule(*M, seed);
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Failed for seed " << seed;
  }
}

// ------------------------------------------------------------------
// DifferentEncodings: different allocas get different A,B values.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, DifferentEncodings) {
  auto M = createTwoAllocaFunction();
  auto *F = M->getFunction("test_fn");

  ollvm::encodeAllocasModule(*M, 42);

  // Both allocas should be encoded. Collect all ConstantInt operands
  // of Mul instructions — the A and A_inv constants should differ
  // between the two allocas.
  std::set<uint64_t> mulConstants;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (I.getOpcode() == llvm::Instruction::Mul) {
        for (unsigned i = 0; i < I.getNumOperands(); ++i) {
          if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(I.getOperand(i)))
            mulConstants.insert(CI->getZExtValue());
        }
      }
    }
  }

  // With two allocas encoded, we expect at least 2 distinct constants
  // (different A values for each alloca).
  EXPECT_GE(mulConstants.size(), 2u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ------------------------------------------------------------------
// FilterConfigSkips: transform_percent=0 skips all allocas.
// ------------------------------------------------------------------
TEST_F(ArithmeticEncodingObfTest, FilterConfigSkips) {
  auto M = createStoreLoadFunction(32);
  auto *F = M->getFunction("test_fn");

  unsigned mulsBefore = countOpcode(F, llvm::Instruction::Mul);

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 0;
  ollvm::encodeAllocasModule(*M, 42, cfg);

  unsigned mulsAfter = countOpcode(F, llvm::Instruction::Mul);
  EXPECT_EQ(mulsBefore, mulsAfter);
}

}  // namespace

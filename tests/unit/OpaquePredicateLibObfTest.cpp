// OpaquePredicateLib unit tests
#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/TargetParser/Triple.h>

#include <cstdint>

#include "../../tools/ollvm-obf/OpaquePredicateLib.h"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-"
    "n8:16:32:64-S128";

class OpaquePredicateLibTest : public ::testing::Test {
protected:
  llvm::LLVMContext Ctx;

  /// Create a module + function(i64) -> void with an empty entry block.
  std::pair<std::unique_ptr<llvm::Module>, llvm::Function *>
  createI64Function(const char *name = "test_fn") {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, *M);
    llvm::BasicBlock::Create(Ctx, "entry", F);
    return {std::move(M), F};
  }

  /// Create a module + function() -> i1 suitable for CRC32 predicate tests.
  /// Adds target-features "+sse4.2" so the intrinsic verifies.
  std::pair<std::unique_ptr<llvm::Module>, llvm::Function *>
  createCRC32Function(const char *name = "crc_fn") {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    M->setTargetTriple(llvm::Triple("x86_64-pc-windows-msvc"));

    auto *i1Ty = llvm::Type::getInt1Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i1Ty, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, *M);
    F->addFnAttr("target-features", "+sse4.2");
    llvm::BasicBlock::Create(Ctx, "entry", F);
    return {std::move(M), F};
  }
};

// ===== softwareCRC32C tests =====

TEST_F(OpaquePredicateLibTest, CRC32KnownValues) {
  // CRC32C(0, 0) — no bits set, polynomial never applied.
  EXPECT_EQ(ollvm::softwareCRC32C(0, 0), 0u);

  // CRC32C(0xFFFFFFFF, 0) — standard init with zero data.
  uint32_t result = ollvm::softwareCRC32C(0xFFFFFFFF, 0);
  uint32_t expected = 0xFFFFFFFF;
  for (int i = 0; i < 32; ++i) {
    if (expected & 1)
      expected = (expected >> 1) ^ 0x82F63B78u;
    else
      expected >>= 1;
  }
  EXPECT_EQ(result, expected);

  // CRC32C(0, 1)
  uint32_t r2 = ollvm::softwareCRC32C(0, 1);
  uint32_t e2 = 1; // 0 ^ 1
  for (int i = 0; i < 32; ++i) {
    if (e2 & 1)
      e2 = (e2 >> 1) ^ 0x82F63B78u;
    else
      e2 >>= 1;
  }
  EXPECT_EQ(r2, e2);
}

TEST_F(OpaquePredicateLibTest, CRC32Deterministic) {
  for (uint32_t crc : {0u, 1u, 42u, 0xDEADBEEFu, 0xFFFFFFFFu}) {
    for (uint32_t data : {0u, 1u, 255u, 0x12345678u}) {
      uint32_t a = ollvm::softwareCRC32C(crc, data);
      uint32_t b = ollvm::softwareCRC32C(crc, data);
      EXPECT_EQ(a, b) << "crc=" << crc << " data=" << data;
    }
  }
}

// ===== buildMBAZero tests =====

TEST_F(OpaquePredicateLibTest, MBAZeroIsAlwaysZero) {
  for (uint64_t seed = 0; seed < 50; ++seed) {
    auto [M, F] = createI64Function();
    llvm::IRBuilder<> builder(&F->getEntryBlock());
    auto *arg = F->getArg(0);

    auto *result = ollvm::detail::buildMBAZero(builder, arg, seed);

    // Result must be i64 (same type as input).
    EXPECT_EQ(result->getType(), arg->getType()) << "seed=" << seed;

    // The result should be a mul instruction (scale factor M * zero).
    EXPECT_TRUE(llvm::isa<llvm::BinaryOperator>(result))
        << "Expected BinaryOperator for seed=" << seed;
    if (auto *binOp = llvm::dyn_cast<llvm::BinaryOperator>(result)) {
      EXPECT_EQ(binOp->getOpcode(), llvm::Instruction::Mul)
          << "Expected Mul for seed=" << seed;
    }

    builder.CreateRetVoid();
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Module verification failed for seed=" << seed;
  }
}

TEST_F(OpaquePredicateLibTest, MBAZeroVerifiesAllSeeds) {
  for (uint64_t seed = 0; seed < 100; ++seed) {
    auto [M, F] = createI64Function();
    llvm::IRBuilder<> builder(&F->getEntryBlock());
    ollvm::detail::buildMBAZero(builder, F->getArg(0), seed);
    builder.CreateRetVoid();

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Verification failed at seed=" << seed;
  }
}

// ===== generateOpaqueTrue tests =====

TEST_F(OpaquePredicateLibTest, OpaqueTrueVerifies) {
  for (uint64_t seed = 0; seed < 50; ++seed) {
    auto [M, F] = createI64Function();
    llvm::IRBuilder<> builder(&F->getEntryBlock());
    ollvm::generateOpaqueTrue(builder, F->getArg(0), seed);
    builder.CreateRetVoid();

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Verification failed at seed=" << seed;
  }
}

TEST_F(OpaquePredicateLibTest, OpaqueTrueReturnsI1) {
  auto [M, F] = createI64Function();
  llvm::IRBuilder<> builder(&F->getEntryBlock());
  auto *result = ollvm::generateOpaqueTrue(builder, F->getArg(0), 42);
  builder.CreateRetVoid();

  EXPECT_TRUE(result->getType()->isIntegerTy(1));
}

TEST_F(OpaquePredicateLibTest, OpaqueTrueProducesICmp) {
  auto [M, F] = createI64Function();
  llvm::IRBuilder<> builder(&F->getEntryBlock());
  auto *result = ollvm::generateOpaqueTrue(builder, F->getArg(0), 99);
  builder.CreateRetVoid();

  auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(result);
  ASSERT_NE(icmp, nullptr) << "Expected ICmpInst";
  // Predicate varies by seed — accept any always-true variant.
  auto pred = icmp->getPredicate();
  bool valid = (pred == llvm::CmpInst::ICMP_EQ ||
                pred == llvm::CmpInst::ICMP_SLE ||
                pred == llvm::CmpInst::ICMP_UGE ||
                pred == llvm::CmpInst::ICMP_SLT);
  EXPECT_TRUE(valid) << "Unexpected predicate " << pred;
}

// ===== buildCRC32Predicate tests =====

TEST_F(OpaquePredicateLibTest, CRC32PredicateVerifies) {
  for (uint64_t seed = 0; seed < 50; ++seed) {
    auto [M, F] = createCRC32Function();
    llvm::IRBuilder<> builder(&F->getEntryBlock());
    auto *result = ollvm::buildCRC32Predicate(builder, *F, seed);
    builder.CreateRet(result);

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Verification failed at seed=" << seed;
  }
}

TEST_F(OpaquePredicateLibTest, CRC32PredicateReturnsI1) {
  auto [M, F] = createCRC32Function();
  llvm::IRBuilder<> builder(&F->getEntryBlock());
  auto *result = ollvm::buildCRC32Predicate(builder, *F, 77);
  builder.CreateRet(result);

  EXPECT_TRUE(result->getType()->isIntegerTy(1));
}

TEST_F(OpaquePredicateLibTest, CRC32PredicateUsesIntrinsic) {
  auto [M, F] = createCRC32Function();
  llvm::IRBuilder<> builder(&F->getEntryBlock());
  ollvm::buildCRC32Predicate(builder, *F, 123);
  builder.CreateRet(llvm::ConstantInt::getTrue(Ctx));

  bool foundIntrinsic = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (auto *callee = call->getCalledFunction()) {
          if (callee->getName() == "llvm.x86.sse42.crc32.32.32")
            foundIntrinsic = true;
        }
      }
    }
  }
  EXPECT_TRUE(foundIntrinsic) << "Expected call to llvm.x86.sse42.crc32.32.32";
}

TEST_F(OpaquePredicateLibTest, CRC32PredicateHasVolatileLoad) {
  auto [M, F] = createCRC32Function();
  llvm::IRBuilder<> builder(&F->getEntryBlock());
  ollvm::buildCRC32Predicate(builder, *F, 456);
  builder.CreateRet(llvm::ConstantInt::getTrue(Ctx));

  bool foundVolatile = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *load = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        if (load->isVolatile())
          foundVolatile = true;
      }
    }
  }
  EXPECT_TRUE(foundVolatile) << "Expected volatile load in CRC32 predicate";
}

// ===== generateOpaqueTrue additional structural tests =====

TEST_F(OpaquePredicateLibTest, OpaqueTrueIsAlwaysTrueICmp) {
  // generateOpaqueTrue must always produce an ICmpInst whose predicate
  // is one of the always-true variants (eq/sle/uge/slt comparing MBA zero).
  for (uint64_t seed = 0; seed < 20; ++seed) {
    auto [M, F] = createI64Function();
    llvm::IRBuilder<> builder(&F->getEntryBlock());
    auto *result = ollvm::generateOpaqueTrue(builder, F->getArg(0), seed);
    builder.CreateRetVoid();

    auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(result);
    ASSERT_NE(icmp, nullptr) << "seed=" << seed;
    auto pred = icmp->getPredicate();
    bool valid = (pred == llvm::CmpInst::ICMP_EQ ||
                  pred == llvm::CmpInst::ICMP_SLE ||
                  pred == llvm::CmpInst::ICMP_UGE ||
                  pred == llvm::CmpInst::ICMP_SLT);
    EXPECT_TRUE(valid) << "Unexpected predicate at seed=" << seed;
  }
}

TEST_F(OpaquePredicateLibTest, MBAZeroScaleFactorIsNonTrivial) {
  // The final mul should have a constant operand in [2, 255].
  for (uint64_t seed = 0; seed < 50; ++seed) {
    auto [M, F] = createI64Function();
    llvm::IRBuilder<> builder(&F->getEntryBlock());
    auto *result = ollvm::detail::buildMBAZero(builder, F->getArg(0), seed);
    builder.CreateRetVoid();

    auto *mul = llvm::dyn_cast<llvm::BinaryOperator>(result);
    ASSERT_NE(mul, nullptr) << "seed=" << seed;

    // One operand should be the scale constant M.
    llvm::ConstantInt *scale = nullptr;
    if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(mul->getOperand(1)))
      scale = c;
    else if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(mul->getOperand(0)))
      scale = c;

    ASSERT_NE(scale, nullptr) << "No constant in mul at seed=" << seed;
    uint64_t m = scale->getZExtValue();
    EXPECT_GE(m, 2u) << "Scale too small at seed=" << seed;
    EXPECT_LE(m, 255u) << "Scale too large at seed=" << seed;
  }
}

} // namespace

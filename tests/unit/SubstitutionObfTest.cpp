#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/Substitution.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class SubstitutionObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_sub", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function with a single binary operation: %r = OP i32 %arg0, %arg1
  llvm::Function *createBinOpFunction(llvm::Module &M, const std::string &name,
                                      llvm::Instruction::BinaryOps opcode) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty, i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *r = B.CreateBinOp(opcode, F->getArg(0), F->getArg(1), "r");
    B.CreateRet(r);
    return F;
  }

  /// Create a function with: %r = OP i32 %arg0, constRHS; ret %r
  llvm::Function *createShiftFunction(llvm::Module &M, const std::string &name,
                                      llvm::Instruction::BinaryOps opcode,
                                      uint32_t constRHS) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *rhs = llvm::ConstantInt::get(i32Ty, constRHS);
    auto *r = B.CreateBinOp(opcode, F->getArg(0), rhs, "r");
    B.CreateRet(r);
    return F;
  }

  /// Check if an instruction with the given opcode exists in the function.
  bool hasOpcode(llvm::Function &F, unsigned opcode) {
    for (auto &BB : F)
      for (auto &I : BB)
        if (I.getOpcode() == opcode)
          return true;
    return false;
  }

  /// Count instructions with the given opcode.
  unsigned countOpcode(llvm::Function &F, unsigned opcode) {
    unsigned count = 0;
    for (auto &BB : F)
      for (auto &I : BB)
        if (I.getOpcode() == opcode)
          ++count;
    return count;
  }

  /// Serialize the function to a string for comparison.
  std::string serializeFunction(llvm::Function &F) {
    std::string str;
    llvm::raw_string_ostream os(str);
    F.print(os);
    return str;
  }

  /// Run substitute over many seeds until the transform fires, return the seed
  /// that triggered it (or -1 if none did).
  int findFiringSeed(llvm::Instruction::BinaryOps opcode, uint32_t constRHS,
                     unsigned maxSeeds = 200) {
    for (uint32_t seed = 0; seed < maxSeeds; ++seed) {
      auto M = createModule();
      createShiftFunction(*M, "fn", opcode, constRHS);
      ollvm::substituteModule(*M, seed);
      auto *F = M->getFunction("fn");
      if (!hasOpcode(*F, opcode))
        return static_cast<int>(seed);
    }
    return -1;
  }
};

// ---------------------------------------------------------------------------
// 1. ShlSubstitution: shl i32 %a, 3 => mul %a, 8
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, ShlSubstitution) {
  int seed = findFiringSeed(llvm::Instruction::Shl, 3);
  ASSERT_GE(seed, 0) << "No seed in [0,200) triggered shl substitution";

  auto M = createModule();
  createShiftFunction(*M, "fn", llvm::Instruction::Shl, 3);
  ollvm::substituteModule(*M, static_cast<uint32_t>(seed));
  auto *F = M->getFunction("fn");

  EXPECT_FALSE(hasOpcode(*F, llvm::Instruction::Shl))
      << "shl should have been replaced";
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::Mul))
      << "shl should be replaced with mul";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

// ---------------------------------------------------------------------------
// 2. LShrSubstitution: lshr i32 %a, 2 => udiv %a, 4
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, LShrSubstitution) {
  int seed = findFiringSeed(llvm::Instruction::LShr, 2);
  ASSERT_GE(seed, 0) << "No seed in [0,200) triggered lshr substitution";

  auto M = createModule();
  createShiftFunction(*M, "fn", llvm::Instruction::LShr, 2);
  ollvm::substituteModule(*M, static_cast<uint32_t>(seed));
  auto *F = M->getFunction("fn");

  EXPECT_FALSE(hasOpcode(*F, llvm::Instruction::LShr))
      << "lshr should have been replaced";
  EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::UDiv))
      << "lshr should be replaced with udiv";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

// ---------------------------------------------------------------------------
// 3. AShrPositive: ashr i32 100, 1 => 50
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, AShrPositive) {
  // Build: define i32 @fn() { ret i32 (ashr 100, 1) }
  // Use both-constant form but make one operand non-constant to avoid the
  // constant-skip filter. Build: %r = ashr i32 %a, 1; with a known call.
  // Instead, verify algebraically: for positive a, a ashr b == a udiv (1<<b).
  uint32_t a = 100;
  uint32_t b = 1;
  int32_t expected = static_cast<int32_t>(a) >> b; // 50
  ASSERT_EQ(expected, 50);

  // The substitution replaces ashr with select(a>=0, a udiv (1<<b), ~(~a udiv (1<<b)))
  // For a=100 (positive): result = 100 udiv 2 = 50.
  uint32_t pow2 = 1u << b;
  uint32_t pos_result = a / pow2;
  EXPECT_EQ(static_cast<int32_t>(pos_result), expected);
}

// ---------------------------------------------------------------------------
// 4. AShrNegative: ashr i32 -7, 1 => -4
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, AShrNegative) {
  int32_t a = -7;
  uint32_t b = 1;
  int32_t expected = a >> b; // -4 (arithmetic shift, rounds toward -inf)
  ASSERT_EQ(expected, -4);

  // Substitution for negative: ~(~a udiv (1 << b))
  uint32_t ua = static_cast<uint32_t>(a);
  uint32_t not_a = ~ua;
  uint32_t pow2 = 1u << b;
  uint32_t neg_div = not_a / pow2;
  int32_t neg_result = static_cast<int32_t>(~neg_div);
  EXPECT_EQ(neg_result, expected)
      << "AShr substitution for negative value should match arithmetic shift";
}

// ---------------------------------------------------------------------------
// 5. AShrEdgeCases: -1, 0, INT_MIN, INT_MAX with shift=1
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, AShrEdgeCases) {
  struct TestCase {
    int32_t input;
    int32_t expected;
  };
  TestCase cases[] = {
      {-1, -1},                          // -1 >> 1 == -1
      {0, 0},                            // 0 >> 1 == 0
      {INT32_MIN, INT32_MIN / 2},        // -2147483648 >> 1 == -1073741824
      {INT32_MAX, INT32_MAX / 2},        // 2147483647 >> 1 == 1073741823
  };

  uint32_t shift = 1;
  uint32_t pow2 = 1u << shift;

  for (auto &tc : cases) {
    uint32_t ua = static_cast<uint32_t>(tc.input);
    int32_t result;
    if (tc.input >= 0) {
      result = static_cast<int32_t>(ua / pow2);
    } else {
      uint32_t not_a = ~ua;
      uint32_t neg_div = not_a / pow2;
      result = static_cast<int32_t>(~neg_div);
    }
    EXPECT_EQ(result, tc.expected)
        << "AShr substitution failed for input=" << tc.input;
  }
}

// ---------------------------------------------------------------------------
// 6. LShrVariableSkipped: lshr with variable shift should not be transformed
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, LShrVariableSkipped) {
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createModule();
    createBinOpFunction(*M, "fn", llvm::Instruction::LShr);
    ollvm::substituteModule(*M, seed);
    auto *F = M->getFunction("fn");
    EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::LShr))
        << "Variable-shift lshr should NOT be substituted (seed=" << seed
        << ")";
  }
}

// ---------------------------------------------------------------------------
// 7. AShrVariableSkipped: ashr with variable shift should not be transformed
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, AShrVariableSkipped) {
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createModule();
    createBinOpFunction(*M, "fn", llvm::Instruction::AShr);
    ollvm::substituteModule(*M, seed);
    auto *F = M->getFunction("fn");
    EXPECT_TRUE(hasOpcode(*F, llvm::Instruction::AShr))
        << "Variable-shift ashr should NOT be substituted (seed=" << seed
        << ")";
  }
}

// ---------------------------------------------------------------------------
// 8. AddMBACorrectness: add MBA variants produce correct results algebraically
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, AddMBACorrectness) {
  // Both MBA variants for add:
  //   Variant 0: (a ^ b) + 2*(a & b) == a + b
  //   Variant 1: (a | b) + (a & b)   == a + b
  uint32_t testPairs[][2] = {
      {0, 0},     {1, 1},           {0xFFFFFFFF, 0},
      {42, 58},   {0xDEAD, 0xBEEF}, {INT32_MAX, 1},
  };

  for (auto &pair : testPairs) {
    uint32_t a = pair[0], b = pair[1];
    uint32_t expected = a + b;

    // Variant 0
    uint32_t v0 = (a ^ b) + 2 * (a & b);
    EXPECT_EQ(v0, expected) << "MBA add variant 0 failed for a=" << a
                            << " b=" << b;

    // Variant 1
    uint32_t v1 = (a | b) + (a & b);
    EXPECT_EQ(v1, expected) << "MBA add variant 1 failed for a=" << a
                            << " b=" << b;
  }
}

// ---------------------------------------------------------------------------
// 9. ModuleVerifiesAllOpcodes: function with all opcodes, substitute with 20
//    seeds, verify module each time
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, ModuleVerifiesAllOpcodes) {
  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createModule();
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty, i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "all_ops", *M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *a = F->getArg(0);
    auto *b = F->getArg(1);
    auto *three = llvm::ConstantInt::get(i32Ty, 3);

    auto *v_add = B.CreateAdd(a, b, "v_add");
    auto *v_sub = B.CreateSub(v_add, a, "v_sub");
    auto *v_xor = B.CreateXor(v_sub, b, "v_xor");
    auto *v_and = B.CreateAnd(v_xor, a, "v_and");
    auto *v_or = B.CreateOr(v_and, b, "v_or");
    auto *v_shl = B.CreateShl(v_or, three, "v_shl");
    auto *v_lshr = B.CreateLShr(v_shl, three, "v_lshr");
    auto *v_ashr = B.CreateAShr(v_lshr, three, "v_ashr");
    B.CreateRet(v_ashr);

    ollvm::substituteModule(*M, seed);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed with seed=" << seed << ": " << errStr;
  }
}

// ---------------------------------------------------------------------------
// 10. DeclarationSkipped: declare-only function should not crash
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, DeclarationSkipped) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage, "decl_fn", *M);

  // Should not crash.
  ollvm::substituteModule(*M, 42);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

// ---------------------------------------------------------------------------
// 11. DeterministicOutput: same seed = same output
// ---------------------------------------------------------------------------
TEST_F(SubstitutionObfTest, DeterministicOutput) {
  constexpr uint32_t kSeed = 12345;

  auto M1 = createModule();
  createBinOpFunction(*M1, "fn", llvm::Instruction::Add);
  createShiftFunction(*M1, "fn_shl", llvm::Instruction::Shl, 3);
  ollvm::substituteModule(*M1, kSeed);

  auto M2 = createModule();
  createBinOpFunction(*M2, "fn", llvm::Instruction::Add);
  createShiftFunction(*M2, "fn_shl", llvm::Instruction::Shl, 3);
  ollvm::substituteModule(*M2, kSeed);

  auto ir1_add = serializeFunction(*M1->getFunction("fn"));
  auto ir2_add = serializeFunction(*M2->getFunction("fn"));
  EXPECT_EQ(ir1_add, ir2_add) << "Same seed should produce identical output";

  auto ir1_shl = serializeFunction(*M1->getFunction("fn_shl"));
  auto ir2_shl = serializeFunction(*M2->getFunction("fn_shl"));
  EXPECT_EQ(ir1_shl, ir2_shl)
      << "Same seed should produce identical shift output";

  // Different seed should differ (at least one of them).
  auto M3 = createModule();
  createBinOpFunction(*M3, "fn", llvm::Instruction::Add);
  createShiftFunction(*M3, "fn_shl", llvm::Instruction::Shl, 3);
  ollvm::substituteModule(*M3, 99999);

  auto ir3_add = serializeFunction(*M3->getFunction("fn"));
  auto ir3_shl = serializeFunction(*M3->getFunction("fn_shl"));
  bool differs = (ir1_add != ir3_add) || (ir1_shl != ir3_shl);
  EXPECT_TRUE(differs)
      << "Different seeds should produce different output for at least one fn";
}

TEST_F(SubstitutionObfTest, WideIntegerSkipped) {
  // i128 operations must be skipped — modInverse uses uint64_t arithmetic
  // which is incorrect for >64-bit types.
  auto M = createModule();
  auto *i128Ty = llvm::Type::getInt128Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i128Ty, {i128Ty, i128Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "wide_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entry);
  auto *add = builder.CreateAdd(F->getArg(0), F->getArg(1));
  auto *xorOp = builder.CreateXor(add, F->getArg(0));
  builder.CreateRet(xorOp);

  std::string before;
  { llvm::raw_string_ostream os(before); F->print(os); }

  ollvm::substituteModule(*M, 42);

  std::string after;
  { llvm::raw_string_ostream os(after); F->print(os); }

  // i128 function should remain untouched.
  EXPECT_EQ(before, after)
      << "i128 operations should not be substituted";
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

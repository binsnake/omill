#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/Vectorize.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class VectorizeObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_vec", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function: `type @name(type %a, type %b) { %r = OP %a, %b; ret %r }`
  llvm::Function *createArithFunction(llvm::Module &M, const std::string &name,
                                      llvm::Instruction::BinaryOps opcode,
                                      llvm::Type *ty) {
    auto *fnTy = llvm::FunctionType::get(ty, {ty, ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *r = B.CreateBinOp(opcode, F->getArg(0), F->getArg(1), "r");
    B.CreateRet(r);
    return F;
  }

  /// Count instructions whose result type is a vector type.
  unsigned countVectorInsts(llvm::Function &F) {
    unsigned count = 0;
    for (auto &I : llvm::instructions(F)) {
      if (I.getType()->isVectorTy())
        ++count;
    }
    return count;
  }

  /// Check if any instruction in the module has a vector type.
  bool hasAnyVectorType(llvm::Module &M) {
    for (auto &F : M) {
      for (auto &I : llvm::instructions(F)) {
        if (I.getType()->isVectorTy())
          return true;
      }
    }
    return false;
  }

  /// Count InsertElementInst instructions.
  unsigned countInsertElements(llvm::Function &F) {
    unsigned count = 0;
    for (auto &I : llvm::instructions(F)) {
      if (llvm::isa<llvm::InsertElementInst>(&I))
        ++count;
    }
    return count;
  }

  /// Serialize the function to a string for comparison.
  std::string serializeFunction(llvm::Function &F) {
    std::string str;
    llvm::raw_string_ostream os(str);
    F.print(os);
    return str;
  }

  /// Count total instructions in a function.
  unsigned countInstructions(llvm::Function &F) {
    unsigned count = 0;
    for (auto &I : llvm::instructions(F))
      ++count;
    return count;
  }
};

TEST_F(VectorizeObfTest, BasicI32Vectorization) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt32Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  ollvm::vectorizeModule(*M, 42, opts);

  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  // At 100% the scalar add should be vectorized — expect vector instructions.
  unsigned vecInsts = countVectorInsts(*F);
  EXPECT_GT(vecInsts, 0u)
      << "100% vectorize should produce vector instructions for i32 add";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

TEST_F(VectorizeObfTest, BasicI64Vectorization) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt64Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_i64 = true;
  ollvm::vectorizeModule(*M, 42, opts);

  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  // Look for <2 x i64> vector types.
  bool foundI64Vec = false;
  for (auto &I : llvm::instructions(*F)) {
    if (auto *vecTy = llvm::dyn_cast<llvm::VectorType>(I.getType())) {
      if (vecTy->getElementType()->isIntegerTy(64)) {
        foundI64Vec = true;
        break;
      }
    }
  }
  EXPECT_TRUE(foundI64Vec)
      << "vectorize_i64=true should produce <2 x i64> vector types";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

TEST_F(VectorizeObfTest, I64DisabledSkipsI64) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt64Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_i64 = false;
  ollvm::vectorizeModule(*M, 42, opts);

  EXPECT_FALSE(hasAnyVectorType(*M))
      << "vectorize_i64=false should not produce any vector instructions for i64";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

TEST_F(VectorizeObfTest, ConstantMinusOne) {
  // xor i64 %x, -1 is bitwise NOT. The constant -1 (all ones, 0xFFFFFFFFFFFFFFFF)
  // is the DenseMap tombstone sentinel. This must not crash.
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "not_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *notVal = B.CreateXor(F->getArg(0),
                             llvm::ConstantInt::getSigned(i64Ty, -1), "bitnot");
  B.CreateRet(notVal);

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_i64 = true;
  // Must not crash.
  ollvm::vectorizeModule(*M, 42, opts);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed after xor i64 -1: " << errStr;
}

TEST_F(VectorizeObfTest, ConstantMinusOneI32) {
  // xor i32 %x, -1 (0xFFFFFFFF). Another DenseMap sentinel edge case.
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "not_fn32", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *notVal = B.CreateXor(F->getArg(0),
                             llvm::ConstantInt::getSigned(i32Ty, -1), "bitnot");
  B.CreateRet(notVal);

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_i64 = false;
  // Must not crash.
  ollvm::vectorizeModule(*M, 42, opts);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed after xor i32 -1: " << errStr;
}

TEST_F(VectorizeObfTest, NoiseLanesNonZero) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt32Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_data = true;
  ollvm::vectorizeModule(*M, 42, opts);

  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  // Check that InsertElement instructions exist with non-zero lane indices,
  // indicating noise fill in non-zero lanes.
  bool foundNonZeroLane = false;
  for (auto &I : llvm::instructions(*F)) {
    if (auto *IE = llvm::dyn_cast<llvm::InsertElementInst>(&I)) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(IE->getOperand(2))) {
        if (CI->getZExtValue() > 0) {
          foundNonZeroLane = true;
          break;
        }
      }
    }
  }
  // With vectorize_data=true, we expect noise lanes to be filled.
  unsigned insEls = countInsertElements(*F);
  EXPECT_GT(insEls, 0u) << "Should have InsertElement instructions";
  if (insEls > 0) {
    EXPECT_TRUE(foundNonZeroLane)
        << "At least one InsertElement should target a non-zero lane (noise)";
  }
}

TEST_F(VectorizeObfTest, DomTreeCrossBlock) {
  // entry: %x = add i32 %a, 1 -> br bb2
  // bb2:   %y = add i32 %x, 2 -> ret %y
  // DomTree should handle cross-block operands.
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "cross_fn", *M);
  auto *arg = F->getArg(0);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "bb2", F);

  llvm::IRBuilder<> entryB(entryBB);
  auto *x = entryB.CreateAdd(arg, llvm::ConstantInt::get(i32Ty, 1), "x");
  entryB.CreateBr(bb2);

  llvm::IRBuilder<> bb2B(bb2);
  auto *y = bb2B.CreateAdd(x, llvm::ConstantInt::get(i32Ty, 2), "y");
  bb2B.CreateRet(y);

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  ollvm::vectorizeModule(*M, 42, opts);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed with cross-block domtree: " << errStr;
}

TEST_F(VectorizeObfTest, ZeroPercentSkipsAll) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt32Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 0;
  ollvm::vectorizeModule(*M, 42, opts);

  EXPECT_FALSE(hasAnyVectorType(*M))
      << "transform_percent=0 should produce no vector instructions";
}

TEST_F(VectorizeObfTest, DeclarationSkipped) {
  auto M = createModule();
  // Add a declaration-only function (no body).
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage, "decl_fn", *M);

  // Also add a real function so vectorize has something to do.
  createArithFunction(*M, "real_fn", llvm::Instruction::Add, i32Ty);

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  // Must not crash on the declaration.
  ollvm::vectorizeModule(*M, 42, opts);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed with declaration present: " << errStr;
}

TEST_F(VectorizeObfTest, ModuleVerifiesAllSeeds) {
  // Run 20 different seeds with all options enabled, verify each.
  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_data = true;
  opts.vectorize_bitwise = true;
  opts.vectorize_i64 = true;

  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createModule();
    createArithFunction(*M, "fn_i32", llvm::Instruction::Add,
                        llvm::Type::getInt32Ty(Ctx));
    createArithFunction(*M, "fn_i64", llvm::Instruction::Add,
                        llvm::Type::getInt64Ty(Ctx));
    createArithFunction(*M, "fn_xor", llvm::Instruction::Xor,
                        llvm::Type::getInt32Ty(Ctx));
    createArithFunction(*M, "fn_sub", llvm::Instruction::Sub,
                        llvm::Type::getInt64Ty(Ctx));

    ollvm::vectorizeModule(*M, seed, opts);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed at seed " << seed << ": " << errStr;
  }
}

TEST_F(VectorizeObfTest, DeterministicOutput) {
  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_data = true;
  opts.vectorize_i64 = true;

  auto M1 = createModule();
  createArithFunction(*M1, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt32Ty(Ctx));
  ollvm::vectorizeModule(*M1, 12345, opts);
  auto ir1 = serializeFunction(*M1->getFunction("test_fn"));
  unsigned count1 = countInstructions(*M1->getFunction("test_fn"));

  auto M2 = createModule();
  createArithFunction(*M2, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt32Ty(Ctx));
  ollvm::vectorizeModule(*M2, 12345, opts);
  auto ir2 = serializeFunction(*M2->getFunction("test_fn"));
  unsigned count2 = countInstructions(*M2->getFunction("test_fn"));

  EXPECT_EQ(ir1, ir2)
      << "Same seed should produce identical vectorized output";
  EXPECT_EQ(count1, count2)
      << "Same seed should produce identical instruction count";

  // Different seed should differ.
  auto M3 = createModule();
  createArithFunction(*M3, "test_fn", llvm::Instruction::Add,
                      llvm::Type::getInt32Ty(Ctx));
  ollvm::vectorizeModule(*M3, 99999, opts);
  auto ir3 = serializeFunction(*M3->getFunction("test_fn"));

  EXPECT_NE(ir1, ir3)
      << "Different seeds should produce different output";
}

TEST_F(VectorizeObfTest, BitwiseMulDecomposition) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Mul,
                      llvm::Type::getInt32Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_bitwise = true;
  ollvm::vectorizeModule(*M, 42, opts);

  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  // Bitwise Mul decomposition produces vector AND, LShr, Shl, Mul, Add.
  unsigned vecInsts = countVectorInsts(*F);
  EXPECT_GT(vecInsts, 0u)
      << "Bitwise Mul should produce vector instructions";

  // Verify the schoolbook decomposition signature: at least 3 vector muls
  // (a_lo*b_lo, a_lo*b_hi, a_hi*b_lo) and shifts/masks.
  unsigned mulCount = 0;
  unsigned shlCount = 0;
  unsigned andCount = 0;
  for (auto &I : llvm::instructions(*F)) {
    if (!I.getType()->isVectorTy()) continue;
    if (I.getOpcode() == llvm::Instruction::Mul) ++mulCount;
    if (I.getOpcode() == llvm::Instruction::Shl) ++shlCount;
    if (I.getOpcode() == llvm::Instruction::And) ++andCount;
  }
  EXPECT_GE(mulCount, 3u) << "Should have >= 3 half-width vector muls";
  EXPECT_GE(shlCount, 2u) << "Should have >= 2 vector shifts";
  EXPECT_GE(andCount, 2u) << "Should have >= 2 vector masks";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

TEST_F(VectorizeObfTest, BitwiseMulI64) {
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Mul,
                      llvm::Type::getInt64Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_bitwise = true;
  opts.vectorize_i64 = true;
  ollvm::vectorizeModule(*M, 42, opts);

  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  // Check for <2 x i64> vector types from Mul decomposition.
  bool foundI64Vec = false;
  for (auto &I : llvm::instructions(*F)) {
    if (auto *vecTy = llvm::dyn_cast<llvm::VectorType>(I.getType())) {
      if (vecTy->getElementType()->isIntegerTy(64)) {
        foundI64Vec = true;
        break;
      }
    }
  }
  EXPECT_TRUE(foundI64Vec)
      << "Bitwise Mul i64 should produce <2 x i64> vector types";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

TEST_F(VectorizeObfTest, MulNonBitwiseFallback) {
  // Without vectorize_bitwise, Mul should still vectorize (plain vector mul).
  auto M = createModule();
  createArithFunction(*M, "test_fn", llvm::Instruction::Mul,
                      llvm::Type::getInt32Ty(Ctx));

  ollvm::VectorizeOptions opts;
  opts.transform_percent = 100;
  opts.vectorize_bitwise = false;
  ollvm::vectorizeModule(*M, 42, opts);

  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  unsigned vecInsts = countVectorInsts(*F);
  EXPECT_GT(vecInsts, 0u)
      << "Mul should be vectorized even without bitwise mode";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

}  // namespace

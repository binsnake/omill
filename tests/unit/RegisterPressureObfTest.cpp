#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>

#include "../../tools/ollvm-obf/RegisterPressure.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-"
    "n8:16:32:64-S128";

class RegisterPressureObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a function that uses an i64 argument across
  /// multiple basic blocks — a prime candidate for register pressure
  /// extension.
  std::unique_ptr<llvm::Module> createMultiBlockFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *mid = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exit = llvm::BasicBlock::Create(Ctx, "", F);

    auto *arg = F->getArg(0);

    // entry: use arg, branch to mid
    {
      llvm::IRBuilder<> B(entry);
      B.CreateAdd(arg, llvm::ConstantInt::get(i64Ty, 1), "");
      B.CreateBr(mid);
    }
    // mid: use arg again, branch to exit
    {
      llvm::IRBuilder<> B(mid);
      B.CreateAdd(arg, llvm::ConstantInt::get(i64Ty, 2), "");
      B.CreateBr(exit);
    }
    // exit: use arg, return
    {
      llvm::IRBuilder<> B(exit);
      auto *sum = B.CreateAdd(arg, llvm::ConstantInt::get(i64Ty, 3), "");
      B.CreateRet(sum);
    }

    return M;
  }

  /// Create a module with a function using pointer arguments across blocks.
  std::unique_ptr<llvm::Module> createPointerFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::getUnqual(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {ptrTy}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "ptr_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *mid = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exit = llvm::BasicBlock::Create(Ctx, "", F);

    auto *arg = F->getArg(0);

    // entry: load from arg, branch to mid
    {
      llvm::IRBuilder<> B(entry);
      B.CreateLoad(i64Ty, arg, "");
      B.CreateBr(mid);
    }
    // mid: load from arg again, branch to exit
    {
      llvm::IRBuilder<> B(mid);
      B.CreateLoad(i64Ty, arg, "");
      B.CreateBr(exit);
    }
    // exit: load and return
    {
      llvm::IRBuilder<> B(exit);
      auto *v = B.CreateLoad(i64Ty, arg, "");
      B.CreateRet(v);
    }

    return M;
  }


  /// Create a function with mixed-width integer arguments (i8, i16, i32, i64)
  /// used across multiple blocks — the pattern that triggers type mismatch
  /// when the asm always uses i64.
  std::unique_ptr<llvm::Module> createMixedWidthFunction() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i8Ty = llvm::Type::getInt8Ty(Ctx);
    auto *i16Ty = llvm::Type::getInt16Ty(Ctx);
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(
        i64Ty, {i8Ty, i16Ty, i32Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "mixed_fn", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    auto *mid = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exit = llvm::BasicBlock::Create(Ctx, "", F);

    // entry: use all args
    {
      llvm::IRBuilder<> B(entry);
      B.CreateAdd(F->getArg(0), llvm::ConstantInt::get(i8Ty, 1), "");
      B.CreateAdd(F->getArg(1), llvm::ConstantInt::get(i16Ty, 2), "");
      B.CreateAdd(F->getArg(2), llvm::ConstantInt::get(i32Ty, 3), "");
      B.CreateAdd(F->getArg(3), llvm::ConstantInt::get(i64Ty, 4), "");
      B.CreateBr(mid);
    }
    // mid: use all args again
    {
      llvm::IRBuilder<> B(mid);
      B.CreateAdd(F->getArg(0), llvm::ConstantInt::get(i8Ty, 10), "");
      B.CreateAdd(F->getArg(1), llvm::ConstantInt::get(i16Ty, 20), "");
      B.CreateAdd(F->getArg(2), llvm::ConstantInt::get(i32Ty, 30), "");
      B.CreateAdd(F->getArg(3), llvm::ConstantInt::get(i64Ty, 40), "");
      B.CreateBr(exit);
    }
    // exit: return i64 arg
    {
      llvm::IRBuilder<> B(exit);
      B.CreateRet(F->getArg(3));
    }
    return M;
  }

  /// Count inline asm calls in a function.
  unsigned countInlineAsm(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I))
          if (CB->isInlineAsm())
            ++count;
    return count;
  }

  /// Count ptrtoint instructions in a function.
  unsigned countPtrToInt(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (llvm::isa<llvm::PtrToIntInst>(&I))
          ++count;
    return count;
  }
};

/// Basic test: inline asm anchors are inserted for cross-block values.
TEST_F(RegisterPressureObfTest, BasicAnchor) {
  auto M = createMultiBlockFunction();
  auto *F = M->getFunction("test_fn");
  ASSERT_NE(F, nullptr);

  unsigned before = countInlineAsm(F);
  EXPECT_EQ(before, 0u);

  // Run with 100% transform_percent to maximize insertion chance.
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::extendRegisterPressureModule(*M, 42, cfg);

  unsigned after = countInlineAsm(F);
  // With 40% per-anchor probability and shuffle, at least one should hit
  // across multiple seeds. Try a few.
  bool anyInserted = after > 0;
  if (!anyInserted) {
    // Retry with different seeds.
    for (uint32_t seed = 0; seed < 20 && !anyInserted; ++seed) {
      auto M2 = createMultiBlockFunction();
      ollvm::extendRegisterPressureModule(*M2, seed, cfg);
      anyInserted = countInlineAsm(M2->getFunction("test_fn")) > 0;
    }
  }
  EXPECT_TRUE(anyInserted);
}

/// The inserted asm uses "=r,0" constraint — output tied to input (identity).
TEST_F(RegisterPressureObfTest, AsmIsIdentity) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  // Try seeds until we get an insertion.
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createMultiBlockFunction();
    ollvm::extendRegisterPressureModule(*M, seed, cfg);
    auto *F = M->getFunction("test_fn");

    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || !CB->isInlineAsm())
          continue;

        auto *IA = llvm::cast<llvm::InlineAsm>(CB->getCalledOperand());
        // Empty asm string — no machine instructions emitted.
        EXPECT_TRUE(IA->getAsmString().empty());
        // Constraint "=r,0" ties output register to input.
        EXPECT_EQ(IA->getConstraintString(), "=r,0");
        // Side effects prevent elimination.
        EXPECT_TRUE(IA->hasSideEffects());
        // One input operand.
        EXPECT_EQ(CB->arg_size(), 1u);
        return;  // Found and verified.
      }
    }
  }
  // If we never inserted across 50 seeds, something is wrong.
  FAIL() << "No inline asm anchor inserted across 50 seeds";
}

/// Module verifies after transformation across multiple seeds.
TEST_F(RegisterPressureObfTest, ModuleVerifies) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed : {0u, 1u, 42u, 1337u, 65535u}) {
    auto M = createMultiBlockFunction();
    ollvm::extendRegisterPressureModule(*M, seed, cfg);
    std::string err;
    llvm::raw_string_ostream os(err);
    EXPECT_FALSE(llvm::verifyModule(*M, &os))
        << "Verification failed for seed " << seed << ": " << err;
  }
}

/// Declarations should not be touched.
TEST_F(RegisterPressureObfTest, DeclarationSkipped) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  // Create a declaration (no body).
  llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage, "decl_fn", *M);

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::extendRegisterPressureModule(*M, 42, cfg);

  auto *F = M->getFunction("decl_fn");
  ASSERT_NE(F, nullptr);
  EXPECT_TRUE(F->isDeclaration());
  EXPECT_EQ(countInlineAsm(F), 0u);
}

/// Pointer values get ptrtoint/inttoptr wrapping around the asm.
TEST_F(RegisterPressureObfTest, PointerValuesHandled) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  bool foundPtrHandling = false;
  for (uint32_t seed = 0; seed < 50 && !foundPtrHandling; ++seed) {
    auto M = createPointerFunction();
    ollvm::extendRegisterPressureModule(*M, seed, cfg);
    auto *F = M->getFunction("ptr_fn");

    // If asm was inserted, there must be ptrtoint instructions.
    if (countInlineAsm(F) > 0) {
      EXPECT_GT(countPtrToInt(F), 0u);
      foundPtrHandling = true;

      // Verify the module is still valid.
      std::string err;
      llvm::raw_string_ostream os(err);
      EXPECT_FALSE(llvm::verifyModule(*M, &os)) << err;
    }
  }
  EXPECT_TRUE(foundPtrHandling)
      << "No pointer anchor inserted across 50 seeds";
}

/// With transform_percent=0, nothing should be inserted.
TEST_F(RegisterPressureObfTest, ZeroPercentNoTransform) {
  auto M = createMultiBlockFunction();
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 0;
  ollvm::extendRegisterPressureModule(*M, 42, cfg);
  EXPECT_EQ(countInlineAsm(M->getFunction("test_fn")), 0u);
}

/// At most 5 anchors per function.
TEST_F(RegisterPressureObfTest, MaxAnchorsRespected) {
  // Build a function with many cross-block values.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  llvm::SmallVector<llvm::Type *, 8> params(8, i64Ty);
  auto *fnTy = llvm::FunctionType::get(i64Ty, params, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "many_args", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  auto *mid = llvm::BasicBlock::Create(Ctx, "", F);
  auto *exit = llvm::BasicBlock::Create(Ctx, "", F);

  // Use all 8 args in entry and mid blocks.
  {
    llvm::IRBuilder<> B(entry);
    for (unsigned i = 0; i < 8; ++i)
      B.CreateAdd(F->getArg(i), llvm::ConstantInt::get(i64Ty, i), "");
    B.CreateBr(mid);
  }
  {
    llvm::IRBuilder<> B(mid);
    for (unsigned i = 0; i < 8; ++i)
      B.CreateAdd(F->getArg(i), llvm::ConstantInt::get(i64Ty, i + 10), "");
    B.CreateBr(exit);
  }
  {
    llvm::IRBuilder<> B(exit);
    auto *sum = B.CreateAdd(F->getArg(0), F->getArg(1), "");
    B.CreateRet(sum);
  }

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::extendRegisterPressureModule(*M, 42, cfg);

  EXPECT_LE(countInlineAsm(F), 5u);

  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << err;
}


/// Mixed-width integers (i8, i16, i32, i64) must all verify after
/// transformation — the original bug was always using i64 for the asm type.
TEST_F(RegisterPressureObfTest, MixedWidthIntegersVerify) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed : {0u, 1u, 42u, 1337u, 65535u}) {
    auto M = createMixedWidthFunction();
    ollvm::extendRegisterPressureModule(*M, seed, cfg);
    std::string err;
    llvm::raw_string_ostream os(err);
    EXPECT_FALSE(llvm::verifyModule(*M, &os))
        << "Verification failed for seed " << seed << ": " << err;
  }
}

/// Inline asm for non-i64 integers should use the value's actual type.
TEST_F(RegisterPressureObfTest, AsmTypeMatchesValue) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed = 0; seed < 100; ++seed) {
    auto M = createMixedWidthFunction();
    ollvm::extendRegisterPressureModule(*M, seed, cfg);
    auto *F = M->getFunction("mixed_fn");

    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || !CB->isInlineAsm())
          continue;
        // The asm function's return type must match its argument type.
        auto *asmFnTy = CB->getFunctionType();
        EXPECT_EQ(asmFnTy->getReturnType(), asmFnTy->getParamType(0))
            << "Asm return type doesn't match param type for seed " << seed;
        // The actual argument passed must match the asm's expected type.
        EXPECT_EQ(CB->getArgOperand(0)->getType(), asmFnTy->getParamType(0))
            << "Argument type mismatch for seed " << seed;
      }
    }
  }
}
}  // namespace

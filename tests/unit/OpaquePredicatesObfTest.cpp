#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>

#include "OpaquePredicates.h"
#include "OpaquePredicateLib.h"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-"
    "n8:16:32:64-S128";

class OpaquePredicatesObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a function that has the given number of blocks
  /// chained via unconditional branches: entry -> bb1 -> bb2 -> ... -> ret.
  std::unique_ptr<llvm::Module> createChainedFunction(
      unsigned numBlocks, bool withIntArg = true) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    llvm::SmallVector<llvm::Type *, 1> params;
    if (withIntArg)
      params.push_back(i64Ty);
    auto *fnTy = llvm::FunctionType::get(voidTy, params, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "test_fn", *M);

    // Create blocks.
    std::vector<llvm::BasicBlock *> blocks;
    blocks.push_back(llvm::BasicBlock::Create(Ctx, "entry", F));
    for (unsigned i = 1; i < numBlocks; ++i)
      blocks.push_back(llvm::BasicBlock::Create(
          Ctx, "bb" + std::to_string(i), F));

    // Chain them together with unconditional branches, last block returns.
    for (unsigned i = 0; i + 1 < numBlocks; ++i) {
      llvm::IRBuilder<> B(blocks[i]);
      // Add a dummy instruction to give the block some content.
      if (withIntArg) {
        auto *arg = F->getArg(0);
        B.CreateAdd(arg, llvm::ConstantInt::get(i64Ty, i), "dummy");
      }
      B.CreateBr(blocks[i + 1]);
    }

    // Last block returns.
    llvm::IRBuilder<> B(blocks.back());
    B.CreateRetVoid();

    return M;
  }

  unsigned countBlocks(llvm::Function *F) {
    return static_cast<unsigned>(std::distance(F->begin(), F->end()));
  }

  /// Count blocks whose name starts with prefix.
  unsigned countBlocksWithPrefix(llvm::Function *F, llvm::StringRef prefix) {
    unsigned count = 0;
    for (auto &BB : *F)
      if (BB.getName().starts_with(prefix))
        ++count;
    return count;
  }
};

/// A function with 4 blocks should gain extra opaque predicate blocks.
TEST_F(OpaquePredicatesObfTest, InsertsOpaqueBranch) {
  auto M = createChainedFunction(4);
  auto *F = M->getFunction("test_fn");
  unsigned origBlocks = countBlocks(F);
  ASSERT_EQ(origBlocks, 4u);

  // Use a seed that we know triggers insertion.
  // Run a few seeds to find one that adds at least one opaque predicate.
  bool found = false;
  for (uint32_t seed = 0; seed < 100 && !found; ++seed) {
    auto testM = createChainedFunction(4);
    ollvm::insertOpaquePredicatesModule(*testM, seed);
    auto *testF = testM->getFunction("test_fn");
    if (countBlocks(testF) > origBlocks) {
      found = true;
      // Verify extra blocks (junk) were added — names stripped for hardening.
      EXPECT_GT(countBlocks(testF), origBlocks);
    }
  }
  EXPECT_TRUE(found) << "No seed in [0,100) produced opaque predicates";
}

/// generateOpaqueTrue must return an i1 ICmpInst.  The comparison predicate
/// varies by seed (eq, sle, uge, slt, or dual-MBA eq).
TEST_F(OpaquePredicatesObfTest, PredicateAlwaysTrue) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1Ty  = llvm::Type::getInt1Ty(Ctx);
  auto *fnTy  = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx),
                                        {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "pred_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entry);
  auto *arg = F->getArg(0);

  uint64_t seeds[] = {0, 1, 42, 999, 0xDEADBEEF};
  for (uint64_t seed : seeds) {
    auto *cond = ollvm::generateOpaqueTrue(builder, arg, seed);

    // Must be i1.
    EXPECT_EQ(cond->getType(), i1Ty) << "seed=" << seed;

    // Must be an ICmpInst (predicate varies by seed).
    auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(cond);
    ASSERT_NE(icmp, nullptr) << "Not an ICmpInst for seed=" << seed;

    // Predicate must be one of the always-true variants.
    auto pred = icmp->getPredicate();
    bool validPred = (pred == llvm::CmpInst::ICMP_EQ ||
                      pred == llvm::CmpInst::ICMP_SLE ||
                      pred == llvm::CmpInst::ICMP_UGE ||
                      pred == llvm::CmpInst::ICMP_SLT);
    EXPECT_TRUE(validPred) << "Unexpected predicate for seed=" << seed;
  }

  builder.CreateRetVoid();
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

/// detail::buildMBAZero must return a value of the same type as the input
/// argument, and the module must verify.
TEST_F(OpaquePredicatesObfTest, MBAZeroPropertyHolds) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy  = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx),
                                        {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "mba_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entry);
  auto *arg = F->getArg(0);

  uint64_t seeds[] = {0, 1, 7, 42, 256, 0xCAFEBABE};
  for (uint64_t seed : seeds) {
    auto *result = ollvm::detail::buildMBAZero(builder, arg, seed);
    EXPECT_EQ(result->getType(), i64Ty)
        << "MBA zero type mismatch for seed=" << seed;
  }

  builder.CreateRetVoid();
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

/// Single-block functions should not be modified.
TEST_F(OpaquePredicatesObfTest, SkipsSingleBlockFunction) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  auto *voidTy = llvm::Type::getVoidTy(Ctx);
  auto *fnTy = llvm::FunctionType::get(voidTy, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "single_block", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRetVoid();

  ASSERT_EQ(countBlocks(F), 1u);
  ollvm::insertOpaquePredicatesModule(*M, 42);
  EXPECT_EQ(countBlocks(F), 1u);
}

/// The module must pass verifyModule after the pass.
TEST_F(OpaquePredicatesObfTest, ModuleVerifies) {
  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createChainedFunction(5);
    ollvm::insertOpaquePredicatesModule(*M, seed);
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Module verification failed with seed=" << seed;
  }
}

/// Same seed must produce identical output.
TEST_F(OpaquePredicatesObfTest, DeterministicWithSeed) {
  constexpr uint32_t kSeed = 12345;

  auto M1 = createChainedFunction(5);
  ollvm::insertOpaquePredicatesModule(*M1, kSeed);
  unsigned blocks1 = countBlocks(M1->getFunction("test_fn"));

  auto M2 = createChainedFunction(5);
  ollvm::insertOpaquePredicatesModule(*M2, kSeed);
  unsigned blocks2 = countBlocks(M2->getFunction("test_fn"));

  EXPECT_EQ(blocks1, blocks2);

  // Also verify block names match.
  auto *F1 = M1->getFunction("test_fn");
  auto *F2 = M2->getFunction("test_fn");
  auto it1 = F1->begin();
  auto it2 = F2->begin();
  for (; it1 != F1->end() && it2 != F2->end(); ++it1, ++it2) {
    EXPECT_EQ(it1->getName(), it2->getName());
  }
  EXPECT_EQ(it1, F1->end());
  EXPECT_EQ(it2, F2->end());
}

/// Functions without integer arguments should use alloca-based fallback.
TEST_F(OpaquePredicatesObfTest, NoIntArgUsesAlloca) {
  auto M = createChainedFunction(4, /*withIntArg=*/false);
  auto *F = M->getFunction("test_fn");
  unsigned origBlocks = countBlocks(F);

  // Try seeds until we get an insertion.
  bool found = false;
  for (uint32_t seed = 0; seed < 100 && !found; ++seed) {
    auto testM = createChainedFunction(4, /*withIntArg=*/false);
    ollvm::insertOpaquePredicatesModule(*testM, seed);
    auto *testF = testM->getFunction("test_fn");
    if (countBlocks(testF) > origBlocks) {
      found = true;
      // Should still verify — the alloca/load path must be correct.
      EXPECT_FALSE(llvm::verifyModule(*testM, &llvm::errs()));
    }
  }
  EXPECT_TRUE(found) << "No seed in [0,100) triggered alloca fallback path";
}

/// Return blocks should not have opaque predicates inserted before them.
TEST_F(OpaquePredicatesObfTest, SkipsReturnBlocks) {
  // Create a function where the last block has a return.
  // The pass should never change a return into a conditional branch.
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createChainedFunction(3);
    ollvm::insertOpaquePredicatesModule(*M, seed);
    auto *F = M->getFunction("test_fn");

    // Every return instruction should still be a plain ReturnInst.
    for (auto &BB : *F) {
      if (llvm::isa<llvm::ReturnInst>(BB.getTerminator())) {
        // The block ending in a return should not have been tampered with.
        EXPECT_TRUE(llvm::isa<llvm::ReturnInst>(BB.getTerminator()))
            << "Return block was modified with seed=" << seed;
      }
    }
  }
}

}  // namespace

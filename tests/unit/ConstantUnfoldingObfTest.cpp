#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/ConstantUnfolding.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class ConstantUnfoldingObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_const_unfold", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function with a single binary op: `ret (arg + C)`.
  llvm::Function *createAddConstFunction(llvm::Module &M,
                                         const std::string &name,
                                         int64_t constant) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);
    auto *add = builder.CreateAdd(F->getArg(0),
                                  llvm::ConstantInt::get(i64Ty, constant));
    builder.CreateRet(add);
    return F;
  }

  /// Create a function with many binary ops using diverse constants,
  /// maximizing the chance that at least some get unfolded.
  llvm::Function *createManyConstantsFunction(llvm::Module &M,
                                              const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);
    llvm::Value *acc = F->getArg(0);
    // 20 distinct non-trivial constants.
    for (int64_t c = 2; c <= 21; ++c) {
      acc = builder.CreateAdd(acc, llvm::ConstantInt::get(i64Ty, c * 7));
    }
    builder.CreateRet(acc);
    return F;
  }

  /// Count how many ConstantInt operands remain in a function's instructions
  /// (excluding PHIs, branch targets, etc.).
  unsigned countConstantIntOperands(llvm::Function &F) {
    unsigned count = 0;
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (llvm::isa<llvm::PHINode>(&I))
          continue;
        for (unsigned i = 0, e = I.getNumOperands(); i < e; ++i) {
          if (llvm::isa<llvm::ConstantInt>(I.getOperand(i)))
            ++count;
        }
      }
    }
    return count;
  }

  /// Check if a function contains a volatile load.
  bool hasVolatileLoad(llvm::Function &F) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          if (LI->isVolatile())
            return true;
        }
      }
    }
    return false;
  }
};

// --------------------------------------------------------------------------
// 1. After the pass, the module should contain unnamed internal i64 anchors.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, AnchorCreated) {
  auto M = createModule();
  createAddConstFunction(*M, "fn", 42);

  ollvm::unfoldConstantsModule(*M, 0);

  // Pass creates 3-5 unnamed internal i64 globals as anchors.
  unsigned anchorCount = 0;
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  for (auto &GV : M->globals()) {
    if (GV.hasInternalLinkage() && GV.getValueType() == i64Ty)
      ++anchorCount;
  }
  EXPECT_GE(anchorCount, 3u) << "Pass should create at least 3 anchor globals";
  EXPECT_LE(anchorCount, 5u) << "Pass should create at most 5 anchor globals";

  // No global should be named .cu_anchor (fingerprint removed).
  EXPECT_EQ(M->getGlobalVariable(".cu_anchor", true), nullptr)
      << "Anchor global must not be named .cu_anchor";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// --------------------------------------------------------------------------
// 2. Loads from the anchor must be volatile so the optimizer can't fold them.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, AnchorIsVolatileLoad) {
  auto M = createModule();
  createManyConstantsFunction(*M, "fn");

  // Run with many seeds until we find one that actually transforms.
  bool foundVolatile = false;
  for (uint32_t seed = 0; seed < 50 && !foundVolatile; ++seed) {
    auto Mx = createModule();
    createManyConstantsFunction(*Mx, "fn");
    ollvm::unfoldConstantsModule(*Mx, seed);
    auto *F = Mx->getFunction("fn");
    if (hasVolatileLoad(*F)) {
      foundVolatile = true;
      EXPECT_FALSE(llvm::verifyModule(*Mx, &llvm::errs()));
    }
  }
  EXPECT_TRUE(foundVolatile)
      << "At least one seed should produce a volatile anchor load";
}

// --------------------------------------------------------------------------
// 3. Trivial constants (0, 1, -1) should never be replaced.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, TrivialConstantsSkipped) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "trivial_fn", *M);
  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entryBB);
  auto *a0 = builder.CreateAdd(F->getArg(0),
                                llvm::ConstantInt::get(i64Ty, 0));
  auto *a1 = builder.CreateAdd(a0, llvm::ConstantInt::get(i64Ty, 1));
  auto *a2 = builder.CreateAdd(a1, llvm::ConstantInt::get(i64Ty, -1));
  builder.CreateRet(a2);

  unsigned before = countConstantIntOperands(*F);

  // Run many seeds — none should change these trivial constants.
  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto Mx = createModule();
    auto *i64 = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(i64, {i64}, false);
    auto *Fx = llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                      "trivial_fn", *Mx);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", Fx);
    llvm::IRBuilder<> b(bb);
    auto *x0 = b.CreateAdd(Fx->getArg(0),
                            llvm::ConstantInt::get(i64, 0));
    auto *x1 = b.CreateAdd(x0, llvm::ConstantInt::get(i64, 1));
    auto *x2 = b.CreateAdd(x1, llvm::ConstantInt::get(i64, -1));
    b.CreateRet(x2);

    ollvm::unfoldConstantsModule(*Mx, seed);
    EXPECT_EQ(countConstantIntOperands(*Fx), before)
        << "Trivial constants (0,1,-1) should not be unfolded (seed=" << seed
        << ")";
    EXPECT_FALSE(llvm::verifyModule(*Mx, &llvm::errs()));
  }
}

// --------------------------------------------------------------------------
// 4. Boolean (i1) constants should never be replaced.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, BoolSkipped) {
  auto M = createModule();
  auto *i1Ty = llvm::Type::getInt1Ty(Ctx);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i1Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "bool_fn", *M);
  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entryBB);
  // XOR with i1 true — should not be unfolded.
  auto *xored = builder.CreateXor(F->getArg(0),
                                   llvm::ConstantInt::getTrue(Ctx));
  auto *ext = builder.CreateZExt(xored, i64Ty);
  builder.CreateRet(ext);

  // Count i1 constant operands before.
  auto countI1Constants = [](llvm::Function &Fn) -> unsigned {
    unsigned n = 0;
    for (auto &BB : Fn)
      for (auto &I : BB)
        for (unsigned i = 0; i < I.getNumOperands(); ++i)
          if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(I.getOperand(i)))
            if (ci->getBitWidth() == 1)
              ++n;
    return n;
  };

  unsigned beforeI1 = countI1Constants(*F);

  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto Mx = createModule();
    auto *i1 = llvm::Type::getInt1Ty(Ctx);
    auto *i64 = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(i64, {i1}, false);
    auto *Fx = llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                      "bool_fn", *Mx);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", Fx);
    llvm::IRBuilder<> b(bb);
    auto *x = b.CreateXor(Fx->getArg(0), llvm::ConstantInt::getTrue(Ctx));
    auto *e = b.CreateZExt(x, i64);
    b.CreateRet(e);

    ollvm::unfoldConstantsModule(*Mx, seed);
    EXPECT_EQ(countI1Constants(*Fx), beforeI1)
        << "i1 constants should never be unfolded (seed=" << seed << ")";
    EXPECT_FALSE(llvm::verifyModule(*Mx, &llvm::errs()));
  }
}

// --------------------------------------------------------------------------
// 5. BinaryOperator constants get unfolded (at least some across many seeds).
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, BinaryOpUnfolded) {
  // The pass replaces ConstantInt operands with computed expressions that
  // themselves contain ConstantInts, so the raw count may not decrease.
  // Detect transformation by checking for volatile anchor loads.
  bool anyTransformed = false;
  for (uint32_t seed = 0; seed < 50 && !anyTransformed; ++seed) {
    auto M = createModule();
    createManyConstantsFunction(*M, "fn");
    auto *F = M->getFunction("fn");

    ollvm::unfoldConstantsModule(*M, seed);

    if (hasVolatileLoad(*F))
      anyTransformed = true;
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  }
  EXPECT_TRUE(anyTransformed)
      << "Across 50 seeds with 20 constants, at least one should be unfolded";
}

// --------------------------------------------------------------------------
// 6. ICmpInst constants can be unfolded.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, ICmpUnfolded) {
  bool anyTransformed = false;
  for (uint32_t seed = 0; seed < 50 && !anyTransformed; ++seed) {
    auto M = createModule();
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "icmp_fn", *M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);
    // Many icmp comparisons with diverse constants.
    llvm::Value *acc = F->getArg(0);
    for (int64_t c = 10; c <= 30; ++c) {
      auto *cmp = builder.CreateICmpEQ(acc,
                                        llvm::ConstantInt::get(i64Ty, c * 3));
      acc = builder.CreateSelect(cmp, llvm::ConstantInt::get(i64Ty, c), acc);
    }
    builder.CreateRet(acc);

    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    // Count ConstantInt operands in ICmpInst only.
    auto countICmpConsts = [](llvm::Function &Fn) {
      unsigned n = 0;
      for (auto &BB : Fn)
        for (auto &I : BB)
          if (llvm::isa<llvm::ICmpInst>(&I))
            for (unsigned i = 0; i < I.getNumOperands(); ++i)
              if (llvm::isa<llvm::ConstantInt>(I.getOperand(i)))
                ++n;
      return n;
    };

    unsigned before = countICmpConsts(*F);
    ollvm::unfoldConstantsModule(*M, seed);
    unsigned after = countICmpConsts(*F);

    if (after < before)
      anyTransformed = true;

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  }
  EXPECT_TRUE(anyTransformed)
      << "Across 50 seeds, at least one ICmp constant should be unfolded";
}

// --------------------------------------------------------------------------
// 7. StoreInst value operand can be unfolded.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, StoreValueUnfolded) {
  bool anyTransformed = false;
  for (uint32_t seed = 0; seed < 50 && !anyTransformed; ++seed) {
    auto M = createModule();
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *ptrTy = llvm::PointerType::getUnqual(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, {ptrTy}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "store_fn", *M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);
    // Many stores of non-trivial constants.
    for (int c = 2; c <= 21; ++c) {
      builder.CreateStore(llvm::ConstantInt::get(i32Ty, c * 11),
                          F->getArg(0));
    }
    builder.CreateRetVoid();
    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    auto countStoreConsts = [](llvm::Function &Fn) {
      unsigned n = 0;
      for (auto &BB : Fn)
        for (auto &I : BB)
          if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I))
            if (llvm::isa<llvm::ConstantInt>(SI->getValueOperand()))
              ++n;
      return n;
    };

    unsigned before = countStoreConsts(*F);
    ollvm::unfoldConstantsModule(*M, seed);
    unsigned after = countStoreConsts(*F);

    if (after < before)
      anyTransformed = true;

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  }
  EXPECT_TRUE(anyTransformed)
      << "Across 50 seeds, at least one store value constant should be unfolded";
}

// --------------------------------------------------------------------------
// 8. Store pointer operand is never replaced (only value operand idx==0).
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, StorePointerUntouched) {
  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *ptrTy = llvm::PointerType::getUnqual(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, {ptrTy}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "store_ptr_fn", *M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);
    builder.CreateStore(llvm::ConstantInt::get(i32Ty, 99), F->getArg(0));
    builder.CreateRetVoid();

    ollvm::unfoldConstantsModule(*M, seed);

    // The pointer operand (operand 1) of each store must still be the
    // original function argument, not a computed expression.
    for (auto &BB : *F) {
      for (auto &I : BB) {
        if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          // Skip stores to anchor globals (internal i64 GVs added by pass).
          if (llvm::isa<llvm::GlobalVariable>(SI->getPointerOperand()))
            continue;
          EXPECT_EQ(SI->getPointerOperand(), F->getArg(0))
              << "Store pointer operand must not be replaced (seed=" << seed
              << ")";
        }
      }
    }
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  }
}

// --------------------------------------------------------------------------
// 9. Constants in PHI nodes are never replaced.
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, PHIOperandsUntouched) {
  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     "phi_fn", *M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    auto *trueBB = llvm::BasicBlock::Create(Ctx, "if.true", F);
    auto *falseBB = llvm::BasicBlock::Create(Ctx, "if.false", F);
    auto *mergeBB = llvm::BasicBlock::Create(Ctx, "merge", F);

    llvm::IRBuilder<> entryB(entryBB);
    auto *cond = entryB.CreateICmpSGT(F->getArg(0),
                                       llvm::ConstantInt::get(i64Ty, 0));
    entryB.CreateCondBr(cond, trueBB, falseBB);

    llvm::IRBuilder<> trueB(trueBB);
    trueB.CreateBr(mergeBB);

    llvm::IRBuilder<> falseB(falseBB);
    falseB.CreateBr(mergeBB);

    llvm::IRBuilder<> mergeB(mergeBB);
    auto *phi = mergeB.CreatePHI(i64Ty, 2);
    phi->addIncoming(llvm::ConstantInt::get(i64Ty, 42), trueBB);
    phi->addIncoming(llvm::ConstantInt::get(i64Ty, 99), falseBB);
    mergeB.CreateRet(phi);

    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    ollvm::unfoldConstantsModule(*M, seed);

    // PHI incoming values must remain ConstantInt.
    for (auto &BB : *F) {
      for (auto &I : BB) {
        if (auto *PN = llvm::dyn_cast<llvm::PHINode>(&I)) {
          for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
            EXPECT_TRUE(llvm::isa<llvm::ConstantInt>(PN->getIncomingValue(i)))
                << "PHI constant must not be replaced (seed=" << seed
                << ", incoming=" << i << ")";
          }
        }
      }
    }
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  }
}

// --------------------------------------------------------------------------
// 10. Module verifies across many seeds (fuzz-style).
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, ModuleVerifiesMultipleSeeds) {
  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    createManyConstantsFunction(*M, "fn");

    ollvm::unfoldConstantsModule(*M, seed);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed with seed " << seed << ": " << errStr;
  }
}

// --------------------------------------------------------------------------
// 11. i128 constants are skipped (not crashed on).
// --------------------------------------------------------------------------
TEST_F(ConstantUnfoldingObfTest, WideIntegerConstantsSkipped) {
  auto M = createModule();
  auto *i128Ty = llvm::Type::getInt128Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i128Ty, {i128Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "wide_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entry);
  // i128 add with a large constant — must NOT trigger getSExtValue assert.
  auto *k = llvm::ConstantInt::get(i128Ty, 42);
  auto *result = builder.CreateAdd(F->getArg(0), k);
  builder.CreateRet(result);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Must not crash.
  for (uint32_t seed = 0; seed < 10; ++seed) {
    auto Mx = createModule();
    auto *Fx = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                      "wide_fn", *Mx);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", Fx);
    llvm::IRBuilder<> b(bb);
    b.CreateRet(b.CreateAdd(Fx->getArg(0), llvm::ConstantInt::get(i128Ty, 42)));

    ollvm::unfoldConstantsModule(*Mx, seed);

    // i128 constant should remain untouched — no volatile anchor loads.
    bool hasVolatile = false;
    for (auto &BB : *Mx->getFunction("wide_fn"))
      for (auto &I : BB)
        if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
          if (LI->isVolatile()) hasVolatile = true;
    EXPECT_FALSE(hasVolatile)
        << "i128 constants should be skipped, not unfolded (seed=" << seed << ")";
    EXPECT_FALSE(llvm::verifyModule(*Mx, &llvm::errs()));
  }
}

}  // namespace

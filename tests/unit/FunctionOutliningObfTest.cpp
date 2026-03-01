#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <cstdint>
#include <string>

#include "../../tools/ollvm-obf/FunctionOutlining.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class FunctionOutliningObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_outline", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function: entry → body → exit
  /// body has > 3 arithmetic instructions using entry's args, branches to exit.
  /// exit returns a value defined in body.
  llvm::Function *createOutlineableFunction(llvm::Module &M,
                                            const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg0 = F->getArg(0);
    auto *arg1 = F->getArg(1);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *bodyBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> entryBuilder(entryBB);
    entryBuilder.CreateBr(bodyBB);

    llvm::IRBuilder<> bodyBuilder(bodyBB);
    auto *sum = bodyBuilder.CreateAdd(arg0, arg1, "");
    auto *prod = bodyBuilder.CreateMul(sum, arg0, "");
    auto *diff = bodyBuilder.CreateSub(prod, arg1, "");
    auto *extra = bodyBuilder.CreateAdd(diff, arg0, "");
    (void)extra;
    bodyBuilder.CreateBr(exitBB);

    llvm::IRBuilder<> exitBuilder(exitBB);
    exitBuilder.CreateRet(diff);

    return F;
  }

  /// Create a function with many candidate blocks to increase outlining
  /// probability.
  llvm::Function *createMultiBlockFunction(llvm::Module &M,
                                           const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg0 = F->getArg(0);
    auto *arg1 = F->getArg(1);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> entryBuilder(entryBB);

    llvm::BasicBlock *prevBB = entryBB;
    llvm::Value *accum = arg0;

    // Create 10 blocks, each with > 3 instructions, single predecessor,
    // unconditional branch.
    for (int i = 0; i < 10; ++i) {
      auto *bb = llvm::BasicBlock::Create(Ctx, "", F);
      llvm::IRBuilder<>(prevBB).CreateBr(bb);

      llvm::IRBuilder<> builder(bb);
      auto *v1 = builder.CreateAdd(accum, arg1, "");
      auto *v2 = builder.CreateMul(v1, arg0, "");
      auto *v3 = builder.CreateSub(v2, arg1, "");
      accum = builder.CreateAdd(v3, arg0, "");
      prevBB = bb;
    }

    auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<>(prevBB).CreateBr(exitBB);
    llvm::IRBuilder<>(exitBB).CreateRet(accum);

    return F;
  }

  /// Create function with PHI nodes in a block.
  llvm::Function *createFunctionWithPHI(llvm::Module &M,
                                        const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg0 = F->getArg(0);
    auto *arg1 = F->getArg(1);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *leftBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *rightBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *mergeBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> entryBuilder(entryBB);
    auto *cmp = entryBuilder.CreateICmpSGT(arg0, arg1, "");
    entryBuilder.CreateCondBr(cmp, leftBB, rightBB);

    llvm::IRBuilder<> leftBuilder(leftBB);
    auto *lv = leftBuilder.CreateAdd(arg0, arg1, "");
    leftBuilder.CreateBr(mergeBB);

    llvm::IRBuilder<> rightBuilder(rightBB);
    auto *rv = rightBuilder.CreateSub(arg0, arg1, "");
    rightBuilder.CreateBr(mergeBB);

    // mergeBB has a PHI node — should not be outlined.
    llvm::IRBuilder<> mergeBuilder(mergeBB);
    auto *phi = mergeBuilder.CreatePHI(i64Ty, 2, "");
    phi->addIncoming(lv, leftBB);
    phi->addIncoming(rv, rightBB);
    auto *res = mergeBuilder.CreateAdd(phi, arg0, "");
    auto *res2 = mergeBuilder.CreateMul(res, arg1, "");
    auto *res3 = mergeBuilder.CreateSub(res2, arg0, "");
    (void)res3;
    mergeBuilder.CreateRet(res);

    return F;
  }

  /// Count internal (outlined) functions in the module.
  unsigned countInternalFunctions(llvm::Module &M) {
    unsigned count = 0;
    for (auto &F : M) {
      if (F.hasInternalLinkage() && !F.isDeclaration())
        ++count;
    }
    return count;
  }

  /// Check if any call instruction in F calls an internal function.
  bool hasCallToInternal(llvm::Function &F) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
          if (auto *callee = call->getCalledFunction()) {
            if (callee->hasInternalLinkage())
              return true;
          }
        }
      }
    }
    return false;
  }
};

// Force-outline by using 100% transform_percent and trying many seeds.
// The 30% coin means we may need several seeds.
static ollvm::FilterConfig forceCfg() {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  return cfg;
}

TEST_F(FunctionOutliningObfTest, BasicOutline) {
  // Try multiple seeds until we get an outline (30% chance per candidate).
  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M = createModule();
    createMultiBlockFunction(*M, "f");
    unsigned funcsBefore = 0;
    for (auto &F : *M) ++funcsBefore;

    ollvm::outlineFunctionsModule(*M, seed, forceCfg());

    unsigned funcsAfter = 0;
    for (auto &F : *M) ++funcsAfter;

    if (funcsAfter > funcsBefore) {
      // At least one function was outlined.
      EXPECT_GT(funcsAfter, funcsBefore);
      EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
      return;
    }
  }
  FAIL() << "No outline happened after 200 seeds";
}

TEST_F(FunctionOutliningObfTest, LiveInPassed) {
  // Verify that outlined function receives arguments (live-in values).
  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M = createModule();
    createOutlineableFunction(*M, "f");

    ollvm::outlineFunctionsModule(*M, seed, forceCfg());

    if (countInternalFunctions(*M) > 0) {
      // Find the outlined function and check it has arguments.
      for (auto &F : *M) {
        if (F.hasInternalLinkage() && !F.isDeclaration()) {
          EXPECT_GT(F.arg_size(), 0u)
              << "Outlined function must have live-in arguments";
          EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
          return;
        }
      }
    }
  }
  FAIL() << "No outline happened after 200 seeds";
}

TEST_F(FunctionOutliningObfTest, LiveOutReturned) {
  // The outlined function from createOutlineableFunction should return
  // a value (diff is used in exit block).
  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M = createModule();
    createOutlineableFunction(*M, "f");

    ollvm::outlineFunctionsModule(*M, seed, forceCfg());

    if (countInternalFunctions(*M) > 0) {
      for (auto &F : *M) {
        if (F.hasInternalLinkage() && !F.isDeclaration()) {
          EXPECT_FALSE(F.getReturnType()->isVoidTy())
              << "Outlined function should return live-out value";
          EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
          return;
        }
      }
    }
  }
  FAIL() << "No outline happened after 200 seeds";
}

TEST_F(FunctionOutliningObfTest, MultipleLiveOuts) {
  // Create a function where a body block defines 2 values used in exit.
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "f", *M);
  auto *arg0 = F->getArg(0);
  auto *arg1 = F->getArg(1);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
  auto *bodyBB = llvm::BasicBlock::Create(Ctx, "", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

  llvm::IRBuilder<> entryBuilder(entryBB);
  entryBuilder.CreateBr(bodyBB);

  // Body: define two values used in exit.
  llvm::IRBuilder<> bodyBuilder(bodyBB);
  auto *sum = bodyBuilder.CreateAdd(arg0, arg1, "");
  auto *prod = bodyBuilder.CreateMul(arg0, arg1, "");
  auto *extra1 = bodyBuilder.CreateSub(sum, arg1, "");
  auto *extra2 = bodyBuilder.CreateAdd(prod, arg0, "");
  (void)extra1;
  (void)extra2;
  bodyBuilder.CreateBr(exitBB);

  // Exit uses both sum and prod.
  llvm::IRBuilder<> exitBuilder(exitBB);
  auto *res = exitBuilder.CreateAdd(sum, prod, "");
  exitBuilder.CreateRet(res);

  for (uint32_t seed = 0; seed < 200; ++seed) {
    // Clone module for each attempt (cheap for small modules).
    auto M2 = llvm::CloneModule(*M);
    ollvm::outlineFunctionsModule(*M2, seed, forceCfg());

    for (auto &Fn : *M2) {
      if (Fn.hasInternalLinkage() && !Fn.isDeclaration()) {
        // Return type should be a struct (2 live-outs).
        EXPECT_TRUE(Fn.getReturnType()->isStructTy())
            << "Multiple live-outs should produce struct return";
        EXPECT_FALSE(llvm::verifyModule(*M2, &llvm::errs()));
        return;
      }
    }
  }
  FAIL() << "No outline happened after 200 seeds";
}

TEST_F(FunctionOutliningObfTest, SkipsEntry) {
  // A function with only an entry block: nothing should be outlined.
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "f", *M);
  auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
  llvm::IRBuilder<> builder(entryBB);
  auto *v1 = builder.CreateAdd(F->getArg(0), F->getArg(0), "");
  auto *v2 = builder.CreateMul(v1, F->getArg(0), "");
  auto *v3 = builder.CreateSub(v2, v1, "");
  auto *v4 = builder.CreateAdd(v3, v2, "");
  builder.CreateRet(v4);

  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M2 = llvm::CloneModule(*M);
    ollvm::outlineFunctionsModule(*M2, seed, forceCfg());
    EXPECT_EQ(countInternalFunctions(*M2), 0u)
        << "Entry-only function should not be outlined";
  }
}

TEST_F(FunctionOutliningObfTest, ModuleVerifies) {
  // Verify module integrity across multiple seeds.
  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    createMultiBlockFunction(*M, "f1");
    createMultiBlockFunction(*M, "f2");
    createOutlineableFunction(*M, "f3");

    ollvm::outlineFunctionsModule(*M, seed, forceCfg());

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Module verification failed for seed " << seed;
  }
}

TEST_F(FunctionOutliningObfTest, SkipsPHIBlocks) {
  // Blocks with PHI nodes must not be outlined.
  auto M = createModule();
  createFunctionWithPHI(*M, "f");

  // mergeBB has a PHI — it should be skipped. leftBB and rightBB each
  // have only 2 instructions (add/sub + branch), so they're too small.
  // No outlining should occur.
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M2 = llvm::CloneModule(*M);
    ollvm::outlineFunctionsModule(*M2, seed, forceCfg());
    EXPECT_EQ(countInternalFunctions(*M2), 0u)
        << "Blocks with PHI nodes should not be outlined";
  }
}

TEST_F(FunctionOutliningObfTest, OutlinedHasInternalLinkage) {
  // Verify that all outlined functions have internal linkage.
  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M = createModule();
    createMultiBlockFunction(*M, "f");

    ollvm::outlineFunctionsModule(*M, seed, forceCfg());

    bool found = false;
    for (auto &F : *M) {
      if (&F != M->getFunction("f") && !F.isDeclaration()) {
        EXPECT_TRUE(F.hasInternalLinkage());
        found = true;
      }
    }
    if (found) {
      EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
      return;
    }
  }
  FAIL() << "No outline happened after 200 seeds";
}


/// Outlining a block with mixed-type operands (ptr, i32, i64) must verify.
TEST_F(FunctionOutliningObfTest, MixedTypeOperandsVerify) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::getUnqual(Ctx);
  auto *fnTy = llvm::FunctionType::get(
      i64Ty, {ptrTy, i32Ty, i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "mixed", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  auto *body = llvm::BasicBlock::Create(Ctx, "", F);
  auto *exit = llvm::BasicBlock::Create(Ctx, "", F);

  llvm::IRBuilder<> eB(entry);
  eB.CreateBr(body);

  llvm::IRBuilder<> bB(body);
  auto *loaded = bB.CreateLoad(i64Ty, F->getArg(0), "");
  auto *ext = bB.CreateZExt(F->getArg(1), i64Ty, "");
  auto *sum = bB.CreateAdd(loaded, ext, "");
  auto *product = bB.CreateMul(sum, F->getArg(2), "");
  bB.CreateBr(exit);

  llvm::IRBuilder<> xB(exit);
  xB.CreateRet(product);

  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M2 = llvm::CloneModule(*M);
    ollvm::outlineFunctionsModule(*M2, seed, forceCfg());
    std::string err;
    llvm::raw_string_ostream os(err);
    EXPECT_FALSE(llvm::verifyModule(*M2, &os))
        << "Verification failed for seed " << seed << ": " << os.str();
  }
}

/// No instruction in the outlined function should reference the original.
TEST_F(FunctionOutliningObfTest, NoCrossFunctionRefs) {
  for (uint32_t seed = 0; seed < 200; ++seed) {
    auto M = createModule();
    createMultiBlockFunction(*M, "f");
    ollvm::outlineFunctionsModule(*M, seed, forceCfg());

    for (auto &F : *M) {
      if (!F.hasInternalLinkage() || F.isDeclaration())
        continue;
      // Every operand of every instruction in F must belong to F.
      for (auto &BB : F) {
        for (auto &I : BB) {
          for (auto &Op : I.operands()) {
            if (auto *inst = llvm::dyn_cast<llvm::Instruction>(Op.get())) {
              EXPECT_EQ(inst->getFunction(), &F)
                  << "Cross-function ref in outlined fn at seed " << seed;
            }
          }
        }
      }
      return;  // Found and checked one.
    }
  }
}
}  // namespace

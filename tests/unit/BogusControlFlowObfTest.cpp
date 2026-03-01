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
#include "../../tools/ollvm-obf/BogusControlFlow.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class BogusControlFlowObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_bcf", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a multi-block function: entry → body → exit, with arithmetic in
  /// body so BCF has something to clone.
  llvm::Function *createMultiBlockFunction(llvm::Module &M,
                                           const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg0 = F->getArg(0);
    auto *arg1 = F->getArg(1);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    auto *bodyBB = llvm::BasicBlock::Create(Ctx, "body", F);
    auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

    // entry: branch to body
    llvm::IRBuilder<> entryBuilder(entryBB);
    entryBuilder.CreateBr(bodyBB);

    // body: some arithmetic, then branch to exit
    llvm::IRBuilder<> bodyBuilder(bodyBB);
    auto *sum = bodyBuilder.CreateAdd(arg0, arg1, "sum");
    auto *prod = bodyBuilder.CreateMul(sum, arg0, "prod");
    auto *diff = bodyBuilder.CreateSub(prod, arg1, "diff");
    bodyBuilder.CreateBr(exitBB);

    // exit: return
    llvm::IRBuilder<> exitBuilder(exitBB);
    exitBuilder.CreateRet(diff);

    return F;
  }

  /// Create a function with a single block (entry only).
  llvm::Function *createSingleBlockFunction(llvm::Module &M,
                                            const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);
    builder.CreateRet(F->getArg(0));
    return F;
  }

  /// Create a function with many blocks so BCF is very likely to select some
  /// even at 30% rate.
  llvm::Function *createManyBlockFunction(llvm::Module &M,
                                          const std::string &name,
                                          unsigned numBlocks) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg = F->getArg(0);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::Value *val = arg;

    auto *prevBB = entryBB;
    for (unsigned i = 0; i < numBlocks; ++i) {
      auto *bb = llvm::BasicBlock::Create(
          Ctx, "block_" + std::to_string(i), F);
      llvm::IRBuilder<>(prevBB).CreateBr(bb);
      llvm::IRBuilder<> builder(bb);
      val = builder.CreateAdd(val, llvm::ConstantInt::get(i64Ty, i + 1),
                              "add_" + std::to_string(i));
      val = builder.CreateMul(val, llvm::ConstantInt::get(i64Ty, 2),
                              "mul_" + std::to_string(i));
      prevBB = bb;
    }

    auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);
    llvm::IRBuilder<>(prevBB).CreateBr(exitBB);
    llvm::IRBuilder<>(exitBB).CreateRet(val);

    return F;
  }

  unsigned countBlocks(llvm::Function &F) {
    return static_cast<unsigned>(F.size());
  }

  /// Serialize the function to a string for comparison.
  std::string serializeFunction(llvm::Function &F) {
    std::string str;
    llvm::raw_string_ostream os(str);
    F.print(os);
    return str;
  }
};

TEST_F(BogusControlFlowObfTest, InsertsClonedBlocks) {
  auto M = createModule();
  // Use many blocks to ensure BCF triggers despite 30% selection rate.
  createManyBlockFunction(*M, "test_fn", 20);
  auto *F = M->getFunction("test_fn");
  unsigned blocksBefore = countBlocks(*F);

  // Use a seed known to select at least some blocks.
  ollvm::insertBogusControlFlowModule(*M, 42);

  unsigned blocksAfter = countBlocks(*F);
  // Each selected block adds 2 blocks (dispatch + bogus clone).
  EXPECT_GT(blocksAfter, blocksBefore)
      << "BCF should insert additional blocks";
}

TEST_F(BogusControlFlowObfTest, OpaqueBranchHasMBAPredicate) {
  auto M = createModule();
  createManyBlockFunction(*M, "test_fn", 20);
  ollvm::insertBogusControlFlowModule(*M, 42);

  auto *F = M->getFunction("test_fn");
  // After BCF, dispatch blocks contain MBA-based opaque predicates:
  // a conditional branch whose condition is an ICmpInst.  The predicate
  // and polarity vary (eq/sle/uge/slt/ne/sgt/ugt for anti-fingerprinting).
  // The original function had only unconditional branches, so any
  // conditional branch is BCF-injected.
  bool foundMBACondBranch = false;
  for (auto &BB : *F) {
    auto *BI = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
    if (!BI || !BI->isConditional())
      continue;
    auto *ICmp = llvm::dyn_cast<llvm::ICmpInst>(BI->getCondition());
    if (!ICmp)
      continue;
    // Any ICmpInst-based conditional branch is a BCF opaque predicate.
    foundMBACondBranch = true;
    break;
  }
  EXPECT_TRUE(foundMBACondBranch)
      << "Should find at least one conditional branch with an ICmpInst condition";
}

TEST_F(BogusControlFlowObfTest, SkipsEntryBlock) {
  auto M = createModule();
  createMultiBlockFunction(*M, "test_fn");
  auto *F = M->getFunction("test_fn");

  // Record entry block name before pass.
  auto *entryBB = &F->getEntryBlock();
  std::string entryName = entryBB->getName().str();

  ollvm::insertBogusControlFlowModule(*M, 100);

  // Entry block should still be the entry (no dispatch block inserted before
  // it redirecting away from entry).
  auto *newEntry = &F->getEntryBlock();
  // The entry block itself was never cloned — it should still be the first
  // block with the same name.
  EXPECT_EQ(newEntry->getName().str(), entryName)
      << "Entry block should remain the function entry";
}

TEST_F(BogusControlFlowObfTest, ModuleVerifies) {
  auto M = createModule();
  createManyBlockFunction(*M, "test_fn", 20);

  ollvm::insertBogusControlFlowModule(*M, 42);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed after BCF: " << errStr;
}

TEST_F(BogusControlFlowObfTest, DeterministicWithSeed) {
  // Run twice with the same seed, compare IR output.
  auto M1 = createModule();
  createManyBlockFunction(*M1, "test_fn", 20);
  ollvm::insertBogusControlFlowModule(*M1, 12345);
  auto ir1 = serializeFunction(*M1->getFunction("test_fn"));

  auto M2 = createModule();
  createManyBlockFunction(*M2, "test_fn", 20);
  ollvm::insertBogusControlFlowModule(*M2, 12345);
  auto ir2 = serializeFunction(*M2->getFunction("test_fn"));

  EXPECT_EQ(ir1, ir2)
      << "Same seed should produce identical BCF output";

  // Different seed should produce different output.
  auto M3 = createModule();
  createManyBlockFunction(*M3, "test_fn", 20);
  ollvm::insertBogusControlFlowModule(*M3, 99999);
  auto ir3 = serializeFunction(*M3->getFunction("test_fn"));

  EXPECT_NE(ir1, ir3)
      << "Different seeds should produce different BCF output";
}

TEST_F(BogusControlFlowObfTest, SkipsSmallFunctions) {
  auto M = createModule();
  createSingleBlockFunction(*M, "small_fn");
  auto *F = M->getFunction("small_fn");
  unsigned blocksBefore = countBlocks(*F);

  ollvm::insertBogusControlFlowModule(*M, 42);

  unsigned blocksAfter = countBlocks(*F);
  EXPECT_EQ(blocksAfter, blocksBefore)
      << "Single-block functions should be unchanged";
}

TEST_F(BogusControlFlowObfTest, SkipsBlocksWithPHI) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "phi_fn", *M);
  auto *arg = F->getArg(0);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *leftBB = llvm::BasicBlock::Create(Ctx, "left", F);
  auto *rightBB = llvm::BasicBlock::Create(Ctx, "right", F);
  auto *mergeBB = llvm::BasicBlock::Create(Ctx, "merge", F);

  // entry: conditional branch
  llvm::IRBuilder<> entryBuilder(entryBB);
  auto *cond = entryBuilder.CreateICmpSGT(
      arg, llvm::ConstantInt::get(i64Ty, 0), "cond");
  entryBuilder.CreateCondBr(cond, leftBB, rightBB);

  // left: compute and branch to merge
  llvm::IRBuilder<> leftBuilder(leftBB);
  auto *leftVal = leftBuilder.CreateAdd(arg, llvm::ConstantInt::get(i64Ty, 1));
  leftBuilder.CreateBr(mergeBB);

  // right: compute and branch to merge
  llvm::IRBuilder<> rightBuilder(rightBB);
  auto *rightVal =
      rightBuilder.CreateSub(arg, llvm::ConstantInt::get(i64Ty, 1));
  rightBuilder.CreateBr(mergeBB);

  // merge: PHI node
  llvm::IRBuilder<> mergeBuilder(mergeBB);
  auto *phi = mergeBuilder.CreatePHI(i64Ty, 2, "result");
  phi->addIncoming(leftVal, leftBB);
  phi->addIncoming(rightVal, rightBB);
  mergeBuilder.CreateRet(phi);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  unsigned blocksBefore = countBlocks(*F);
  // Use seed 0 — deterministic; merge block has PHI so should be skipped.
  // left/right are 2-instruction blocks (compute + br), eligible.
  // With 30% selection at seed 0 they might or might not be selected, but
  // the merge block must never be cloned.
  ollvm::insertBogusControlFlowModule(*M, 0);

  // Verify no bogus clone of the merge block exists.
  for (auto &BB : *F) {
    if (BB.getName().contains("merge") && BB.getName().contains("bogus")) {
      FAIL() << "Merge block with PHI node should not be cloned";
    }
  }

  // Module should still verify.
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(BogusControlFlowObfTest, JunkBlocksReferenceFunctionArgs) {
  auto M = createModule();
  createManyBlockFunction(*M, "test_fn", 20);
  auto *F = M->getFunction("test_fn");
  unsigned blocksBefore = countBlocks(*F);

  ollvm::insertBogusControlFlowModule(*M, 42);

  unsigned blocksAfter = countBlocks(*F);
  ASSERT_GT(blocksAfter, blocksBefore) << "BCF must insert junk blocks";

  // Junk blocks are new blocks not in the original set. They should contain
  // instructions that use function arguments (the i64 arg).
  auto *arg0 = F->getArg(0);
  bool foundArgUseInJunk = false;
  for (auto &BB : *F) {
    // Skip named blocks (original blocks have names; junk blocks have empty names).
    if (!BB.getName().empty())
      continue;
    for (auto &I : BB) {
      for (unsigned i = 0, e = I.getNumOperands(); i < e; ++i) {
        // Check if operand is a zext/trunc of arg0, or arg0 directly.
        if (I.getOperand(i) == arg0) {
          foundArgUseInJunk = true;
          break;
        }
        // The arg gets ZExtOrTrunc'd to i64 — check if operand is a cast of arg.
        if (auto *cast = llvm::dyn_cast<llvm::CastInst>(I.getOperand(i))) {
          if (cast->getOperand(0) == arg0) {
            foundArgUseInJunk = true;
            break;
          }
        }
      }
      if (foundArgUseInJunk) break;
    }
    if (foundArgUseInJunk) break;
  }
  EXPECT_TRUE(foundArgUseInJunk)
      << "Junk blocks should reference real function arguments";
}

TEST_F(BogusControlFlowObfTest, JunkBlocksHaveSinkAlloca) {
  auto M = createModule();
  createManyBlockFunction(*M, "test_fn", 20);
  auto *F = M->getFunction("test_fn");

  ollvm::insertBogusControlFlowModule(*M, 42);

  // The entry block should contain an alloca for the sink.
  auto &entryBB = F->getEntryBlock();
  llvm::AllocaInst *sinkAlloca = nullptr;
  for (auto &I : entryBB) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (AI->getAllocatedType()->isIntegerTy(64)) {
        sinkAlloca = AI;
        break;
      }
    }
  }
  ASSERT_NE(sinkAlloca, nullptr)
      << "Should find an i64 sink alloca in the entry block";

  // Junk blocks should both load from and store to the sink alloca.
  bool foundLoad = false;
  bool foundStore = false;
  for (auto &BB : *F) {
    if (!BB.getName().empty()) continue;
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        if (LI->getPointerOperand() == sinkAlloca)
          foundLoad = true;
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (SI->getPointerOperand() == sinkAlloca)
          foundStore = true;
      }
    }
  }
  EXPECT_TRUE(foundLoad) << "Junk blocks should load from sink alloca";
  EXPECT_TRUE(foundStore) << "Junk blocks should store to sink alloca";
}

TEST_F(BogusControlFlowObfTest, JunkBlocksHaveMultipleArithOps) {
  auto M = createModule();
  createManyBlockFunction(*M, "test_fn", 20);
  auto *F = M->getFunction("test_fn");

  ollvm::insertBogusControlFlowModule(*M, 42);

  // Each junk block should have at least 3 binary arithmetic operations.
  for (auto &BB : *F) {
    if (!BB.getName().empty()) continue;
    unsigned arithCount = 0;
    for (auto &I : BB) {
      if (llvm::isa<llvm::BinaryOperator>(&I))
        ++arithCount;
    }
    // Each junk block should have 3-6 arithmetic ops (per createJunkBlock).
    EXPECT_GE(arithCount, 3u)
        << "Junk block should have at least 3 arithmetic operations";
    EXPECT_LE(arithCount, 6u)
        << "Junk block should have at most 6 arithmetic operations";
  }
}

TEST_F(BogusControlFlowObfTest, JunkBlocksVerifyWithPointerArgs) {
  // Test with a function that has pointer arguments (PtrToInt path).
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {ptrTy, ptrTy}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "ptr_fn", *M);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> entryBuilder(entryBB);
  auto *val = entryBuilder.CreatePtrToInt(F->getArg(0), i64Ty);

  // Create several blocks so BCF has targets.
  auto *prevBB = entryBB;
  llvm::Value *acc = val;
  for (unsigned i = 0; i < 15; ++i) {
    auto *bb = llvm::BasicBlock::Create(Ctx, "b" + std::to_string(i), F);
    llvm::IRBuilder<>(prevBB).CreateBr(bb);
    llvm::IRBuilder<> b(bb);
    acc = b.CreateAdd(acc, llvm::ConstantInt::get(i64Ty, i + 1));
    acc = b.CreateXor(acc, llvm::ConstantInt::get(i64Ty, 0xAB));
    prevBB = bb;
  }
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);
  llvm::IRBuilder<>(prevBB).CreateBr(exitBB);
  llvm::IRBuilder<>(exitBB).CreateRet(acc);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::insertBogusControlFlowModule(*M, 77);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module with pointer-arg function should verify after BCF: " << errStr;
}

}  // namespace

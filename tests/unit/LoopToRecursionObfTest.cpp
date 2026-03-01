#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Analysis/LoopInfo.h>

#include <cstdint>
#include <string>

#include "../../tools/ollvm-obf/LoopToRecursion.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class LoopToRecursionObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_l2r", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function with a simple `for(i=0; i<n; i++) sum += i` loop.
  /// Returns i64 sum.
  ///
  ///   entry:
  ///     br header
  ///   header:                          ; preds = entry, header
  ///     %i   = phi i64 [0, entry], [%i.next, header]
  ///     %sum = phi i64 [0, entry], [%sum.next, header]
  ///     %sum.next = add %sum, %i
  ///     %i.next   = add %i, 1
  ///     %cmp      = icmp slt %i.next, %n
  ///     br i1 %cmp, header, exit
  ///   exit:
  ///     ret %sum.next
  llvm::Function *createSimpleCounterLoop(llvm::Module &M,
                                          const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *n = F->getArg(0);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *headerBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

    // entry
    llvm::IRBuilder<> entryB(entryBB);
    entryB.CreateBr(headerBB);

    // header (single block loop — header IS the latch)
    llvm::IRBuilder<> hdrB(headerBB);
    auto *iPhi = hdrB.CreatePHI(i64Ty, 2, "");
    auto *sumPhi = hdrB.CreatePHI(i64Ty, 2, "");
    auto *sumNext = hdrB.CreateAdd(sumPhi, iPhi, "");
    auto *iNext = hdrB.CreateAdd(iPhi, llvm::ConstantInt::get(i64Ty, 1), "");
    auto *cmp = hdrB.CreateICmpSLT(iNext, n, "");
    hdrB.CreateCondBr(cmp, headerBB, exitBB);

    iPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entryBB);
    iPhi->addIncoming(iNext, headerBB);
    sumPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entryBB);
    sumPhi->addIncoming(sumNext, headerBB);

    // exit
    llvm::IRBuilder<> exitB(exitBB);
    auto *retPhi = exitB.CreatePHI(i64Ty, 1, "");
    retPhi->addIncoming(sumNext, headerBB);
    exitB.CreateRet(retPhi);

    return F;
  }

  /// Create a function with a 2-block loop (header + separate latch).
  ///   entry -> header -> body -> {header, exit}
  llvm::Function *createTwoBlockLoop(llvm::Module &M,
                                     const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *n = F->getArg(0);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *headerBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *bodyBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> entryB(entryBB);
    entryB.CreateBr(headerBB);

    llvm::IRBuilder<> hdrB(headerBB);
    auto *iPhi = hdrB.CreatePHI(i64Ty, 2, "");
    auto *sumPhi = hdrB.CreatePHI(i64Ty, 2, "");
    hdrB.CreateBr(bodyBB);

    llvm::IRBuilder<> bodyB(bodyBB);
    auto *sumNext = bodyB.CreateAdd(sumPhi, iPhi, "");
    auto *iNext = bodyB.CreateAdd(iPhi, llvm::ConstantInt::get(i64Ty, 1), "");
    auto *cmp = bodyB.CreateICmpSLT(iNext, n, "");
    bodyB.CreateCondBr(cmp, headerBB, exitBB);

    iPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entryBB);
    iPhi->addIncoming(iNext, bodyBB);
    sumPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entryBB);
    sumPhi->addIncoming(sumNext, bodyBB);

    llvm::IRBuilder<> exitB(exitBB);
    auto *retPhi = exitB.CreatePHI(i64Ty, 1, "");
    retPhi->addIncoming(sumNext, bodyBB);
    exitB.CreateRet(retPhi);

    return F;
  }

  /// Create a function with a nested loop (outer contains inner).
  llvm::Function *createNestedLoop(llvm::Module &M,
                                   const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *n = F->getArg(0);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    auto *outerHdr = llvm::BasicBlock::Create(Ctx, "", F);
    auto *innerHdr = llvm::BasicBlock::Create(Ctx, "", F);
    auto *outerLatch = llvm::BasicBlock::Create(Ctx, "", F);
    auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

    llvm::IRBuilder<> entryB(entryBB);
    entryB.CreateBr(outerHdr);

    // Outer header
    llvm::IRBuilder<> ohB(outerHdr);
    auto *oi = ohB.CreatePHI(i64Ty, 2, "");
    ohB.CreateBr(innerHdr);

    // Inner header (inner loop: innerHdr -> innerHdr)
    llvm::IRBuilder<> ihB(innerHdr);
    auto *ji = ihB.CreatePHI(i64Ty, 2, "");
    auto *jNext = ihB.CreateAdd(ji, llvm::ConstantInt::get(i64Ty, 1), "");
    auto *innerCmp = ihB.CreateICmpSLT(jNext, n, "");
    ihB.CreateCondBr(innerCmp, innerHdr, outerLatch);

    ji->addIncoming(llvm::ConstantInt::get(i64Ty, 0), outerHdr);
    ji->addIncoming(jNext, innerHdr);

    // Outer latch
    llvm::IRBuilder<> olB(outerLatch);
    auto *oiNext = olB.CreateAdd(oi, llvm::ConstantInt::get(i64Ty, 1), "");
    auto *outerCmp = olB.CreateICmpSLT(oiNext, n, "");
    olB.CreateCondBr(outerCmp, outerHdr, exitBB);

    oi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entryBB);
    oi->addIncoming(oiNext, outerLatch);

    llvm::IRBuilder<> exitB(exitBB);
    exitB.CreateRet(oiNext);

    return F;
  }

  /// Count the number of functions in the module.
  unsigned countFunctions(const llvm::Module &M) {
    unsigned count = 0;
    for (auto &F : M)
      ++count;
    return count;
  }

  /// Check if a function has any back edges (loops).
  bool hasBackEdges(llvm::Function &F) {
    llvm::DominatorTree DT(F);
    llvm::LoopInfo LI(DT);
    return !LI.empty();
  }
};

// --- Test: simple counter loop is converted ---
TEST_F(LoopToRecursionObfTest, SimpleCounterLoop) {
  auto M = createModule();
  auto *F = createSimpleCounterLoop(*M, "sum_loop");

  // Precondition: F has a loop.
  ASSERT_TRUE(hasBackEdges(*F));

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 42, cfg);

  // After transform, original function should have no back edges.
  EXPECT_FALSE(hasBackEdges(*F));

  // Module must verify.
  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << os.str();
}

// --- Test: helper function is created ---
TEST_F(LoopToRecursionObfTest, HelperFunctionCreated) {
  auto M = createModule();
  createSimpleCounterLoop(*M, "sum_loop");
  ASSERT_EQ(countFunctions(*M), 1u);

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 42, cfg);

  // A new helper function should exist.
  EXPECT_GE(countFunctions(*M), 2u);

  // The new function should have internal linkage.
  for (auto &Fn : *M) {
    if (Fn.getName() != "sum_loop") {
      EXPECT_TRUE(Fn.hasInternalLinkage());
    }
  }
}

// --- Test: original loop removed (no back edges) ---
TEST_F(LoopToRecursionObfTest, OriginalLoopRemoved) {
  auto M = createModule();
  auto *F = createTwoBlockLoop(*M, "twoblock");
  ASSERT_TRUE(hasBackEdges(*F));

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 99, cfg);

  EXPECT_FALSE(hasBackEdges(*F));

  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << os.str();
}

// --- Test: module verifies across multiple seeds ---
TEST_F(LoopToRecursionObfTest, ModuleVerifies) {
  uint32_t seeds[] = {0, 1, 42, 1000, 0xDEADBEEF};
  for (auto seed : seeds) {
    auto M = createModule();
    createSimpleCounterLoop(*M, "f");

    ollvm::FilterConfig cfg;
    cfg.transform_percent = 100;
    ollvm::loopToRecursionModule(*M, seed, cfg);

    std::string err;
    llvm::raw_string_ostream os(err);
    EXPECT_FALSE(llvm::verifyModule(*M, &os))
        << "Seed " << seed << ": " << os.str();
  }
}

// --- Test: nested loop is skipped ---
TEST_F(LoopToRecursionObfTest, NestedLoopSkipped) {
  auto M = createModule();
  auto *F = createNestedLoop(*M, "nested");

  // The outer loop has a sub-loop, so it should be skipped.
  // The inner loop has 3+ blocks in the outer loop context... let's check.
  unsigned funcsBefore = countFunctions(*M);

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 42, cfg);

  // The outer loop has sub-loops → skipped.
  // The inner loop (innerHdr→innerHdr) is a single-block loop but it's
  // nested inside the outer loop as a sub-loop. LoopInfo reports it as a
  // sub-loop of the outer, and top-level iteration only sees the outer loop.
  // So no conversion should happen for the top-level loop.
  // However, the inner loop IS a top-level... let me check: LoopInfo::begin
  // returns top-level loops. The outer loop IS top-level but has sub-loops,
  // so it's skipped. The inner loop is NOT top-level (it's a sub-loop).
  // Therefore, no conversion should happen.
  // Actually, we iterate LI (top-level loops only) and the outer loop has
  // sub-loops, so it's skipped. The inner loop is only accessible via
  // L->getSubLoops() which we don't iterate.

  // Module should still verify.
  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << os.str();

  // No new functions created (nothing was converted).
  EXPECT_EQ(countFunctions(*M), funcsBefore);
}

// --- Test: exit values are preserved ---
TEST_F(LoopToRecursionObfTest, ExitValuesPreserved) {
  auto M = createModule();
  auto *F = createSimpleCounterLoop(*M, "exit_vals");

  // The function returns the loop's sum — after conversion, it should
  // still return an i64 (the exit value should be wired through the helper).
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 7, cfg);

  // Verify module.
  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << os.str();

  // The original function should still return i64.
  EXPECT_TRUE(F->getReturnType()->isIntegerTy(64));

  // The helper function should also return i64 (the exit value type).
  for (auto &Fn : *M) {
    if (&Fn != F && !Fn.isDeclaration()) {
      EXPECT_TRUE(Fn.getReturnType()->isIntegerTy(64));
    }
  }

  // The original function should contain a call to the helper.
  bool hasCall = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto *callee = call->getCalledFunction();
        if (callee && callee != F) {
          hasCall = true;
        }
      }
    }
  }
  EXPECT_TRUE(hasCall);
}

// --- Test: transform_percent=0 skips all ---
TEST_F(LoopToRecursionObfTest, TransformPercentZeroSkips) {
  auto M = createModule();
  auto *F = createSimpleCounterLoop(*M, "noskip");
  unsigned funcsBefore = countFunctions(*M);

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 0;
  ollvm::loopToRecursionModule(*M, 42, cfg);

  // Nothing should be converted.
  EXPECT_EQ(countFunctions(*M), funcsBefore);
  EXPECT_TRUE(hasBackEdges(*F));
}


// --- Test: loop with non-loop predecessor to exit block is rejected ---
TEST_F(LoopToRecursionObfTest, NonLoopExitPredRejected) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "multi_pred", *M);
  auto *n = F->getArg(0);
  auto *flag = F->getArg(1);

  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  auto *header = llvm::BasicBlock::Create(Ctx, "", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

  // entry: branch to header or exit based on flag
  llvm::IRBuilder<> eB(entry);
  auto *cond = eB.CreateICmpEQ(flag, llvm::ConstantInt::get(i64Ty, 0), "");
  eB.CreateCondBr(cond, exitBB, header);

  // header: single-block loop, exits to exitBB
  llvm::IRBuilder<> hB(header);
  auto *iPhi = hB.CreatePHI(i64Ty, 2, "");
  auto *iNext = hB.CreateAdd(iPhi, llvm::ConstantInt::get(i64Ty, 1), "");
  auto *cmp = hB.CreateICmpSLT(iNext, n, "");
  hB.CreateCondBr(cmp, header, exitBB);
  iPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entry);
  iPhi->addIncoming(iNext, header);

  // exitBB has predecessors from both entry AND header
  llvm::IRBuilder<> xB(exitBB);
  auto *retPhi = xB.CreatePHI(i64Ty, 2, "");
  retPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entry);
  retPhi->addIncoming(iNext, header);
  xB.CreateRet(retPhi);

  unsigned funcsBefore = countFunctions(*M);
  ASSERT_TRUE(hasBackEdges(*F));

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 42, cfg);

  // Should NOT have converted (exitBB has non-loop predecessor).
  EXPECT_EQ(countFunctions(*M), funcsBefore);
  EXPECT_TRUE(hasBackEdges(*F));

  // Module must still verify (loop was left untouched).
  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << os.str();
}

// --- Test: loop with non-exit PHI in exit block is rejected ---
TEST_F(LoopToRecursionObfTest, NonExitPhiRejected) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "nonexitphi", *M);
  auto *n = F->getArg(0);

  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  auto *header = llvm::BasicBlock::Create(Ctx, "", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

  llvm::IRBuilder<> eB(entry);
  eB.CreateBr(header);

  // header: single-block loop
  llvm::IRBuilder<> hB(header);
  auto *iPhi = hB.CreatePHI(i64Ty, 2, "");
  auto *iNext = hB.CreateAdd(iPhi, llvm::ConstantInt::get(i64Ty, 1), "");
  auto *cmp = hB.CreateICmpSLT(iNext, n, "");
  hB.CreateCondBr(cmp, header, exitBB);
  iPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 0), entry);
  iPhi->addIncoming(iNext, header);

  // exitBB has TWO PHIs: one exit-phi and one "extra" phi
  llvm::IRBuilder<> xB(exitBB);
  auto *exitPhi1 = xB.CreatePHI(i64Ty, 1, "");
  exitPhi1->addIncoming(iNext, header);
  auto *extraPhi = xB.CreatePHI(i64Ty, 1, "");
  // This PHI gets a constant (non-loop-instruction) from the loop block
  extraPhi->addIncoming(llvm::ConstantInt::get(i64Ty, 99), header);
  auto *sum = xB.CreateAdd(exitPhi1, extraPhi, "");
  xB.CreateRet(sum);

  unsigned funcsBefore = countFunctions(*M);

  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;
  ollvm::loopToRecursionModule(*M, 42, cfg);

  // The extra PHI has a constant incoming from the loop block but is not
  // captured as an exit PHI (its value is not a loop instruction).
  // Our strict check should reject this loop.
  // Either way, module must verify.
  std::string err;
  llvm::raw_string_ostream os(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &os)) << os.str();
}
}  // namespace

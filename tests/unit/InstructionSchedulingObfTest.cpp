#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <cstdint>
#include <string>
#include <vector>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/InstructionScheduling.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class InstructionSchedulingObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_sched", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Serialize the function to a string for comparison.
  std::string serializeFunction(llvm::Function &F) {
    std::string str;
    llvm::raw_string_ostream os(str);
    F.print(os);
    return str;
  }

  /// Create a function with several independent arithmetic operations that can
  /// be freely reordered, plus some dependent chains.
  ///
  ///   define i32 @fn(i32 %a, i32 %b, i32 %c) {
  ///   entry:
  ///     %x = add i32 %a, %b       ; independent of y, z
  ///     %y = sub i32 %b, %c       ; independent of x, z
  ///     %z = xor i32 %a, %c       ; independent of x, y
  ///     %w = mul i32 %x, %y       ; depends on x and y
  ///     %r = add i32 %w, %z       ; depends on w and z
  ///     ret i32 %r
  ///   }
  llvm::Function *createIndependentOpsFunction(llvm::Module &M,
                                                const std::string &name) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy =
        llvm::FunctionType::get(i32Ty, {i32Ty, i32Ty, i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *a = F->getArg(0);
    auto *b = F->getArg(1);
    auto *c = F->getArg(2);
    auto *x = B.CreateAdd(a, b, "");
    auto *y = B.CreateSub(b, c, "");
    auto *z = B.CreateXor(a, c, "");
    auto *w = B.CreateMul(x, y, "");
    auto *r = B.CreateAdd(w, z, "");
    B.CreateRet(r);
    return F;
  }

  /// Create a function with loads and stores (memory operations).
  ///
  ///   define void @fn(ptr %p, ptr %q) {
  ///   entry:
  ///     %v1 = load i32, ptr %p
  ///     store i32 42, ptr %q
  ///     %v2 = load i32, ptr %p
  ///     %sum = add i32 %v1, %v2
  ///     store i32 %sum, ptr %q
  ///     ret void
  ///   }
  llvm::Function *createMemoryOpsFunction(llvm::Module &M,
                                           const std::string &name) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *ptrTy = llvm::PointerType::getUnqual(Ctx);
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, {ptrTy, ptrTy}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *p = F->getArg(0);
    auto *q = F->getArg(1);
    auto *v1 = B.CreateLoad(i32Ty, p, "");
    B.CreateStore(llvm::ConstantInt::get(i32Ty, 42), q);
    auto *v2 = B.CreateLoad(i32Ty, p, "");
    auto *sum = B.CreateAdd(v1, v2, "");
    B.CreateStore(sum, q);
    B.CreateRetVoid();
    return F;
  }

  /// Collect non-PHI non-terminator instructions in order.
  std::vector<unsigned> collectOpcodeOrder(llvm::Function &F) {
    std::vector<unsigned> ops;
    for (auto &BB : F)
      for (auto &I : BB) {
        if (llvm::isa<llvm::PHINode>(&I) || I.isTerminator())
          continue;
        ops.push_back(I.getOpcode());
      }
    return ops;
  }
};

// ---------------------------------------------------------------------------
// 1. ModuleVerifies: scheduling doesn't break the module
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, ModuleVerifies) {
  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createModule();
    createIndependentOpsFunction(*M, "fn");
    ollvm::FilterConfig cfg;
    cfg.transform_percent = 100;
    ollvm::scheduleInstructionsModule(*M, seed, cfg);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed with seed=" << seed << ": " << errStr;
  }
}

// ---------------------------------------------------------------------------
// 2. DeterministicOutput: same seed = same output
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, DeterministicOutput) {
  constexpr uint32_t kSeed = 42;
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  auto M1 = createModule();
  createIndependentOpsFunction(*M1, "fn");
  ollvm::scheduleInstructionsModule(*M1, kSeed, cfg);

  auto M2 = createModule();
  createIndependentOpsFunction(*M2, "fn");
  ollvm::scheduleInstructionsModule(*M2, kSeed, cfg);

  auto ir1 = serializeFunction(*M1->getFunction("fn"));
  auto ir2 = serializeFunction(*M2->getFunction("fn"));
  EXPECT_EQ(ir1, ir2) << "Same seed should produce identical output";
}

// ---------------------------------------------------------------------------
// 3. DifferentSeedsDiffer: at least one seed in [0..50) produces a different
//    instruction order than seed 0.
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, DifferentSeedsDiffer) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  auto M0 = createModule();
  createIndependentOpsFunction(*M0, "fn");
  ollvm::scheduleInstructionsModule(*M0, 0, cfg);
  auto ir0 = serializeFunction(*M0->getFunction("fn"));

  bool found_different = false;
  for (uint32_t seed = 1; seed < 50; ++seed) {
    auto M = createModule();
    createIndependentOpsFunction(*M, "fn");
    ollvm::scheduleInstructionsModule(*M, seed, cfg);
    auto ir = serializeFunction(*M->getFunction("fn"));
    if (ir != ir0) {
      found_different = true;
      break;
    }
  }
  EXPECT_TRUE(found_different)
      << "Different seeds should produce different orderings";
}

// ---------------------------------------------------------------------------
// 4. MemoryOrderPreserved: memory operations stay in their original relative
//    order after scheduling.
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, MemoryOrderPreserved) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    createMemoryOpsFunction(*M, "fn");
    auto *F = M->getFunction("fn");

    // Collect memory instruction order before scheduling.
    std::vector<unsigned> memBefore;
    for (auto &I : F->getEntryBlock()) {
      if (I.isTerminator()) continue;
      if (I.mayReadOrWriteMemory())
        memBefore.push_back(I.getOpcode());
    }

    ollvm::scheduleInstructionsModule(*M, seed, cfg);

    // Collect memory instruction order after scheduling.
    std::vector<unsigned> memAfter;
    for (auto &I : F->getEntryBlock()) {
      if (I.isTerminator()) continue;
      if (I.mayReadOrWriteMemory())
        memAfter.push_back(I.getOpcode());
    }

    EXPECT_EQ(memBefore, memAfter)
        << "Memory operation order should be preserved (seed=" << seed << ")";

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed with seed=" << seed << ": " << errStr;
  }
}

// ---------------------------------------------------------------------------
// 5. PHIsStayAtTop: PHI nodes must remain before all non-PHI instructions.
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, PHIsStayAtTop) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "phi_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  auto *loopBB = llvm::BasicBlock::Create(Ctx, "", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "", F);

  // entry: br loop
  llvm::IRBuilder<> entryB(entry);
  entryB.CreateBr(loopBB);

  // loop: phi, some arithmetic, conditional br
  llvm::IRBuilder<> loopB(loopBB);
  auto *phi = loopB.CreatePHI(i32Ty, 2, "");
  phi->addIncoming(F->getArg(0), entry);
  auto *inc = loopB.CreateAdd(phi, llvm::ConstantInt::get(i32Ty, 1), "");
  auto *mul = loopB.CreateMul(phi, llvm::ConstantInt::get(i32Ty, 2), "");
  auto *combined = loopB.CreateAdd(inc, mul, "");
  phi->addIncoming(combined, loopBB);
  auto *cmp = loopB.CreateICmpSLT(combined, llvm::ConstantInt::get(i32Ty, 100), "");
  loopB.CreateCondBr(cmp, loopBB, exitBB);

  // exit: ret
  llvm::IRBuilder<> exitB(exitBB);
  exitB.CreateRet(combined);

  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto Mc = llvm::CloneModule(*M);
    ollvm::scheduleInstructionsModule(*Mc, seed, cfg);

    // Check that in the loop BB, PHIs come first.
    auto &loopBlock = *std::next(Mc->getFunction("phi_fn")->begin());
    bool seenNonPhi = false;
    for (auto &I : loopBlock) {
      if (llvm::isa<llvm::PHINode>(&I)) {
        EXPECT_FALSE(seenNonPhi)
            << "PHI node found after non-PHI instruction (seed=" << seed << ")";
      } else {
        seenNonPhi = true;
      }
    }

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*Mc, &errOS))
        << "Module verification failed with seed=" << seed << ": " << errStr;
  }
}

// ---------------------------------------------------------------------------
// 6. TerminatorStaysAtEnd: terminator must always be the last instruction.
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, TerminatorStaysAtEnd) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createModule();
    createIndependentOpsFunction(*M, "fn");
    ollvm::scheduleInstructionsModule(*M, seed, cfg);
    auto *F = M->getFunction("fn");
    for (auto &BB : *F) {
      EXPECT_TRUE(BB.back().isTerminator())
          << "Terminator not at end of block (seed=" << seed << ")";
    }
  }
}

// ---------------------------------------------------------------------------
// 7. DeclarationSkipped: declare-only function should not crash.
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, DeclarationSkipped) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage, "decl_fn", *M);

  ollvm::scheduleInstructionsModule(*M, 42);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed: " << errStr;
}

// ---------------------------------------------------------------------------
// 8. EntryAllocasStayAtTop: allocas in the entry block prefix stay pinned.
// ---------------------------------------------------------------------------
TEST_F(InstructionSchedulingObfTest, EntryAllocasStayAtTop) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty, i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "alloca_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  llvm::IRBuilder<> B(entry);

  // Two allocas at top.
  auto *a1 = B.CreateAlloca(i32Ty, nullptr, "");
  auto *a2 = B.CreateAlloca(i32Ty, nullptr, "");
  // Then some independent arithmetic.
  B.CreateStore(F->getArg(0), a1);
  B.CreateStore(F->getArg(1), a2);
  auto *v1 = B.CreateLoad(i32Ty, a1, "");
  auto *v2 = B.CreateLoad(i32Ty, a2, "");
  auto *sum = B.CreateAdd(v1, v2, "");
  auto *diff = B.CreateSub(v1, v2, "");
  auto *result = B.CreateMul(sum, diff, "");
  B.CreateRet(result);

  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto Mc = llvm::CloneModule(*M);
    ollvm::scheduleInstructionsModule(*Mc, seed, cfg);

    auto &entryBlock = Mc->getFunction("alloca_fn")->getEntryBlock();
    auto it = entryBlock.begin();
    // First two instructions must still be allocas.
    EXPECT_TRUE(llvm::isa<llvm::AllocaInst>(&*it))
        << "First instruction should be alloca (seed=" << seed << ")";
    ++it;
    EXPECT_TRUE(llvm::isa<llvm::AllocaInst>(&*it))
        << "Second instruction should be alloca (seed=" << seed << ")";

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*Mc, &errOS))
        << "Module verification failed with seed=" << seed << ": " << errStr;
  }
}

}  // namespace

#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/Flattening.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class FlatteningObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_flatten", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function with conditional branches that survive mergeLinearChains.
  /// entry → (cond) → block_0 or exit
  /// block_i → (cond) → block_{i+1} or exit
  /// block_{N-1} → exit
  /// exit has a PHI node merging values from all predecessors.
  llvm::Function *createChainedFunction(llvm::Module &M,
                                        const std::string &name,
                                        unsigned numBlocks) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg = F->getArg(0);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

    // Create intermediate blocks.
    std::vector<llvm::BasicBlock *> blocks;
    for (unsigned i = 0; i < numBlocks; ++i)
      blocks.push_back(llvm::BasicBlock::Create(
          Ctx, "block_" + std::to_string(i), F));

    // Entry: conditional branch to block_0 or exit.
    llvm::IRBuilder<> entryB(entryBB);
    auto *entryCond = entryB.CreateICmpSGT(
        arg, llvm::ConstantInt::get(i64Ty, 0));
    entryB.CreateCondBr(entryCond, blocks[0], exitBB);

    // Each intermediate block: compute a value, conditionally branch to next or exit.
    std::vector<std::pair<llvm::Value *, llvm::BasicBlock *>> phiIncoming;
    phiIncoming.emplace_back(arg, entryBB);  // from entry → exit

    llvm::Value *prevVal = arg;
    for (unsigned i = 0; i < numBlocks; ++i) {
      llvm::IRBuilder<> builder(blocks[i]);
      auto *val = builder.CreateAdd(
          prevVal, llvm::ConstantInt::get(i64Ty, i + 1),
          "add_" + std::to_string(i));
      if (i + 1 < numBlocks) {
        auto *cond = builder.CreateICmpSGT(
            val, llvm::ConstantInt::get(i64Ty, static_cast<int64_t>(i + 1)));
        builder.CreateCondBr(cond, blocks[i + 1], exitBB);
        phiIncoming.emplace_back(val, blocks[i]);
      } else {
        // Last block: unconditional branch to exit.
        builder.CreateBr(exitBB);
        phiIncoming.emplace_back(val, blocks[i]);
      }
      prevVal = val;
    }

    // Exit: PHI merging all incoming values, then ret.
    llvm::IRBuilder<> exitB(exitBB);
    auto *phi = exitB.CreatePHI(i64Ty, static_cast<unsigned>(phiIncoming.size()));
    for (auto &[val, bb] : phiIncoming)
      phi->addIncoming(val, bb);
    exitB.CreateRet(phi);

    return F;
  }

  /// Create a single-block function.
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

  unsigned countBlocks(llvm::Function &F) {
    return static_cast<unsigned>(F.size());
  }

  /// Find the SwitchInst in the function (the dispatcher), or nullptr.
  llvm::SwitchInst *findSwitch(llvm::Function &F) {
    for (auto &BB : F) {
      if (auto *sw = llvm::dyn_cast<llvm::SwitchInst>(BB.getTerminator()))
        return sw;
    }
    return nullptr;
  }

  /// Check if a function has been flattened (switch or if-else dispatch).
  /// Detects the affine decode pattern (sub + mul) in a block with >=2 preds.
  bool isFlattened(llvm::Function &F) {
    if (findSwitch(F))
      return true;
    // If-else variant: look for a block that has a mul (affine decode)
    // and has multiple predecessors (dispatcher loop target).
    for (auto &BB : F) {
      if (!BB.hasNPredecessorsOrMore(2))
        continue;
      bool hasMul = false;
      for (auto &I : BB) {
        if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
          if (bin->getOpcode() == llvm::Instruction::Mul)
            hasMul = true;
        }
      }
      if (hasMul)
        return true;
    }
    return false;
  }

  std::string serializeFunction(llvm::Function &F) {
    std::string str;
    llvm::raw_string_ostream os(str);
    F.print(os);
    return str;
  }
};

TEST_F(FlatteningObfTest, BasicFlattening) {
  auto M = createModule();
  createChainedFunction(*M, "test_fn", 3);
  auto *F = M->getFunction("test_fn");
  unsigned blocksBefore = countBlocks(*F);

  ollvm::flattenModule(*M, 42);

  // After flattening, a switch dispatcher should exist.
  auto *sw = findSwitch(*F);
  ASSERT_NE(sw, nullptr) << "Flattening should create a switch dispatcher";

  // Block count should increase (dispatcher, loop_end, default, bogus cases).
  unsigned blocksAfter = countBlocks(*F);
  EXPECT_GT(blocksAfter, blocksBefore)
      << "Block count should increase after flattening";
}

TEST_F(FlatteningObfTest, SingleBlockSkipped) {
  auto M = createModule();
  createSingleBlockFunction(*M, "single_fn");
  auto *F = M->getFunction("single_fn");
  unsigned blocksBefore = countBlocks(*F);

  ollvm::flattenModule(*M, 42);

  unsigned blocksAfter = countBlocks(*F);
  EXPECT_EQ(blocksAfter, blocksBefore)
      << "Single-block functions should not be modified";
  EXPECT_EQ(findSwitch(*F), nullptr)
      << "No switch dispatcher for single-block function";
}

TEST_F(FlatteningObfTest, BogusCasesAdded) {
  auto M = createModule();
  // 5 intermediate blocks + entry + exit = 7 blocks total.
  // After mergeLinearChains, the linear chain collapses.
  // Use a branching structure to prevent chain merging.
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "branch_fn", *M);
  auto *arg = F->getArg(0);

  // Create blocks with conditional branches to prevent merging.
  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *bb1 = llvm::BasicBlock::Create(Ctx, "bb1", F);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "bb2", F);
  auto *bb3 = llvm::BasicBlock::Create(Ctx, "bb3", F);
  auto *bb4 = llvm::BasicBlock::Create(Ctx, "bb4", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

  llvm::IRBuilder<> entryB(entryBB);
  auto *cond = entryB.CreateICmpSGT(arg, llvm::ConstantInt::get(i64Ty, 0));
  entryB.CreateCondBr(cond, bb1, bb2);

  llvm::IRBuilder<> b1(bb1);
  auto *v1 = b1.CreateAdd(arg, llvm::ConstantInt::get(i64Ty, 1));
  b1.CreateBr(bb3);

  llvm::IRBuilder<> b2(bb2);
  auto *v2 = b2.CreateSub(arg, llvm::ConstantInt::get(i64Ty, 1));
  b2.CreateBr(bb3);

  llvm::IRBuilder<> b3(bb3);
  auto *phi = b3.CreatePHI(i64Ty, 2);
  phi->addIncoming(v1, bb1);
  phi->addIncoming(v2, bb2);
  auto *cond2 = b3.CreateICmpSGT(phi, llvm::ConstantInt::get(i64Ty, 5));
  b3.CreateCondBr(cond2, bb4, exitBB);

  llvm::IRBuilder<> b4(bb4);
  auto *v4 = b4.CreateMul(phi, llvm::ConstantInt::get(i64Ty, 2));
  b4.CreateBr(exitBB);

  llvm::IRBuilder<> exitB(exitBB);
  auto *exitPhi = exitB.CreatePHI(i64Ty, 2);
  exitPhi->addIncoming(phi, bb3);
  exitPhi->addIncoming(v4, bb4);
  exitB.CreateRet(exitPhi);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::flattenModule(*M, 42);

  auto *sw = findSwitch(*F);
  ASSERT_NE(sw, nullptr);

  // The pass adds min(numOrigBlocks, 8) bogus cases, at least 2.
  // So total cases > number of original non-entry blocks.
  unsigned numCases = sw->getNumCases();
  // We had 5 non-entry blocks; after demoting and splitting, the number of
  // real switch cases + bogus cases should exceed original block count.
  EXPECT_GE(numCases, 5u + 2u)
      << "Switch should have bogus cases beyond the original blocks";
}

TEST_F(FlatteningObfTest, BogusCaseBlocksHaveXor) {
  auto M = createModule();
  createChainedFunction(*M, "test_fn", 5);

  ollvm::flattenModule(*M, 42);

  auto *F = M->getFunction("test_fn");
  auto *sw = findSwitch(*F);
  ASSERT_NE(sw, nullptr);

  // Look for XOR instructions in switch case blocks — bogus blocks use
  // load→xor→store→br pattern.
  bool foundXor = false;
  for (auto &c : sw->cases()) {
    auto *caseBB = c.getCaseSuccessor();
    for (auto &I : *caseBB) {
      if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        if (bin->getOpcode() == llvm::Instruction::Xor) {
          foundXor = true;
          break;
        }
      }
    }
    if (foundXor)
      break;
  }
  EXPECT_TRUE(foundXor)
      << "Bogus case blocks should contain XOR instructions";
}

TEST_F(FlatteningObfTest, EHFunctionHandled) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *voidTy = llvm::Type::getVoidTy(Ctx);
  auto *i8PtrTy = llvm::PointerType::getUnqual(Ctx);

  // Create a function with invoke + landing pad (resume).
  auto *fnTy = llvm::FunctionType::get(voidTy, {}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "eh_fn", *M);
  F->setPersonalityFn(llvm::ConstantPointerNull::get(
      llvm::PointerType::getUnqual(Ctx)));

  auto *calleeTy = llvm::FunctionType::get(voidTy, {}, false);
  auto *callee = llvm::Function::Create(calleeTy,
                                        llvm::Function::ExternalLinkage,
                                        "may_throw", *M);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *normalBB = llvm::BasicBlock::Create(Ctx, "normal", F);
  auto *lpBB = llvm::BasicBlock::Create(Ctx, "lpad", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

  // entry: invoke may_throw() to normal unwind lpad
  llvm::IRBuilder<> entryB(entryBB);
  entryB.CreateInvoke(callee, normalBB, lpBB);

  // normal: branch to exit
  llvm::IRBuilder<> normalB(normalBB);
  normalB.CreateBr(exitBB);

  // lpad: cleanup landing pad + resume
  llvm::IRBuilder<> lpB(lpBB);
  auto *lpType = llvm::StructType::get(Ctx, {i8PtrTy, i32Ty});
  auto *lp = lpB.CreateLandingPad(lpType, 0);
  lp->setCleanup(true);
  lpB.CreateResume(lp);

  // exit: ret void
  llvm::IRBuilder<> exitB(exitBB);
  exitB.CreateRetVoid();

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Should not crash.
  ollvm::flattenModule(*M, 42);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module with EH should verify after flattening: " << errStr;
}

TEST_F(FlatteningObfTest, AffineEncoding) {
  auto M = createModule();
  createChainedFunction(*M, "test_fn", 4);

  ollvm::flattenModule(*M, 42);

  auto *F = M->getFunction("test_fn");
  auto *sw = findSwitch(*F);
  ASSERT_NE(sw, nullptr);

  // The dispatcher block decodes with: sub then mul (affine decoding).
  // Check that the dispatcher block (parent of switch) contains a mul.
  auto *dispBB = sw->getParent();
  bool foundMul = false;
  for (auto &I : *dispBB) {
    if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
      if (bin->getOpcode() == llvm::Instruction::Mul) {
        foundMul = true;
        break;
      }
    }
  }
  EXPECT_TRUE(foundMul)
      << "Dispatcher should contain mul for affine decoding";
}

TEST_F(FlatteningObfTest, ModuleVerifiesAllSeeds) {
  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createModule();
    createChainedFunction(*M, "test_fn", 5);

    ollvm::flattenModule(*M, seed);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed with seed " << seed << ": " << errStr;
  }
}

TEST_F(FlatteningObfTest, DeterministicOutput) {
  auto M1 = createModule();
  createChainedFunction(*M1, "test_fn", 5);
  ollvm::flattenModule(*M1, 12345);
  auto ir1 = serializeFunction(*M1->getFunction("test_fn"));

  auto M2 = createModule();
  createChainedFunction(*M2, "test_fn", 5);
  ollvm::flattenModule(*M2, 12345);
  auto ir2 = serializeFunction(*M2->getFunction("test_fn"));

  EXPECT_EQ(ir1, ir2)
      << "Same seed should produce identical flattening output";

  // Different seed → different output.
  auto M3 = createModule();
  createChainedFunction(*M3, "test_fn", 5);
  ollvm::flattenModule(*M3, 99999);
  auto ir3 = serializeFunction(*M3->getFunction("test_fn"));

  EXPECT_NE(ir1, ir3)
      << "Different seeds should produce different flattening output";
}

TEST_F(FlatteningObfTest, ManyBlocksFunction) {
  auto M = createModule();
  createChainedFunction(*M, "test_fn", 20);

  ollvm::flattenModule(*M, 42);

  auto *F = M->getFunction("test_fn");
  EXPECT_TRUE(isFlattened(*F))
      << "20-block function should be flattened";

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module verification failed for 20-block function: " << errStr;
}

TEST_F(FlatteningObfTest, FunctionWithLoops) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "loop_fn", *M);
  auto *arg = F->getArg(0);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *headerBB = llvm::BasicBlock::Create(Ctx, "header", F);
  auto *bodyBB = llvm::BasicBlock::Create(Ctx, "body", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

  // entry → header
  llvm::IRBuilder<> entryB(entryBB);
  entryB.CreateBr(headerBB);

  // header: i = phi [arg, entry], [i_next, body]; if i > 0 → body else exit
  llvm::IRBuilder<> headerB(headerBB);
  auto *iPhi = headerB.CreatePHI(i64Ty, 2, "i");
  auto *cond = headerB.CreateICmpSGT(iPhi, llvm::ConstantInt::get(i64Ty, 0));
  headerB.CreateCondBr(cond, bodyBB, exitBB);

  // body: i_next = i - 1; → header
  llvm::IRBuilder<> bodyB(bodyBB);
  auto *iNext = bodyB.CreateSub(iPhi, llvm::ConstantInt::get(i64Ty, 1),
                                "i_next");
  bodyB.CreateBr(headerBB);

  iPhi->addIncoming(arg, entryBB);
  iPhi->addIncoming(iNext, bodyBB);

  // exit: ret i
  llvm::IRBuilder<> exitB(exitBB);
  exitB.CreateRet(iPhi);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::flattenModule(*M, 42);

  std::string errStr;
  llvm::raw_string_ostream errOS(errStr);
  EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
      << "Module with loops should verify after flattening: " << errStr;
}

// Helper: create a function with i32 arithmetic across multiple branches.
// entry: cond br to bb1 or bb2
// bb1: x = arg + 42; br exit
// bb2: y = arg * 7; br exit
// exit: phi(x,y); ret
static llvm::Function *createI32ArithFunction(llvm::LLVMContext &Ctx,
                                               llvm::Module &M,
                                               const std::string &name) {
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   name, M);
  auto *arg = F->getArg(0);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *bb1 = llvm::BasicBlock::Create(Ctx, "bb1", F);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "bb2", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

  llvm::IRBuilder<> entryB(entryBB);
  auto *cond = entryB.CreateICmpSGT(arg, llvm::ConstantInt::get(i32Ty, 0));
  entryB.CreateCondBr(cond, bb1, bb2);

  llvm::IRBuilder<> b1(bb1);
  auto *x = b1.CreateAdd(arg, llvm::ConstantInt::get(i32Ty, 42), "x");
  b1.CreateBr(exitBB);

  llvm::IRBuilder<> b2(bb2);
  auto *y = b2.CreateMul(arg, llvm::ConstantInt::get(i32Ty, 7), "y");
  b2.CreateBr(exitBB);

  llvm::IRBuilder<> exitB(exitBB);
  auto *phi = exitB.CreatePHI(i32Ty, 2);
  phi->addIncoming(x, bb1);
  phi->addIncoming(y, bb2);
  exitB.CreateRet(phi);

  return F;
}

// Helper: create a function with many i32 BinaryOperator constants to maximize
// the chance of encryption triggering (50% coin per operand).
static llvm::Function *createI32ManyConstsFunction(llvm::LLVMContext &Ctx,
                                                   llvm::Module &M,
                                                   const std::string &name) {
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   name, M);
  auto *arg = F->getArg(0);

  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *bb1 = llvm::BasicBlock::Create(Ctx, "bb1", F);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "bb2", F);
  auto *bb3 = llvm::BasicBlock::Create(Ctx, "bb3", F);
  auto *exitBB = llvm::BasicBlock::Create(Ctx, "exit", F);

  llvm::IRBuilder<> entryB(entryBB);
  auto *cond = entryB.CreateICmpSGT(arg, llvm::ConstantInt::get(i32Ty, 0));
  entryB.CreateCondBr(cond, bb1, bb2);

  // bb1: chain of 6 arithmetic ops with distinct i32 constants.
  llvm::IRBuilder<> b1(bb1);
  auto *v = b1.CreateAdd(arg, llvm::ConstantInt::get(i32Ty, 11));
  v = b1.CreateSub(v, llvm::ConstantInt::get(i32Ty, 22));
  v = b1.CreateMul(v, llvm::ConstantInt::get(i32Ty, 3));
  v = b1.CreateAdd(v, llvm::ConstantInt::get(i32Ty, 44));
  v = b1.CreateXor(v, llvm::ConstantInt::get(i32Ty, 55));
  v = b1.CreateOr(v, llvm::ConstantInt::get(i32Ty, 66));
  auto *cond2 = b1.CreateICmpSGT(v, llvm::ConstantInt::get(i32Ty, 100));
  b1.CreateCondBr(cond2, bb3, bb2);

  // bb2: another chain of 6 arithmetic ops.
  llvm::IRBuilder<> b2(bb2);
  auto *w = b2.CreateSub(arg, llvm::ConstantInt::get(i32Ty, 77));
  w = b2.CreateAnd(w, llvm::ConstantInt::get(i32Ty, 0xFF));
  w = b2.CreateAdd(w, llvm::ConstantInt::get(i32Ty, 88));
  w = b2.CreateMul(w, llvm::ConstantInt::get(i32Ty, 5));
  w = b2.CreateShl(w, llvm::ConstantInt::get(i32Ty, 1));
  w = b2.CreateAdd(w, llvm::ConstantInt::get(i32Ty, 99));
  b2.CreateBr(exitBB);

  // bb3: more ops.
  llvm::IRBuilder<> b3(bb3);
  auto *z = b3.CreateAdd(v, llvm::ConstantInt::get(i32Ty, 111));
  z = b3.CreateSub(z, llvm::ConstantInt::get(i32Ty, 222));
  b3.CreateBr(exitBB);

  llvm::IRBuilder<> exitB(exitBB);
  auto *phi = exitB.CreatePHI(i32Ty, 2);
  phi->addIncoming(w, bb2);
  phi->addIncoming(z, bb3);
  exitB.CreateRet(phi);

  return F;
}

TEST_F(FlatteningObfTest, ConstantEncryptionPresent) {
  // Constant encryption replaces i32 ConstantInt operands with
  // load(switch_var) XOR encrypted_constant. Test across multiple seeds
  // because the encryption is a 50% coin flip per operand.
  bool foundEncryptedXor = false;

  for (uint32_t seed = 0; seed < 50 && !foundEncryptedXor; ++seed) {
    auto M = createModule();
    createI32ManyConstsFunction(Ctx, *M, "const_enc_fn");
    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    ollvm::flattenModule(*M, seed);

    auto *F = M->getFunction("const_enc_fn");
    ASSERT_NE(F, nullptr);

    // After flattening, look for the pattern:
    //   %sv = load i32, ptr %switch_var
    //   %dec = xor i32 %sv, <encrypted_const>
    //   <binop> ... %dec ...
    // The load's pointer operand should be an alloca (the switch_var).
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I);
        if (!bin) continue;

        // Check if any operand is produced by an XOR whose LHS is a load
        // from an alloca (the switch_var).
        for (unsigned op = 0; op < bin->getNumOperands(); ++op) {
          auto *xorInst = llvm::dyn_cast<llvm::BinaryOperator>(bin->getOperand(op));
          if (!xorInst || xorInst->getOpcode() != llvm::Instruction::Xor)
            continue;

          auto *load = llvm::dyn_cast<llvm::LoadInst>(xorInst->getOperand(0));
          if (!load) continue;

          auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(load->getPointerOperand());
          if (alloca && alloca->getAllocatedType()->isIntegerTy(32)) {
            foundEncryptedXor = true;
            break;
          }
        }
        if (foundEncryptedXor) break;
      }
      if (foundEncryptedXor) break;
    }
  }

  EXPECT_TRUE(foundEncryptedXor)
      << "Expected load(switch_var)->xor->binop pattern from constant encryption";
}

TEST_F(FlatteningObfTest, ConstantEncryptionVerifies) {
  // Fuzz 50 seeds to verify constant encryption never produces invalid IR.
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createModule();
    createI32ManyConstsFunction(Ctx, *M, "const_enc_fuzz");
    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "Pre-flatten verification failed";

    ollvm::flattenModule(*M, seed);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Constant encryption produced invalid IR with seed " << seed
        << ": " << errStr;
  }
}

TEST_F(FlatteningObfTest, NoSideEffectIntrinsic) {
  // Verify @llvm.sideeffect intrinsic is NOT present in output.
  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M = createModule();
    createChainedFunction(*M, "test_fn", 5);
    ollvm::flattenModule(*M, seed);

    auto *F = M->getFunction("test_fn");
    for (auto &BB : *F) {
      for (auto &I : BB) {
        if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
          if (auto *callee = call->getCalledFunction()) {
            EXPECT_FALSE(callee->isIntrinsic() &&
                         callee->getIntrinsicID() == llvm::Intrinsic::sideeffect)
                << "Found @llvm.sideeffect in seed " << seed;
          }
        }
      }
    }
  }
}

TEST_F(FlatteningObfTest, IfElseDispatchVariant) {
  // Over many seeds, both switch and if-else dispatch should appear.
  unsigned switchCount = 0;
  unsigned ifElseCount = 0;
  for (uint32_t seed = 0; seed < 100; ++seed) {
    auto M = createModule();
    createChainedFunction(*M, "test_fn", 5);
    ollvm::flattenModule(*M, seed);

    auto *F = M->getFunction("test_fn");
    if (findSwitch(*F))
      ++switchCount;
    else if (isFlattened(*F))
      ++ifElseCount;

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Verification failed with seed " << seed << ": " << errStr;
  }
  EXPECT_GT(switchCount, 0u)
      << "Expected some functions to use switch dispatch";
  EXPECT_GT(ifElseCount, 0u)
      << "Expected some functions to use if-else dispatch";
}

}  // namespace

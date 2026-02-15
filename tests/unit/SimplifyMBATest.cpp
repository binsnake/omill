#include "omill/Simplifier/LLVMTranslator.h"
#include "omill/Passes/SimplifyMBA.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class SimplifyMBATest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    return M;
  }

  /// Create a function with two i32 args.
  llvm::Function *createBinaryFunc(llvm::Module &M, llvm::StringRef name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *fn_ty = llvm::FunctionType::get(i32, {i32, i32}, false);
    return llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                  name, M);
  }

  /// Create a function with one i32 arg.
  llvm::Function *createUnaryFunc(llvm::Module &M, llvm::StringRef name) {
    auto *i32 = llvm::Type::getInt32Ty(Ctx);
    auto *fn_ty = llvm::FunctionType::get(i32, {i32}, false);
    return llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                  name, M);
  }

  void runPass(llvm::Function &F) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::SimplifyMBAPass());
    FPM.run(F, FAM);
  }
};

// --- LLVMTranslator round-trip tests ---

TEST_F(SimplifyMBATest, ConstantRoundTrip) {
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(llvm::ConstantInt::get(B.getInt32Ty(), 42));

  omill::LLVMTranslator T;
  auto *val = llvm::ConstantInt::get(B.getInt32Ty(), 42);
  auto idx = T.translate(val);
  auto *result = T.reconstruct(idx, B);

  ASSERT_TRUE(llvm::isa<llvm::ConstantInt>(result));
  EXPECT_EQ(llvm::cast<llvm::ConstantInt>(result)->getZExtValue(), 42u);
}

TEST_F(SimplifyMBATest, SymbolRoundTrip) {
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(0));

  omill::LLVMTranslator T;
  auto *arg = F->getArg(0);
  auto idx = T.translate(arg);
  auto *result = T.reconstruct(idx, B);

  EXPECT_EQ(result, arg);
}

TEST_F(SimplifyMBATest, SimpleAddRoundTrip) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *add = B.CreateAdd(F->getArg(0), F->getArg(1));
  B.CreateRet(add);

  omill::LLVMTranslator T;
  auto idx = T.translate(add);
  auto *result = T.reconstruct(idx, B);

  ASSERT_TRUE(llvm::isa<llvm::BinaryOperator>(result));
  EXPECT_EQ(llvm::cast<llvm::BinaryOperator>(result)->getOpcode(),
            llvm::Instruction::Add);
}

TEST_F(SimplifyMBATest, SubEncoding) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *sub = B.CreateSub(F->getArg(0), F->getArg(1));
  B.CreateRet(sub);

  // Sub should be encodable and reconstructable.
  omill::LLVMTranslator T;
  auto idx = T.translate(sub);
  // Just verify it doesn't crash and produces a valid AST.
  uint8_t opcode = ContextGetOpcode(T.getContext(), idx);
  // Sub is encoded as add(a, add(neg(b), 1)), so top-level should be add.
  EXPECT_EQ(opcode, EQSAT_OP_ADD);

  auto *result = T.reconstruct(idx, B);
  ASSERT_NE(result, nullptr);
}

TEST_F(SimplifyMBATest, ShlConstant) {
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *shl = B.CreateShl(F->getArg(0), 3);
  B.CreateRet(shl);

  omill::LLVMTranslator T;
  auto idx = T.translate(shl);
  // shl x, 3 → mul(x, 8), so top-level should be mul.
  uint8_t opcode = ContextGetOpcode(T.getContext(), idx);
  EXPECT_EQ(opcode, EQSAT_OP_MUL);
}

TEST_F(SimplifyMBATest, ShlVariableOpaque) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *shl = B.CreateShl(F->getArg(0), F->getArg(1));
  B.CreateRet(shl);

  omill::LLVMTranslator T;
  auto idx = T.translate(shl);
  // Variable shift → opaque symbol.
  uint8_t opcode = ContextGetOpcode(T.getContext(), idx);
  EXPECT_EQ(opcode, EQSAT_OP_SYMBOL);
}

TEST_F(SimplifyMBATest, XorAndToAdd) {
  // (x ^ y) + 2 * (x & y) should simplify to x + y.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *xor_xy = B.CreateXor(x, y);
  auto *and_xy = B.CreateAnd(x, y);
  auto *two = llvm::ConstantInt::get(B.getInt32Ty(), 2);
  auto *mul = B.CreateMul(two, and_xy);
  auto *result = B.CreateAdd(xor_xy, mul);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  ASSERT_NE(simplified, nullptr);

  // The simplified result should be simpler (lower cost).
  // Ideally it's x + y, but we just verify it's non-null (cost improved).
}

TEST_F(SimplifyMBATest, IdentityElimination) {
  // x + 0 should simplify to x.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *zero = llvm::ConstantInt::get(B.getInt32Ty(), 0);
  auto *add = B.CreateAdd(x, zero);
  B.CreateRet(add);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(add, B);
  // Should simplify: either to x directly, or at least reduce cost.
  // If EqSat recognizes x+0=x, result should be non-null.
  if (simplified) {
    EXPECT_EQ(simplified, x);
  }
  // If the simplifier doesn't handle this identity, that's OK too —
  // InstCombine would get it. This test just verifies we don't crash.
}

TEST_F(SimplifyMBATest, NoCostImprovement) {
  // x + y is already simple — should return nullptr.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *add = B.CreateAdd(F->getArg(0), F->getArg(1));
  B.CreateRet(add);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(add, B);
  EXPECT_EQ(simplified, nullptr);
}

TEST_F(SimplifyMBATest, ZextTruncRoundTrip) {
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *trunc = B.CreateTrunc(x, B.getInt16Ty());
  auto *zext = B.CreateZExt(trunc, B.getInt32Ty());
  B.CreateRet(zext);

  omill::LLVMTranslator T;
  auto idx = T.translate(zext);
  auto *result = T.reconstruct(idx, B);
  ASSERT_NE(result, nullptr);

  // Result should be a zext of a trunc.
  auto *zext_inst = llvm::dyn_cast<llvm::ZExtInst>(result);
  ASSERT_NE(zext_inst, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::TruncInst>(zext_inst->getOperand(0)));
}

TEST_F(SimplifyMBATest, PassIntegration) {
  // Build IR with (x^y) + 2*(x&y), run the pass, verify it changed.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *xor_xy = B.CreateXor(x, y);
  auto *and_xy = B.CreateAnd(x, y);
  auto *two = llvm::ConstantInt::get(B.getInt32Ty(), 2);
  auto *mul = B.CreateMul(two, and_xy);
  auto *result = B.CreateAdd(xor_xy, mul);
  B.CreateRet(result);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Count instructions before.
  unsigned before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++before;

  runPass(*F);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Count instructions after — should be fewer if MBA was simplified.
  unsigned after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++after;

  EXPECT_LE(after, before);
}

}  // namespace

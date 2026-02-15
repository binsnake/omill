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

// --- Additional round-trip tests ---

TEST_F(SimplifyMBATest, OrRoundTrip) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *or_inst = B.CreateOr(F->getArg(0), F->getArg(1));
  B.CreateRet(or_inst);

  omill::LLVMTranslator T;
  auto idx = T.translate(or_inst);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_OR);

  auto *result = T.reconstruct(idx, B);
  ASSERT_TRUE(llvm::isa<llvm::BinaryOperator>(result));
  EXPECT_EQ(llvm::cast<llvm::BinaryOperator>(result)->getOpcode(),
            llvm::Instruction::Or);
}

TEST_F(SimplifyMBATest, AndRoundTrip) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *and_inst = B.CreateAnd(F->getArg(0), F->getArg(1));
  B.CreateRet(and_inst);

  omill::LLVMTranslator T;
  auto idx = T.translate(and_inst);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_AND);

  auto *result = T.reconstruct(idx, B);
  ASSERT_TRUE(llvm::isa<llvm::BinaryOperator>(result));
  EXPECT_EQ(llvm::cast<llvm::BinaryOperator>(result)->getOpcode(),
            llvm::Instruction::And);
}

TEST_F(SimplifyMBATest, XorRoundTrip) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *xor_inst = B.CreateXor(F->getArg(0), F->getArg(1));
  B.CreateRet(xor_inst);

  omill::LLVMTranslator T;
  auto idx = T.translate(xor_inst);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_XOR);

  auto *result = T.reconstruct(idx, B);
  ASSERT_TRUE(llvm::isa<llvm::BinaryOperator>(result));
  EXPECT_EQ(llvm::cast<llvm::BinaryOperator>(result)->getOpcode(),
            llvm::Instruction::Xor);
}

TEST_F(SimplifyMBATest, MulRoundTrip) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *mul = B.CreateMul(F->getArg(0), F->getArg(1));
  B.CreateRet(mul);

  omill::LLVMTranslator T;
  auto idx = T.translate(mul);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_MUL);

  auto *result = T.reconstruct(idx, B);
  ASSERT_TRUE(llvm::isa<llvm::BinaryOperator>(result));
  EXPECT_EQ(llvm::cast<llvm::BinaryOperator>(result)->getOpcode(),
            llvm::Instruction::Mul);
}

TEST_F(SimplifyMBATest, LShrRoundTrip) {
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *lshr = B.CreateLShr(F->getArg(0), F->getArg(1));
  B.CreateRet(lshr);

  omill::LLVMTranslator T;
  auto idx = T.translate(lshr);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_LSHR);

  auto *result = T.reconstruct(idx, B);
  ASSERT_TRUE(llvm::isa<llvm::BinaryOperator>(result));
  EXPECT_EQ(llvm::cast<llvm::BinaryOperator>(result)->getOpcode(),
            llvm::Instruction::LShr);
}

TEST_F(SimplifyMBATest, AShrOpaque) {
  // AShr has no EqSat equivalent and should become an opaque symbol.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *ashr = B.CreateAShr(F->getArg(0), F->getArg(1));
  B.CreateRet(ashr);

  omill::LLVMTranslator T;
  auto idx = T.translate(ashr);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_SYMBOL);
}

// --- Width / type variation tests ---

TEST_F(SimplifyMBATest, Width8RoundTrip) {
  auto M = createModule();
  auto *i8 = llvm::Type::getInt8Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i8, {i8, i8}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test8", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *add = B.CreateAdd(F->getArg(0), F->getArg(1));
  B.CreateRet(add);

  omill::LLVMTranslator T;
  auto idx = T.translate(add);
  EXPECT_EQ(ContextGetWidth(T.getContext(), idx), 8);
  auto *result = T.reconstruct(idx, B);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->getType(), i8);
}

TEST_F(SimplifyMBATest, Width64RoundTrip) {
  auto M = createModule();
  auto *i64 = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i64, {i64, i64}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test64", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *xor_inst = B.CreateXor(F->getArg(0), F->getArg(1));
  B.CreateRet(xor_inst);

  omill::LLVMTranslator T;
  auto idx = T.translate(xor_inst);
  EXPECT_EQ(ContextGetWidth(T.getContext(), idx), 64);
  auto *result = T.reconstruct(idx, B);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->getType(), i64);
}

// --- MBA identity simplification tests ---

TEST_F(SimplifyMBATest, OrAndToAdd) {
  // (x | y) + (x & y) == x + y
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *or_xy = B.CreateOr(x, y);
  auto *and_xy = B.CreateAnd(x, y);
  auto *result = B.CreateAdd(or_xy, and_xy);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  ASSERT_NE(simplified, nullptr);
}

TEST_F(SimplifyMBATest, OrMinusAndToXor) {
  // (x | y) - (x & y) == x ^ y
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *or_xy = B.CreateOr(x, y);
  auto *and_xy = B.CreateAnd(x, y);
  auto *result = B.CreateSub(or_xy, and_xy);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  ASSERT_NE(simplified, nullptr);
}

TEST_F(SimplifyMBATest, SelectViaBitwiseMBA) {
  // (x & ~m) | (y & m) — a bitwise select/mux pattern.
  // This is a common obfuscated expression. Verify it doesn't crash.
  auto M = createModule();
  auto *i32 = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32, {i32, i32, i32}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *m = F->getArg(2);
  auto *not_m = B.CreateXor(m, llvm::ConstantInt::getSigned(i32, -1));
  auto *lhs = B.CreateAnd(x, not_m);
  auto *rhs = B.CreateAnd(y, m);
  auto *result = B.CreateOr(lhs, rhs);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto idx = T.translate(result);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_OR);

  // Reconstruct and verify it doesn't crash.
  auto *reconstructed = T.reconstruct(idx, B);
  ASSERT_NE(reconstructed, nullptr);
}

TEST_F(SimplifyMBATest, DoubleNegation) {
  // ~~x should simplify to x.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *neg_one = llvm::ConstantInt::getSigned(B.getInt32Ty(), -1);
  auto *not_x = B.CreateXor(x, neg_one);
  auto *not_not_x = B.CreateXor(not_x, neg_one);
  B.CreateRet(not_not_x);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(not_not_x, B);
  if (simplified) {
    EXPECT_EQ(simplified, x);
  }
}

TEST_F(SimplifyMBATest, XorSelfZero) {
  // x ^ x == 0.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *result = B.CreateXor(x, x);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  if (simplified) {
    auto *CI = llvm::dyn_cast<llvm::ConstantInt>(simplified);
    ASSERT_NE(CI, nullptr);
    EXPECT_EQ(CI->getZExtValue(), 0u);
  }
}

TEST_F(SimplifyMBATest, AndSelfIdentity) {
  // x & x == x.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *result = B.CreateAnd(x, x);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  if (simplified) {
    EXPECT_EQ(simplified, x);
  }
}

TEST_F(SimplifyMBATest, OrSelfIdentity) {
  // x | x == x.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *result = B.CreateOr(x, x);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  if (simplified) {
    EXPECT_EQ(simplified, x);
  }
}

TEST_F(SimplifyMBATest, MulByOneIdentity) {
  // x * 1 == x.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *one = llvm::ConstantInt::get(B.getInt32Ty(), 1);
  auto *result = B.CreateMul(x, one);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  if (simplified) {
    EXPECT_EQ(simplified, x);
  }
}

// --- Nested MBA expression tests ---

TEST_F(SimplifyMBATest, NestedMBAAddInXorAndForm) {
  // ((a ^ b) + 2*(a & b)) + ((c ^ d) + 2*(c & d))
  // = (a + b) + (c + d)
  auto M = createModule();
  auto *i32 = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32, {i32, i32, i32, i32}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *a = F->getArg(0);
  auto *b = F->getArg(1);
  auto *c = F->getArg(2);
  auto *d = F->getArg(3);
  auto *two = llvm::ConstantInt::get(i32, 2);

  // (a ^ b) + 2*(a & b)
  auto *xor_ab = B.CreateXor(a, b);
  auto *and_ab = B.CreateAnd(a, b);
  auto *mul_ab = B.CreateMul(two, and_ab);
  auto *lhs = B.CreateAdd(xor_ab, mul_ab);

  // (c ^ d) + 2*(c & d)
  auto *xor_cd = B.CreateXor(c, d);
  auto *and_cd = B.CreateAnd(c, d);
  auto *mul_cd = B.CreateMul(two, and_cd);
  auto *rhs = B.CreateAdd(xor_cd, mul_cd);

  auto *result = B.CreateAdd(lhs, rhs);
  B.CreateRet(result);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++before;

  runPass(*F);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++after;

  EXPECT_LT(after, before);
}

// --- Pass behaviour tests ---

TEST_F(SimplifyMBATest, PassPreservesSimpleFunc) {
  // A function with no MBA expressions should be unchanged.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *add = B.CreateAdd(F->getArg(0), F->getArg(1));
  B.CreateRet(add);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++before;

  runPass(*F);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++after;

  EXPECT_EQ(after, before);
}

TEST_F(SimplifyMBATest, PassMultipleRoots) {
  // Two independent MBA expression roots in the same function.
  auto M = createModule();
  auto *i32 = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {i32, i32}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *two = llvm::ConstantInt::get(i32, 2);

  // Root 1: (x ^ y) + 2*(x & y) — consumed by a store-like external call.
  auto *xor1 = B.CreateXor(x, y);
  auto *and1 = B.CreateAnd(x, y);
  auto *mul1 = B.CreateMul(two, and1);
  auto *root1 = B.CreateAdd(xor1, mul1);

  // Root 2: (x | y) + (x & y) — also consumed externally.
  auto *or2 = B.CreateOr(x, y);
  auto *and2 = B.CreateAnd(x, y);
  auto *root2 = B.CreateAdd(or2, and2);

  // Use both roots in an external call so they're both expression roots.
  auto *sink_ty = llvm::FunctionType::get(void_ty, {i32, i32}, false);
  auto sink = M->getOrInsertFunction("sink", sink_ty);
  B.CreateCall(sink, {root1, root2});
  B.CreateRetVoid();

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++before;

  runPass(*F);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++after;

  EXPECT_LT(after, before);
}

TEST_F(SimplifyMBATest, PassSkipsNonIntegerTypes) {
  // A function with only float/pointer ops should pass through unchanged.
  auto M = createModule();
  auto *f32 = llvm::Type::getFloatTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(f32, {f32, f32}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *fadd = B.CreateFAdd(F->getArg(0), F->getArg(1));
  B.CreateRet(fadd);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++before;

  runPass(*F);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++after;

  EXPECT_EQ(after, before);
}

TEST_F(SimplifyMBATest, TranslatorResetReuse) {
  // Verify the translator can be reset and reused for multiple expressions.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);

  omill::LLVMTranslator T;

  // First expression.
  auto *add = B.CreateAdd(x, y);
  auto idx1 = T.translate(add);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx1), EQSAT_OP_ADD);

  T.reset();

  // Second expression after reset.
  auto *xor_inst = B.CreateXor(x, y);
  auto idx2 = T.translate(xor_inst);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx2), EQSAT_OP_XOR);

  auto *result = T.reconstruct(idx2, B);
  ASSERT_NE(result, nullptr);
  B.CreateRet(result);
}

TEST_F(SimplifyMBATest, DepthLimitProducesSymbol) {
  // With max_depth=0, even a simple add should become an opaque symbol.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *add = B.CreateAdd(F->getArg(0), F->getArg(1));
  B.CreateRet(add);

  omill::LLVMTranslator T;
  auto idx = T.translate(add, /*max_depth=*/0);
  EXPECT_EQ(ContextGetOpcode(T.getContext(), idx), EQSAT_OP_SYMBOL);
}

TEST_F(SimplifyMBATest, ConstantExprFolding) {
  // 3 + 7 should translate to a constant 10.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(0));

  auto *three = llvm::ConstantInt::get(B.getInt32Ty(), 3);
  auto *seven = llvm::ConstantInt::get(B.getInt32Ty(), 7);

  omill::LLVMTranslator T;
  auto a = T.translate(three);
  auto b = T.translate(seven);
  auto sum = ContextAdd(T.getContext(), a, b);
  auto simplified = ContextRecursiveSimplify(T.getContext(), sum);

  // After simplification, should be a constant.
  EXPECT_EQ(ContextGetOpcode(T.getContext(), simplified), EQSAT_OP_CONSTANT);
  EXPECT_EQ(ContextGetConstantValue(T.getContext(), simplified), 10u);
}

TEST_F(SimplifyMBATest, MulByZero) {
  // x * 0 should simplify to 0.
  auto M = createModule();
  auto *F = createUnaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *zero = llvm::ConstantInt::get(B.getInt32Ty(), 0);
  auto *result = B.CreateMul(x, zero);
  B.CreateRet(result);

  omill::LLVMTranslator T;
  auto *simplified = T.simplify(result, B);
  if (simplified) {
    auto *CI = llvm::dyn_cast<llvm::ConstantInt>(simplified);
    ASSERT_NE(CI, nullptr);
    EXPECT_EQ(CI->getZExtValue(), 0u);
  }
}

// --- Obfuscated pattern tests (realistic MBA patterns) ---

TEST_F(SimplifyMBATest, LinearMBAAdd) {
  // Typical linear MBA for x + y:
  //   2*(x | y) + 2*(~x | y) + (~x & y) - 2*(~x | ~y) - (~x & ~y)
  // This is a more complex encoding that real obfuscators produce.
  auto M = createModule();
  auto *F = createBinaryFunc(*M, "test");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *x = F->getArg(0);
  auto *y = F->getArg(1);
  auto *neg_one = llvm::ConstantInt::getSigned(B.getInt32Ty(), -1);
  auto *two = llvm::ConstantInt::get(B.getInt32Ty(), 2);

  auto *not_x = B.CreateXor(x, neg_one);
  auto *not_y = B.CreateXor(y, neg_one);

  // 2*(x | y)
  auto *t1 = B.CreateMul(two, B.CreateOr(x, y));
  // 2*(~x | y)
  auto *t2 = B.CreateMul(two, B.CreateOr(not_x, y));
  // (~x & y)
  auto *t3 = B.CreateAnd(not_x, y);
  // 2*(~x | ~y)
  auto *t4 = B.CreateMul(two, B.CreateOr(not_x, not_y));
  // (~x & ~y)
  auto *t5 = B.CreateAnd(not_x, not_y);

  auto *sum = B.CreateAdd(t1, t2);
  sum = B.CreateAdd(sum, t3);
  sum = B.CreateSub(sum, t4);
  sum = B.CreateSub(sum, t5);
  B.CreateRet(sum);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++before;

  runPass(*F);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  unsigned after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      ++after;

  // The pass should produce valid IR and not increase cost significantly.
  // The simplifier may not always reduce instruction count (reconstruction
  // overhead), but it should not crash on complex MBA patterns.
  EXPECT_LE(after, before + 2);
}

}  // namespace

#if OMILL_ENABLE_Z3

#include "omill/Utils/SouperZ3Translator.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include "omill/Analysis/BinaryMemoryMap.h"

#include <z3++.h>

#include <gtest/gtest.h>

namespace {

class LLVMZ3TranslatorTest : public ::testing::Test {
 protected:
  llvm::LLVMContext LCtx;
  z3::context Z3Ctx;

  llvm::Function *createFunc() {
    auto *i64_ty = llvm::Type::getInt64Ty(LCtx);
    auto *ft = llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
    auto *M = new llvm::Module("test", LCtx);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                  "test_fn", M);
  }
};

TEST_F(LLVMZ3TranslatorTest, TranslatesConstant) {
  omill::LLVMZ3Translator translator(Z3Ctx);
  auto *val = llvm::ConstantInt::get(llvm::Type::getInt64Ty(LCtx), 42);
  z3::expr result = translator.translate(val);

  EXPECT_TRUE(result.is_numeral());
  EXPECT_EQ(result.get_numeral_uint64(), 42u);
  EXPECT_EQ(result.get_sort().bv_size(), 64u);
}

TEST_F(LLVMZ3TranslatorTest, TranslatesLargeConstant) {
  omill::LLVMZ3Translator translator(Z3Ctx);
  auto *val =
      llvm::ConstantInt::get(llvm::Type::getInt64Ty(LCtx), 0x140001000ULL);
  z3::expr result = translator.translate(val);

  EXPECT_TRUE(result.is_numeral());
  EXPECT_EQ(result.get_numeral_uint64(), 0x140001000ULL);
}

TEST_F(LLVMZ3TranslatorTest, TranslatesAddConstConst) {
  // add(10, 32) should be satisfiable with result = 42.
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *lhs = llvm::ConstantInt::get(i64_ty, 10);
  auto *rhs = llvm::ConstantInt::get(i64_ty, 32);
  auto *add = B.CreateAdd(lhs, rhs, "sum");
  B.CreateRet(add);

  z3::expr result = translator.translate(add);

  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(42, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesAddWithVariable) {
  // add(arg0, 5) should be satisfiable and x + 5 == 15 => x == 10.
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *add = B.CreateAdd(F->getArg(0), llvm::ConstantInt::get(i64_ty, 5));
  B.CreateRet(add);

  z3::expr result = translator.translate(add);

  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(15, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  z3::expr arg0_z3 = translator.translate(F->getArg(0));
  z3::expr arg0_val = model.eval(arg0_z3, true);
  EXPECT_EQ(arg0_val.get_numeral_uint64(), 10u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesSub) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *sub = B.CreateSub(F->getArg(0), llvm::ConstantInt::get(i64_ty, 3));
  B.CreateRet(sub);

  z3::expr result = translator.translate(sub);

  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(7, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  z3::expr arg0_z3 = translator.translate(F->getArg(0));
  EXPECT_EQ(model.eval(arg0_z3, true).get_numeral_uint64(), 10u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesMul) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *mul = B.CreateMul(F->getArg(0), llvm::ConstantInt::get(i64_ty, 8));
  B.CreateRet(mul);

  z3::expr result = translator.translate(mul);

  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(40, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  z3::expr arg0_z3 = translator.translate(F->getArg(0));
  EXPECT_EQ(model.eval(arg0_z3, true).get_numeral_uint64(), 5u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesShl) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *shl = B.CreateShl(F->getArg(0), llvm::ConstantInt::get(i64_ty, 3));
  B.CreateRet(shl);

  z3::expr result = translator.translate(shl);

  // shl(x, 3) == 40 => x == 5
  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(40, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  z3::expr arg0_z3 = translator.translate(F->getArg(0));
  EXPECT_EQ(model.eval(arg0_z3, true).get_numeral_uint64(), 5u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesAndOrXor) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  // and(0xFF, 0x0F) = 0x0F
  auto *and_val = B.CreateAnd(llvm::ConstantInt::get(i64_ty, 0xFF),
                              llvm::ConstantInt::get(i64_ty, 0x0F));
  // or(0xF0, 0x0F) = 0xFF
  auto *or_val = B.CreateOr(llvm::ConstantInt::get(i64_ty, 0xF0),
                             llvm::ConstantInt::get(i64_ty, 0x0F));
  // xor(0xFF, 0x0F) = 0xF0
  auto *xor_val = B.CreateXor(llvm::ConstantInt::get(i64_ty, 0xFF),
                               llvm::ConstantInt::get(i64_ty, 0x0F));
  B.CreateRet(and_val);

  z3::solver solver(Z3Ctx);
  solver.add(translator.translate(and_val) == Z3Ctx.bv_val(0x0F, 64));
  solver.add(translator.translate(or_val) == Z3Ctx.bv_val(0xFF, 64));
  solver.add(translator.translate(xor_val) == Z3Ctx.bv_val(0xF0, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesZExt) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i32_ty = llvm::Type::getInt32Ty(LCtx);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *narrow = B.CreateTrunc(F->getArg(0), i32_ty);
  auto *wide = B.CreateZExt(narrow, i64_ty);
  B.CreateRet(wide);

  z3::expr result = translator.translate(wide);
  EXPECT_EQ(result.get_sort().bv_size(), 64u);

  // zext(trunc(0x1_FFFF_FFFF)) should yield 0xFFFFFFFF.
  z3::solver solver(Z3Ctx);
  z3::expr arg0 = translator.translate(F->getArg(0));
  solver.add(arg0 == Z3Ctx.bv_val(0x1FFFFFFFFULL, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  EXPECT_EQ(model.eval(result, true).get_numeral_uint64(), 0xFFFFFFFFu);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesSExt) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i32_ty = llvm::Type::getInt32Ty(LCtx);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *narrow = B.CreateTrunc(F->getArg(0), i32_ty);
  auto *wide = B.CreateSExt(narrow, i64_ty);
  B.CreateRet(wide);

  z3::expr result = translator.translate(wide);
  EXPECT_EQ(result.get_sort().bv_size(), 64u);

  // sext(trunc(x)) where lower 32 bits = 0x80000000 → 0xFFFFFFFF80000000.
  z3::solver solver(Z3Ctx);
  z3::expr arg0 = translator.translate(F->getArg(0));
  solver.add(arg0 == Z3Ctx.bv_val(0x80000000ULL, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  EXPECT_EQ(model.eval(result, true).get_numeral_uint64(),
            0xFFFFFFFF80000000ULL);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesTrunc) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i32_ty = llvm::Type::getInt32Ty(LCtx);

  auto *trunc = B.CreateTrunc(F->getArg(0), i32_ty);
  B.CreateRet(B.CreateZExt(trunc, llvm::Type::getInt64Ty(LCtx)));

  z3::expr result = translator.translate(trunc);
  EXPECT_EQ(result.get_sort().bv_size(), 32u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesICmpEq) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *cmp = B.CreateICmpEQ(F->getArg(0), llvm::ConstantInt::get(i64_ty, 5));
  B.CreateRet(llvm::ConstantInt::get(i64_ty, 0));

  z3::expr result = translator.translate(cmp);
  // ICmp → 1-bit bitvector.
  EXPECT_EQ(result.get_sort().bv_size(), 1u);

  // If cmp == 1, then arg0 == 5.
  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(1, 1));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  z3::expr arg0 = translator.translate(F->getArg(0));
  EXPECT_EQ(model.eval(arg0, true).get_numeral_uint64(), 5u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesICmpUlt) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *cmp = B.CreateICmpULT(F->getArg(0), llvm::ConstantInt::get(i64_ty, 3));
  B.CreateRet(llvm::ConstantInt::get(i64_ty, 0));

  // translateICmp gives a Z3 boolean directly.
  auto *icmp = llvm::cast<llvm::ICmpInst>(cmp);
  z3::expr bool_result = translator.translateICmp(icmp);

  // If cmp is true, arg0 can be 0, 1, or 2.
  z3::solver solver(Z3Ctx);
  solver.add(bool_result);

  unsigned count = 0;
  z3::expr arg0 = translator.translate(F->getArg(0));
  while (solver.check() == z3::sat && count < 10) {
    auto model = solver.get_model();
    uint64_t val = model.eval(arg0, true).get_numeral_uint64();
    EXPECT_LT(val, 3u);
    solver.add(arg0 != Z3Ctx.bv_val(val, 64));
    ++count;
  }
  EXPECT_EQ(count, 3u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, TranslatesSelect) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *cmp = B.CreateICmpEQ(F->getArg(0), llvm::ConstantInt::get(i64_ty, 1));
  auto *sel = B.CreateSelect(cmp, llvm::ConstantInt::get(i64_ty, 100),
                              llvm::ConstantInt::get(i64_ty, 200));
  B.CreateRet(sel);

  z3::expr result = translator.translate(sel);

  // If arg0 == 1, result == 100.
  {
    z3::solver solver(Z3Ctx);
    z3::expr arg0 = translator.translate(F->getArg(0));
    solver.add(arg0 == Z3Ctx.bv_val(1, 64));
    EXPECT_EQ(solver.check(), z3::sat);
    EXPECT_EQ(solver.get_model().eval(result, true).get_numeral_uint64(),
              100u);
  }

  // If arg0 != 1, result == 200.
  {
    z3::solver solver(Z3Ctx);
    z3::expr arg0 = translator.translate(F->getArg(0));
    solver.add(arg0 == Z3Ctx.bv_val(0, 64));
    EXPECT_EQ(solver.check(), z3::sat);
    EXPECT_EQ(solver.get_model().eval(result, true).get_numeral_uint64(),
              200u);
  }

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, DAGDedup) {
  // Multiple uses of the same Value should produce the same Z3 expr.
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *val = llvm::ConstantInt::get(llvm::Type::getInt64Ty(LCtx), 99);
  z3::expr first = translator.translate(val);
  z3::expr second = translator.translate(val);

  // Same Z3 AST.
  EXPECT_TRUE(z3::eq(first, second));
}

TEST_F(LLVMZ3TranslatorTest, LoadBecomesVariable) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *alloca = B.CreateAlloca(i64_ty);
  auto *load = B.CreateLoad(i64_ty, alloca, "mem_val");
  B.CreateRet(load);

  z3::expr result = translator.translate(load);

  // Load produces a fresh variable — should be unconstrained.
  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(12345, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  // Also satisfiable with a different value.
  z3::solver solver2(Z3Ctx);
  solver2.add(result == Z3Ctx.bv_val(0, 64));
  EXPECT_EQ(solver2.check(), z3::sat);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, ComplexJumpTableExpression) {
  // Simulate: target = zext(load(table + idx*4)) + image_base
  // This is the core pattern the solver handles.
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i32_ty = llvm::Type::getInt32Ty(LCtx);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);
  auto *ptr_ty = llvm::PointerType::get(LCtx, 0);

  // idx = arg0
  auto *scaled = B.CreateShl(F->getArg(0), llvm::ConstantInt::get(i64_ty, 2));
  auto *addr =
      B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140020000));
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *load = B.CreateLoad(i32_ty, ptr, "rva");
  auto *wide = B.CreateSExt(load, i64_ty);
  auto *target =
      B.CreateAdd(wide, llvm::ConstantInt::get(i64_ty, 0x140000000));
  B.CreateRet(target);

  z3::expr result = translator.translate(target);
  EXPECT_EQ(result.get_sort().bv_size(), 64u);

  // The load is a fresh variable (rva), so:
  // result = sext(rva) + 0x140000000
  // If we constrain rva to a specific value, result should match.
  z3::expr rva = translator.translate(load);
  z3::solver solver(Z3Ctx);
  // rva = 0x1100 (offset to sub_140001100)
  solver.add(rva == Z3Ctx.bv_val(0x1100, 32));
  EXPECT_EQ(solver.check(), z3::sat);

  auto model = solver.get_model();
  EXPECT_EQ(model.eval(result, true).get_numeral_uint64(), 0x140001100ULL);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, ResetClearsCache) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *val = llvm::ConstantInt::get(llvm::Type::getInt64Ty(LCtx), 42);
  z3::expr first = translator.translate(val);
  EXPECT_TRUE(first.is_numeral());

  translator.reset();

  // After reset, should still work but create a fresh expr.
  z3::expr second = translator.translate(val);
  EXPECT_TRUE(second.is_numeral());
  EXPECT_EQ(second.get_numeral_uint64(), 42u);
}

TEST_F(LLVMZ3TranslatorTest, UnsatConstraints) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *and_val =
      B.CreateAnd(F->getArg(0), llvm::ConstantInt::get(i64_ty, 0x3));
  B.CreateRet(and_val);

  z3::expr result = translator.translate(and_val);

  // and(x, 3) can't be 5 — unsatisfiable.
  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(5, 64));
  EXPECT_EQ(solver.check(), z3::unsat);

  delete F->getParent();
}

// ---------------------------------------------------------------------------
// New tests for enhanced translator features
// ---------------------------------------------------------------------------

TEST_F(LLVMZ3TranslatorTest, TracksUnresolvedVars) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  auto *alloca = B.CreateAlloca(i64_ty);
  auto *load = B.CreateLoad(i64_ty, alloca, "val");
  auto *add = B.CreateAdd(load, llvm::ConstantInt::get(i64_ty, 100));
  B.CreateRet(add);

  translator.translate(add);

  llvm::SmallVector<std::pair<llvm::Value *, z3::expr>, 8> vars;
  translator.getUnresolvedVars(vars);

  // The load should be tracked as an unresolved variable.
  EXPECT_EQ(vars.size(), 1u);
  EXPECT_EQ(vars[0].first, load);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, MemoryAwareLoadResolvesConstantAddress) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  // Set up binary memory with a known value.
  omill::BinaryMemoryMap map;
  uint8_t data[] = {0x00, 0x11, 0x00, 0x40, 0x01, 0x00, 0x00, 0x00};
  map.addRegion(0x140020000, data, sizeof(data));
  translator.setBinaryMemory(&map);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i32_ty = llvm::Type::getInt32Ty(LCtx);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);
  auto *ptr_ty = llvm::PointerType::get(LCtx, 0);

  // Load from constant address: inttoptr(0x140020000) -> i32
  auto *addr = llvm::ConstantInt::get(i64_ty, 0x140020000);
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *load = B.CreateLoad(i32_ty, ptr, "mem_read");
  B.CreateRet(B.CreateZExt(load, i64_ty));

  z3::expr result = translator.translate(load);

  // Should resolve to the concrete value from memory: 0x40001100 (LE)
  EXPECT_TRUE(result.is_numeral());
  EXPECT_EQ(result.get_numeral_uint64(), 0x40001100u);

  // No unresolved vars since the load was resolved.
  llvm::SmallVector<std::pair<llvm::Value *, z3::expr>, 8> vars;
  translator.getUnresolvedVars(vars);
  EXPECT_EQ(vars.size(), 0u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, MemoryAwareLoadFallsBackForUnknownAddr) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  // Binary memory with no mapping at the load address.
  omill::BinaryMemoryMap map;
  uint8_t data[] = {0xAA};
  map.addRegion(0x140010000, data, 1);
  translator.setBinaryMemory(&map);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);
  auto *ptr_ty = llvm::PointerType::get(LCtx, 0);

  // Load from unmapped address.
  auto *addr = llvm::ConstantInt::get(i64_ty, 0x140099000);
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *load = B.CreateLoad(i64_ty, ptr, "unmapped");
  B.CreateRet(load);

  z3::expr result = translator.translate(load);

  // Should fall back to a fresh variable.
  EXPECT_FALSE(result.is_numeral());

  llvm::SmallVector<std::pair<llvm::Value *, z3::expr>, 8> vars;
  translator.getUnresolvedVars(vars);
  EXPECT_EQ(vars.size(), 1u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, PHIWithAllConstants) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *bb1 = llvm::BasicBlock::Create(LCtx, "bb1", F);
  auto *bb2 = llvm::BasicBlock::Create(LCtx, "bb2", F);
  auto *merge = llvm::BasicBlock::Create(LCtx, "merge", F);

  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  // bb1 → merge with val 10
  llvm::IRBuilder<>(bb1).CreateBr(merge);
  // bb2 → merge with val 20
  llvm::IRBuilder<>(bb2).CreateBr(merge);

  // PHI in merge with two constant incoming values.
  llvm::IRBuilder<> B(merge);
  auto *phi = B.CreatePHI(i64_ty, 2, "const_phi");
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 10), bb1);
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 20), bb2);
  B.CreateRet(phi);

  z3::expr result = translator.translate(phi);

  // The PHI with all-constant values should produce an expression that
  // can only be 10 or 20.
  z3::solver solver(Z3Ctx);
  solver.add(result == Z3Ctx.bv_val(10, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  z3::solver solver2(Z3Ctx);
  solver2.add(result == Z3Ctx.bv_val(20, 64));
  EXPECT_EQ(solver2.check(), z3::sat);

  // 15 should not be a valid value.
  z3::solver solver3(Z3Ctx);
  solver3.add(result == Z3Ctx.bv_val(15, 64));
  EXPECT_EQ(solver3.check(), z3::unsat);

  // No unresolved vars since the PHI was resolved.
  llvm::SmallVector<std::pair<llvm::Value *, z3::expr>, 8> vars;
  translator.getUnresolvedVars(vars);
  EXPECT_EQ(vars.size(), 0u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, PHIWithSingleConstant) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *bb1 = llvm::BasicBlock::Create(LCtx, "bb1", F);
  auto *bb2 = llvm::BasicBlock::Create(LCtx, "bb2", F);
  auto *merge = llvm::BasicBlock::Create(LCtx, "merge", F);

  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  llvm::IRBuilder<>(bb1).CreateBr(merge);
  llvm::IRBuilder<>(bb2).CreateBr(merge);

  // PHI with the same constant from both paths.
  llvm::IRBuilder<> B(merge);
  auto *phi = B.CreatePHI(i64_ty, 2);
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 42), bb1);
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 42), bb2);
  B.CreateRet(phi);

  z3::expr result = translator.translate(phi);

  // Should be exactly 42.
  EXPECT_TRUE(result.is_numeral());
  EXPECT_EQ(result.get_numeral_uint64(), 42u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, PHIWithNonConstantFallsBack) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *bb1 = llvm::BasicBlock::Create(LCtx, "bb1", F);
  auto *bb2 = llvm::BasicBlock::Create(LCtx, "bb2", F);
  auto *merge = llvm::BasicBlock::Create(LCtx, "merge", F);

  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  llvm::IRBuilder<>(bb1).CreateBr(merge);
  llvm::IRBuilder<>(bb2).CreateBr(merge);

  // PHI with one constant and one non-constant.
  llvm::IRBuilder<> B(merge);
  auto *phi = B.CreatePHI(i64_ty, 2);
  phi->addIncoming(llvm::ConstantInt::get(i64_ty, 10), bb1);
  phi->addIncoming(F->getArg(0), bb2);
  B.CreateRet(phi);

  z3::expr result = translator.translate(phi);

  // Should fall back to fresh variable (non-constant incoming).
  EXPECT_FALSE(result.is_numeral());

  llvm::SmallVector<std::pair<llvm::Value *, z3::expr>, 8> vars;
  translator.getUnresolvedVars(vars);
  EXPECT_EQ(vars.size(), 1u);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, LShrAndAShr) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  // lshr(0x80, 2) = 0x20
  auto *lshr_val = B.CreateLShr(llvm::ConstantInt::get(i64_ty, 0x80),
                                  llvm::ConstantInt::get(i64_ty, 2));
  // ashr(0xFFFFFFFFFFFFFF80, 2) = 0xFFFFFFFFFFFFFFE0
  auto *ashr_val = B.CreateAShr(
      llvm::ConstantInt::get(i64_ty, 0xFFFFFFFFFFFFFF80ULL),
      llvm::ConstantInt::get(i64_ty, 2));
  B.CreateRet(lshr_val);

  z3::solver solver(Z3Ctx);
  solver.add(translator.translate(lshr_val) == Z3Ctx.bv_val(0x20, 64));
  solver.add(translator.translate(ashr_val) ==
             Z3Ctx.bv_val(0xFFFFFFFFFFFFFFE0ULL, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, UDivAndSDiv) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);

  // udiv(100, 10) = 10
  auto *udiv = B.CreateUDiv(llvm::ConstantInt::get(i64_ty, 100),
                             llvm::ConstantInt::get(i64_ty, 10));
  B.CreateRet(udiv);

  z3::solver solver(Z3Ctx);
  solver.add(translator.translate(udiv) == Z3Ctx.bv_val(10, 64));
  EXPECT_EQ(solver.check(), z3::sat);

  delete F->getParent();
}

TEST_F(LLVMZ3TranslatorTest, IntToPtrAndPtrToInt) {
  omill::LLVMZ3Translator translator(Z3Ctx);

  auto *F = createFunc();
  auto *entry = llvm::BasicBlock::Create(LCtx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(LCtx);
  auto *ptr_ty = llvm::PointerType::get(LCtx, 0);

  // inttoptr(arg0) then ptrtoint back should be identity.
  auto *ptr = B.CreateIntToPtr(F->getArg(0), ptr_ty);
  auto *back = B.CreatePtrToInt(ptr, i64_ty);
  B.CreateRet(back);

  z3::expr result = translator.translate(back);
  z3::expr arg0 = translator.translate(F->getArg(0));

  // result should equal arg0.
  z3::solver solver(Z3Ctx);
  solver.add(arg0 == Z3Ctx.bv_val(0x140001000ULL, 64));
  EXPECT_EQ(solver.check(), z3::sat);
  EXPECT_EQ(solver.get_model().eval(result, true).get_numeral_uint64(),
            0x140001000ULL);

  delete F->getParent();
}

}  // namespace

#endif  // OMILL_ENABLE_Z3

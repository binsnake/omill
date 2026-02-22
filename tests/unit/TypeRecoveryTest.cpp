#include "omill/Passes/TypeRecovery.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class TypeRecoveryTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a function that takes a pointer and returns i64.
  struct TestModule {
    std::unique_ptr<llvm::Module> M;
    llvm::Function *F = nullptr;
    llvm::BasicBlock *entry = nullptr;
  };

  TestModule createTestModule() {
    TestModule tm;
    tm.M = std::make_unique<llvm::Module>("test", Ctx);
    tm.M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

    auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty}, false);
    tm.F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                  "test_func", *tm.M);
    tm.entry = llvm::BasicBlock::Create(Ctx, "entry", tm.F);
    return tm;
  }

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::TypeRecoveryPass());
    llvm::FunctionAnalysisManager FAM;
    llvm::LoopAnalysisManager LAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    llvm::PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    FPM.run(*F, FAM);
  }

  unsigned countInsts(llvm::Function *F, unsigned opcode) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (I.getOpcode() == opcode)
          ++count;
    return count;
  }

  unsigned countIntToPtr(llvm::Function *F) {
    return countInsts(F, llvm::Instruction::IntToPtr);
  }

  unsigned countPtrToInt(llvm::Function *F) {
    return countInsts(F, llvm::Instruction::PtrToInt);
  }

  unsigned countGEPs(llvm::Function *F) {
    return countInsts(F, llvm::Instruction::GetElementPtr);
  }
};

// ===----------------------------------------------------------------------===
// Test 1: inttoptr(ptrtoint(p)) → p
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, IntToPtrOfPtrToInt_Folded) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  auto *itp = B.CreateIntToPtr(pti, llvm::PointerType::get(Ctx, 0));
  auto *load = B.CreateLoad(B.getInt64Ty(), itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 1u);

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
}

// ===----------------------------------------------------------------------===
// Test 2: ptrtoint(inttoptr(x)) → x
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, PtrToIntOfIntToPtr_Folded) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  // Function takes i64 so inttoptr won't be constant-folded.
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test_pti", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *x = F->getArg(0);  // i64 param
  auto *itp = B.CreateIntToPtr(x, ptr_ty);
  auto *pti = B.CreatePtrToInt(itp, i64_ty);
  B.CreateRet(pti);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  EXPECT_EQ(countPtrToInt(F), 1u);

  runPass(F);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  EXPECT_EQ(countPtrToInt(F), 0u);
}

// ===----------------------------------------------------------------------===
// Test 3: inttoptr(add(ptrtoint(p), 8)) → GEP i8, p, 8
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, IntToPtrOfAddPtrToIntConst_BecomesGEP) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  auto *add = B.CreateAdd(pti, B.getInt64(8));
  auto *itp = B.CreateIntToPtr(add, llvm::PointerType::get(Ctx, 0));
  auto *load = B.CreateLoad(B.getInt64Ty(), itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 1u);
  EXPECT_EQ(countGEPs(tm.F), 0u);

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
  EXPECT_GE(countGEPs(tm.F), 1u);
}

// ===----------------------------------------------------------------------===
// Test 4: inttoptr(sub(ptrtoint(p), 16)) → GEP i8, p, -16
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, IntToPtrOfSubPtrToIntConst_BecomesGEP) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  auto *sub = B.CreateSub(pti, B.getInt64(16));
  auto *itp = B.CreateIntToPtr(sub, llvm::PointerType::get(Ctx, 0));
  auto *load = B.CreateLoad(B.getInt64Ty(), itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 1u);

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
  EXPECT_GE(countGEPs(tm.F), 1u);
}

// ===----------------------------------------------------------------------===
// Test 5: Chained add: inttoptr(add(add(ptrtoint(p), 8), 16)) → GEP p, 24
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, ChainedAddPtrToInt_BecomesGEP) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  auto *add1 = B.CreateAdd(pti, B.getInt64(8));
  auto *add2 = B.CreateAdd(add1, B.getInt64(16));
  auto *itp = B.CreateIntToPtr(add2, llvm::PointerType::get(Ctx, 0));
  auto *load = B.CreateLoad(B.getInt64Ty(), itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 1u);

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
  EXPECT_GE(countGEPs(tm.F), 1u);
}

// ===----------------------------------------------------------------------===
// Test 6: inttoptr(constant) — NOT a pointer recovery target, preserved
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, IntToPtrOfPlainInteger_Preserved) {
  // Function takes i64 so inttoptr won't be constant-folded.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                   "test_plain", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  // inttoptr of a plain integer (no ptrtoint origin) — should be preserved.
  auto *itp = B.CreateIntToPtr(F->getArg(0), ptr_ty);
  auto *load = B.CreateLoad(i64_ty, itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(F), 1u);

  runPass(F);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // inttoptr of plain integer (not from ptrtoint) is not a recovery target.
  EXPECT_EQ(countIntToPtr(F), 1u);
}

// ===----------------------------------------------------------------------===
// Test 7: inttoptr(add(ptrtoint(p), 0)) → p (zero offset = identity)
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, IntToPtrOfAddZero_FoldsToIdentity) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  auto *add = B.CreateAdd(pti, B.getInt64(0));
  auto *itp = B.CreateIntToPtr(add, llvm::PointerType::get(Ctx, 0));
  auto *load = B.CreateLoad(B.getInt64Ty(), itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
  // Zero offset → no GEP needed, just use original pointer.
  EXPECT_EQ(countGEPs(tm.F), 0u);
}

// ===----------------------------------------------------------------------===
// Test 8: Declaration function → no-op
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, DeclarationFunction_Skipped) {
  auto tm = createTestModule();
  // Replace F with a declaration.
  tm.F->deleteBody();

  // Should not crash.
  runPass(tm.F);
}

// ===----------------------------------------------------------------------===
// Test 9: Multiple inttoptr from same ptrtoint base with different offsets
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, MultipleDerivedPointers_AllRecovered) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  auto *add8 = B.CreateAdd(pti, B.getInt64(8));
  auto *itp8 = B.CreateIntToPtr(add8, llvm::PointerType::get(Ctx, 0));
  auto *add16 = B.CreateAdd(pti, B.getInt64(16));
  auto *itp16 = B.CreateIntToPtr(add16, llvm::PointerType::get(Ctx, 0));
  auto *v1 = B.CreateLoad(B.getInt64Ty(), itp8);
  auto *v2 = B.CreateLoad(B.getInt64Ty(), itp16);
  auto *sum = B.CreateAdd(v1, v2);
  B.CreateRet(sum);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 2u);

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
  EXPECT_EQ(countGEPs(tm.F), 2u);
}

// ===----------------------------------------------------------------------===
// Test 10: inttoptr(add(const, ptrtoint(p))) — commuted operands
// ===----------------------------------------------------------------------===

TEST_F(TypeRecoveryTest, CommutedAddOperands_StillRecovered) {
  auto tm = createTestModule();
  llvm::IRBuilder<> B(tm.entry);
  auto *ptr = tm.F->getArg(0);

  auto *pti = B.CreatePtrToInt(ptr, B.getInt64Ty());
  // add with constant on LHS.
  auto *add = B.CreateAdd(B.getInt64(32), pti);
  auto *itp = B.CreateIntToPtr(add, llvm::PointerType::get(Ctx, 0));
  auto *load = B.CreateLoad(B.getInt64Ty(), itp);
  B.CreateRet(load);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));

  runPass(tm.F);

  ASSERT_FALSE(llvm::verifyModule(*tm.M, &llvm::errs()));
  EXPECT_EQ(countIntToPtr(tm.F), 0u);
  EXPECT_GE(countGEPs(tm.F), 1u);
}

}  // namespace

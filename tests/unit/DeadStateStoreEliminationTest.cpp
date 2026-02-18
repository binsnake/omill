#include "omill/Passes/OptimizeState.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class DeadStateStoreEliminationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a State struct and a function that has redundant
  /// stores to the same State field (offset 0).
  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Lifted function: (State*, i64, Memory*) -> Memory*
    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *mem = test_fn->getArg(2);

    // GEP to State offset 0 (e.g. first register)
    auto *gep0 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0, "reg_ptr");

    // Store 42 to offset 0 — this should be dead (overwritten below).
    B.CreateStore(B.getInt64(42), gep0);

    // Store 99 to offset 0 — overwrites the previous store.
    B.CreateStore(B.getInt64(99), gep0);

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(DeadStateStoreEliminationTest, EliminatesOverwrittenStore) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Count stores before.
  unsigned stores_before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_before++;
  EXPECT_EQ(stores_before, 2u);

  // Run the pass.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::OptimizeStatePass(omill::OptimizePhases::DeadStores));

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

  FPM.run(*F, FAM);

  // Count stores after — should have eliminated 1.
  unsigned stores_after = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;
  EXPECT_EQ(stores_after, 1u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(DeadStateStoreEliminationTest, PreservesStoreBeforeLoad) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  auto *gep0 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0, "reg_ptr");

  // Store, then load, then store — both stores should be preserved.
  B.CreateStore(B.getInt64(42), gep0);
  auto *val = B.CreateLoad(i64_ty, gep0, "val");
  auto *val2 = B.CreateAdd(val, B.getInt64(1));
  B.CreateStore(val2, gep0);

  B.CreateRet(mem);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::OptimizeStatePass(omill::OptimizePhases::DeadStores));

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

  FPM.run(*test_fn, FAM);

  unsigned stores_after = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;
  EXPECT_EQ(stores_after, 2u);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

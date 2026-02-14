#include "omill/Passes/PromoteStateToSSA.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/Scalar/SROA.h>

#include <gtest/gtest.h>

namespace {

class PromoteStateToSSATest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a function that loads a State field, adds 1, stores back.
  std::unique_ptr<llvm::Module> createTestModule() {
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

    // Load from State offset 16 (simulating a register like RBX)
    auto *gep_load = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "rbx_ptr");
    auto *val = B.CreateLoad(i64_ty, gep_load, "rbx_val");

    // val + 1
    auto *val2 = B.CreateAdd(val, B.getInt64(1), "inc");

    // Store back to State offset 16
    auto *gep_store = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "rbx_ptr2");
    B.CreateStore(val2, gep_store);

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(PromoteStateToSSATest, CreatesAllocasForStateFields) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Before: no allocas
  unsigned allocas_before = 0;
  for (auto &I : F->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      allocas_before++;
  EXPECT_EQ(allocas_before, 0u);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());

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

  // After: should have at least one alloca for the state field
  unsigned allocas_after = 0;
  for (auto &I : F->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      allocas_after++;
  EXPECT_GE(allocas_after, 1u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(PromoteStateToSSATest, SROAPromotesToSSA) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Run PromoteStateToSSA then SROA.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));

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

  // After SROA, the alloca should be promoted — no allocas remaining.
  unsigned allocas_after = 0;
  for (auto &I : F->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      allocas_after++;
  EXPECT_EQ(allocas_after, 0u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

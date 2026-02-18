#include "omill/Utils/TranslationValidator.h"

#include "omill/Passes/OptimizeState.h"
#include "omill/Passes/MemoryPointerElimination.h"
#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

#if OMILL_ENABLE_Z3

namespace {

class TranslationValidationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  z3::context Z3Ctx;

  void setupAnalyses(llvm::PassBuilder &PB, llvm::LoopAnalysisManager &LAM,
                      llvm::FunctionAnalysisManager &FAM,
                      llvm::CGSCCAnalysisManager &CGAM,
                      llvm::ModuleAnalysisManager &MAM) {
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
  }

  /// Create a simple function that loads from State, computes, stores back.
  std::unique_ptr<llvm::Module> createSimpleModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    auto *fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *mem = test_fn->getArg(2);

    // Load from offset 16, add 1, store to offset 8.
    auto *gep_load = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    auto *val = B.CreateLoad(i64_ty, gep_load, "rbx_val");
    auto *inc = B.CreateAdd(val, B.getInt64(1), "inc");
    auto *gep_store = B.CreateConstGEP1_64(B.getInt8Ty(), state, 8);
    B.CreateStore(inc, gep_store);

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(TranslationValidationTest, DeadStoreEliminationPreservesSemantics) {
  // Dead store elimination should be semantics-preserving.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Dead store: store 42, then overwrite with 99.
  auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
  B.CreateStore(B.getInt64(42), gep);
  B.CreateStore(B.getInt64(99), gep);
  B.CreateRet(mem);

  // Snapshot before pass.
  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*test_fn);

  // Run the pass.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::OptimizeStatePass(omill::OptimizePhases::DeadStores));

  llvm::PassBuilder PB;
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;
  setupAnalyses(PB, LAM, FAM, CGAM, MAM);
  FPM.run(*test_fn, FAM);

  // Verify semantic equivalence.
  auto result = validator.verify(*test_fn);
  EXPECT_TRUE(result.equivalent)
      << "Counterexample: " << result.counterexample;
}

TEST_F(TranslationValidationTest, IdentityTransformEquivalent) {
  // No pass → snapshot and verify should be equivalent (sanity check).
  auto M = createSimpleModule();
  auto *test_fn = M->getFunction("test_func");

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*test_fn);

  // No pass run — function is unchanged.
  auto result = validator.verify(*test_fn);
  EXPECT_TRUE(result.equivalent)
      << "Identity should be equivalent: " << result.counterexample;
}

TEST_F(TranslationValidationTest, IntentionalBugDetected) {
  // Intentionally break the function and verify the validator catches it.
  auto M = createSimpleModule();
  auto *test_fn = M->getFunction("test_func");

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*test_fn);

  // Modify the function: change the add constant from 1 to 2.
  for (auto &I : test_fn->getEntryBlock()) {
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
      if (BO->getOpcode() == llvm::Instruction::Add) {
        BO->setOperand(1, llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(Ctx), 2));
        break;
      }
    }
  }

  auto result = validator.verify(*test_fn);
  EXPECT_FALSE(result.equivalent)
      << "Modified function should NOT be equivalent";
  EXPECT_FALSE(result.counterexample.empty());
}

TEST_F(TranslationValidationTest, RemoveBarriersPreservesSemantics) {
  // Barrier removal should not change data flow.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  // Create __remill_barrier_store_load as volatile inline asm.
  auto *barrier_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
  auto *barrier_fn = llvm::Function::Create(
      barrier_fn_ty, llvm::Function::ExternalLinkage,
      "__remill_barrier_store_load", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Store to State+0.
  auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
  B.CreateStore(B.getInt64(42), gep);

  // Barrier call (will be removed).
  B.CreateCall(barrier_fn, {mem});

  // Load from State+0.
  auto *val = B.CreateLoad(i64_ty, gep, "val");

  // Store to State+8.
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 8);
  B.CreateStore(val, gep2);

  B.CreateRet(mem);

  omill::TranslationValidator validator(Z3Ctx);
  validator.snapshotBefore(*test_fn);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Barriers));

  llvm::PassBuilder PB;
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;
  setupAnalyses(PB, LAM, FAM, CGAM, MAM);
  FPM.run(*test_fn, FAM);

  auto result = validator.verify(*test_fn);
  EXPECT_TRUE(result.equivalent)
      << "Barrier removal counterexample: " << result.counterexample;
}

}  // namespace

#endif  // OMILL_ENABLE_Z3

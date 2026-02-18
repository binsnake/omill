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

class DeadStateFlagEliminationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::OptimizeStatePass(omill::OptimizePhases::DeadFlags));

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
  }

  /// Create a module with __remill_basic_block defining flag fields.
  std::unique_ptr<llvm::Module> createModuleWithFlags() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Create __remill_basic_block to register flag field names
    auto *bb_fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block",
        *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);

    auto *bb_state = bb_fn->getArg(0);
    // Register flag fields. ZF is at offset 200, CF at 201.
    BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 200, "ZF");
    BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 201, "CF");
    BBB.CreateRet(bb_fn->getArg(2));

    return M;
  }
};

TEST_F(DeadStateFlagEliminationTest, ConsecutiveFlagStoresKillsFirst) {
  auto M = createModuleWithFlags();

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
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

  // GEP to ZF at offset 200
  auto *zf_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state, 200, "zf_ptr");

  // First store to ZF (should be dead — overwritten below)
  B.CreateStore(B.getInt8(1), zf_ptr);

  // Second store to ZF (overwrites first)
  B.CreateStore(B.getInt8(0), zf_ptr);

  B.CreateRet(mem);

  // Count stores before
  unsigned stores_before = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_before++;
  EXPECT_EQ(stores_before, 2u);

  runPass(test_fn);

  // Count stores after — first should be eliminated
  unsigned stores_after = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;
  EXPECT_EQ(stores_after, 1u);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(DeadStateFlagEliminationTest, FlagStoreBeforeLoadPreserved) {
  auto M = createModuleWithFlags();

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
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

  auto *zf_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state, 200, "zf_ptr");

  // Store → Load → Store: both stores must be preserved
  B.CreateStore(B.getInt8(1), zf_ptr);
  auto *val = B.CreateLoad(i8_ty, zf_ptr, "zf_val");
  (void)val;
  B.CreateStore(B.getInt8(0), zf_ptr);

  B.CreateRet(mem);

  runPass(test_fn);

  unsigned stores_after = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;
  EXPECT_EQ(stores_after, 2u);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

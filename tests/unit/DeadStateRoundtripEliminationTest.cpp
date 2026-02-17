#include "omill/Passes/DeadStateRoundtripElimination.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class DeadStateRoundtripEliminationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::DeadStateRoundtripEliminationPass());

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

    FPM.run(F, FAM);
  }
};

TEST_F(DeadStateRoundtripEliminationTest, LoadStoreRoundtripRemoved) {
  // Pattern: store %val to State+offset, call, load from State+offset,
  // store back to same offset → load+store are dead roundtrip.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  // Create a callee declaration.
  auto *callee = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Flush: store value to State+2216 (RAX offset)
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);

  // Call that takes State
  auto *call1 = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Roundtrip: load from State+2216, store back immediately
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  auto *reloaded = B.CreateLoad(i64_ty, gep2, "reloaded");
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr3");
  B.CreateStore(reloaded, gep3);

  // Second call
  auto *call2 = B.CreateCall(callee, {state, B.getInt64(0), call1});
  B.CreateRet(call2);

  // Count stores before.
  unsigned stores_before = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_before++;

  runPass(*test_fn);

  // The roundtrip load+store should be removed.
  unsigned stores_after = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;

  EXPECT_LT(stores_after, stores_before);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(DeadStateRoundtripEliminationTest, ModifiedValuePreserved) {
  // load from State → modify → store back: NOT a dead roundtrip.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *callee = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Flush
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);

  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Load, modify, then store — not a roundtrip.
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  auto *loaded = B.CreateLoad(i64_ty, gep2, "loaded");
  auto *modified = B.CreateAdd(loaded, B.getInt64(1), "modified");
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr3");
  B.CreateStore(modified, gep3);

  B.CreateRet(call);

  unsigned stores_before = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_before++;

  runPass(*test_fn);

  unsigned stores_after = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;

  // Both stores should be preserved — the value was modified.
  EXPECT_EQ(stores_after, stores_before);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(DeadStateRoundtripEliminationTest, CrossBlockRoundtripPreserved) {
  // Load and store in different blocks — should be preserved.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *callee = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *cont = llvm::BasicBlock::Create(Ctx, "cont", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Load in entry block
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  auto *loaded = B.CreateLoad(i64_ty, gep2, "loaded");
  B.CreateBr(cont);

  // Store in continuation block
  B.SetInsertPoint(cont);
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr3");
  B.CreateStore(loaded, gep3);
  B.CreateRet(call);

  unsigned stores_before = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_before++;

  runPass(*test_fn);

  unsigned stores_after = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::StoreInst>(&I))
        stores_after++;

  // Cross-block roundtrips should be preserved.
  EXPECT_EQ(stores_after, stores_before);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

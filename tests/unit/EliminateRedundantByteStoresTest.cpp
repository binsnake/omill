#include "omill/Passes/EliminateRedundantByteStores.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class EliminateRedundantByteStoresTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::EliminateRedundantByteStoresPass());

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

TEST_F(EliminateRedundantByteStoresTest, RedundantByteStoreRemoved) {
  // An i64 store at offset 464 followed by an i8 store of 0 at offset 465
  // should be eliminated if the byte is the same.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Wide store: i64 0 at offset 464
  auto *gep_wide = B.CreateConstGEP1_64(B.getInt8Ty(), state, 464, "wide_ptr");
  B.CreateStore(B.getInt64(0), gep_wide);

  // Narrow store: i8 0 at offset 465 — redundant (byte 1 of the i64 zero)
  auto *gep_narrow = B.CreateConstGEP1_64(B.getInt8Ty(), state, 465, "narrow_ptr");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, 0), gep_narrow);

  B.CreateRet(mem);

  unsigned stores_before = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (llvm::isa<llvm::StoreInst>(&I))
      stores_before++;
  EXPECT_EQ(stores_before, 2u);

  runPass(*test_fn);

  unsigned stores_after = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (llvm::isa<llvm::StoreInst>(&I))
      stores_after++;

  // The narrow store should be removed.
  EXPECT_EQ(stores_after, 1u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(EliminateRedundantByteStoresTest, NonOverlappingPreserved) {
  // Stores to non-overlapping offsets should both be preserved.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Store i64 at offset 464
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 464, "ptr1");
  B.CreateStore(B.getInt64(0), gep1);

  // Store i8 at offset 500 — not overlapping with 464..471
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 500, "ptr2");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, 42), gep2);

  B.CreateRet(mem);

  runPass(*test_fn);

  unsigned stores_after = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (llvm::isa<llvm::StoreInst>(&I))
      stores_after++;

  EXPECT_EQ(stores_after, 2u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

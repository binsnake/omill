#include "omill/Passes/OutlineConstantStackData.h"

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

class OutlineConstantStackDataTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::OutlineConstantStackDataPass());

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

  unsigned countAllocas(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (llvm::isa<llvm::AllocaInst>(&I))
          count++;
    return count;
  }

  unsigned countGlobals(llvm::Module *M, llvm::StringRef prefix) {
    unsigned count = 0;
    for (auto &GV : M->globals())
      if (GV.getName().starts_with(prefix))
        count++;
    return count;
  }
};

TEST_F(OutlineConstantStackDataTest, PromotesConstantAlloca) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  // Create an alloca with two constant stores.
  auto *alloca = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 8));
  B.CreateStore(B.getInt32(0x41424344), alloca);  // "DCBA"
  auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 4);
  B.CreateStore(B.getInt32(0x45464748), gep);  // "HGFE"

  // Load from alloca to keep it alive.
  auto *val = B.CreateLoad(i64_ty, alloca);
  B.CreateRet(val);

  EXPECT_EQ(countAllocas(F), 1u);
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 0u);

  runPass(F);

  EXPECT_EQ(countAllocas(F), 0u);
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(OutlineConstantStackDataTest, OverlappingStoresLastWins) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 4));
  B.CreateStore(B.getInt32(0xAAAAAAAA), alloca);
  B.CreateStore(B.getInt32(0xBBBBBBBB), alloca);  // overwrites

  auto *val = B.CreateLoad(i32_ty, alloca);
  B.CreateRet(val);

  runPass(F);

  // Should be promoted; the second store wins.
  EXPECT_EQ(countAllocas(F), 0u);
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 1u);

  // Verify the global content is from the second store.
  for (auto &GV : M->globals()) {
    if (GV.getName().starts_with(".const_stack")) {
      auto *init = llvm::dyn_cast<llvm::ConstantDataArray>(GV.getInitializer());
      ASSERT_NE(init, nullptr);
      // Little-endian 0xBBBBBBBB = [BB, BB, BB, BB]
      auto raw = init->getRawDataValues();
      EXPECT_EQ(static_cast<uint8_t>(raw[0]), 0xBB);
      EXPECT_EQ(static_cast<uint8_t>(raw[1]), 0xBB);
    }
  }

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(OutlineConstantStackDataTest, RejectsNonConstantStore) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(i32_ty);
  B.CreateStore(F->getArg(0), alloca);  // non-constant!

  auto *val = B.CreateLoad(i32_ty, alloca);
  B.CreateRet(val);

  runPass(F);

  // Should NOT be promoted.
  EXPECT_EQ(countAllocas(F), 1u);
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 0u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(OutlineConstantStackDataTest, RejectsEscapingAlloca) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(i32_ty);
  B.CreateStore(B.getInt32(42), alloca);

  // Store the alloca pointer somewhere (it escapes).
  auto *escape = B.CreateAlloca(ptr_ty);
  B.CreateStore(alloca, escape);

  auto *val = B.CreateLoad(i32_ty, alloca);
  B.CreateRet(val);

  runPass(F);

  // Should NOT be promoted because the pointer escapes.
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 0u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(OutlineConstantStackDataTest, RejectsNonEntryStore) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *other = llvm::BasicBlock::Create(Ctx, "other", F);

  {
    llvm::IRBuilder<> B(entry);
    B.CreateBr(other);
  }

  llvm::IRBuilder<> B(other);
  auto *alloca =
      llvm::IRBuilder<>(&F->getEntryBlock().front())
          .CreateAlloca(i32_ty);
  B.CreateStore(B.getInt32(42), alloca);  // store in non-entry block!

  auto *val = B.CreateLoad(i32_ty, alloca);
  B.CreateRet(val);

  runPass(F);

  // Should NOT be promoted — store is not in entry block.
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 0u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(OutlineConstantStackDataTest, AllowsPtrToIntUser) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(i32_ty);
  B.CreateStore(B.getInt32(0xDEADBEEF), alloca);

  // ptrtoint is allowed (xorstr decryption loop uses this).
  auto *ptr_as_int = B.CreatePtrToInt(alloca, i64_ty);
  B.CreateRet(ptr_as_int);

  runPass(F);

  EXPECT_EQ(countAllocas(F), 0u);
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(OutlineConstantStackDataTest, AllowsGEPChain) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 16));

  // Store through GEP chain: offset 0
  B.CreateStore(B.getInt32(0x11223344), alloca);
  // Store through GEP chain: offset 4
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 4);
  B.CreateStore(B.getInt32(0x55667788), gep1);
  // Store through nested GEP chain: offset 8
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 8);
  B.CreateStore(B.getInt32(0x99AABBCC), gep2);

  auto *val = B.CreateLoad(i32_ty, alloca);
  B.CreateRet(val);

  runPass(F);

  EXPECT_EQ(countAllocas(F), 0u);
  EXPECT_EQ(countGlobals(M.get(), ".const_stack"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

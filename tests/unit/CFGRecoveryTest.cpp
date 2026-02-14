#include "omill/Passes/CFGRecovery.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class CFGRecoveryTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
};

TEST_F(CFGRecoveryTest, MergesSingleSuccessorChain) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Create a chain: entry -> bb1 -> bb2 -> exit (all unconditional)
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *bb1 = llvm::BasicBlock::Create(Ctx, "bb1", test_fn);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "bb2", test_fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", test_fn);

  // entry: store to State, br bb1
  {
    llvm::IRBuilder<> B(entry);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(1), gep);
    B.CreateBr(bb1);
  }

  // bb1: store to State, br bb2
  {
    llvm::IRBuilder<> B(bb1);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 8);
    B.CreateStore(B.getInt64(2), gep);
    B.CreateBr(bb2);
  }

  // bb2: store to State, br exit
  {
    llvm::IRBuilder<> B(bb2);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    B.CreateStore(B.getInt64(3), gep);
    B.CreateBr(exit_bb);
  }

  // exit: ret
  {
    llvm::IRBuilder<> B(exit_bb);
    B.CreateRet(mem);
  }

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));

  unsigned bb_count_before = test_fn->size();
  EXPECT_EQ(bb_count_before, 4u);

  // Run CFGRecovery.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::CFGRecoveryPass());

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

  // After: the chain should have been merged. Fewer blocks.
  unsigned bb_count_after = test_fn->size();
  EXPECT_LT(bb_count_after, bb_count_before);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CFGRecoveryTest, RemovesUnreachableBlocks) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *mem = test_fn->getArg(2);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *unreachable_bb = llvm::BasicBlock::Create(Ctx, "dead", test_fn);

  // entry: ret
  {
    llvm::IRBuilder<> B(entry);
    B.CreateRet(mem);
  }

  // dead: unreachable (no predecessors)
  {
    llvm::IRBuilder<> B(unreachable_bb);
    B.CreateUnreachable();
  }

  EXPECT_EQ(test_fn->size(), 2u);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::CFGRecoveryPass());

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

  EXPECT_EQ(test_fn->size(), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

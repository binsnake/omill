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

TEST_F(CFGRecoveryTest, FoldsConstantBranch) {
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

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "true_bb", test_fn);
  auto *false_bb = llvm::BasicBlock::Create(Ctx, "false_bb", test_fn);

  // entry: br i1 true, true_bb, false_bb
  {
    llvm::IRBuilder<> B(entry);
    B.CreateCondBr(B.getTrue(), true_bb, false_bb);
  }

  // true_bb: store + ret
  {
    llvm::IRBuilder<> B(true_bb);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(42), gep);
    B.CreateRet(mem);
  }

  // false_bb: ret
  {
    llvm::IRBuilder<> B(false_bb);
    B.CreateRet(mem);
  }

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
  EXPECT_EQ(test_fn->size(), 3u);

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

  // The constant-true branch should be folded. false_bb becomes unreachable
  // and will be removed on the next unreachable pass iteration (or stays if
  // the pass doesn't re-run). At minimum, entry should now have unconditional br.
  auto *term = test_fn->getEntryBlock().getTerminator();
  auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
  ASSERT_NE(br, nullptr);
  EXPECT_TRUE(br->isUnconditional());
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CFGRecoveryTest, EliminatesEmptyForwarder) {
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

  // entry -> forwarder -> exit, where forwarder is empty (just br)
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *forwarder = llvm::BasicBlock::Create(Ctx, "forwarder", test_fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", test_fn);

  // entry: store + br forwarder
  {
    llvm::IRBuilder<> B(entry);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(1), gep);
    B.CreateBr(forwarder);
  }

  // forwarder: br exit (empty — no real instructions)
  {
    llvm::IRBuilder<> B(forwarder);
    B.CreateBr(exit_bb);
  }

  // exit: ret
  {
    llvm::IRBuilder<> B(exit_bb);
    B.CreateRet(mem);
  }

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
  EXPECT_EQ(test_fn->size(), 3u);

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

  // forwarder should be merged away since it has single pred/single succ
  EXPECT_LT(test_fn->size(), 3u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CFGRecoveryTest, DiamondCFG_Preserved) {
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
  auto *pc = test_fn->getArg(1);
  auto *mem = test_fn->getArg(2);

  // Diamond: entry -> {left, right} -> merge -> ret
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *left = llvm::BasicBlock::Create(Ctx, "left", test_fn);
  auto *right = llvm::BasicBlock::Create(Ctx, "right", test_fn);
  auto *merge = llvm::BasicBlock::Create(Ctx, "merge", test_fn);

  // entry: cond br on runtime value
  {
    llvm::IRBuilder<> B(entry);
    auto *cmp = B.CreateICmpEQ(pc, B.getInt64(0x1000));
    B.CreateCondBr(cmp, left, right);
  }

  // left: store, br merge
  {
    llvm::IRBuilder<> B(left);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(1), gep);
    B.CreateBr(merge);
  }

  // right: store, br merge
  {
    llvm::IRBuilder<> B(right);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 8);
    B.CreateStore(B.getInt64(2), gep);
    B.CreateBr(merge);
  }

  // merge: ret
  {
    llvm::IRBuilder<> B(merge);
    B.CreateRet(mem);
  }

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
  EXPECT_EQ(test_fn->size(), 4u);

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

  // Diamond with real conditional should NOT be simplified — all 4 blocks remain
  EXPECT_EQ(test_fn->size(), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CFGRecoveryTest, SingleBlockFunction_NoChange) {
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
  {
    llvm::IRBuilder<> B(entry);
    B.CreateRet(mem);
  }

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
  EXPECT_EQ(test_fn->size(), 1u);

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

  // Single-block function: nothing to simplify
  EXPECT_EQ(test_fn->size(), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(CFGRecoveryTest, VerifiesAfterTransform) {
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

  // Complex: entry -> bb1 -> bb2 -> exit, plus dead_bb (unreachable)
  // Also bb3 as constant-branch forwarder: entry2 path
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *bb1 = llvm::BasicBlock::Create(Ctx, "bb1", test_fn);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "bb2", test_fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", test_fn);
  auto *dead_bb = llvm::BasicBlock::Create(Ctx, "dead", test_fn);

  // entry: store, br bb1
  {
    llvm::IRBuilder<> B(entry);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(10), gep);
    B.CreateBr(bb1);
  }

  // bb1: store, br bb2
  {
    llvm::IRBuilder<> B(bb1);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 8);
    B.CreateStore(B.getInt64(20), gep);
    B.CreateBr(bb2);
  }

  // bb2: store, br exit
  {
    llvm::IRBuilder<> B(bb2);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    B.CreateStore(B.getInt64(30), gep);
    B.CreateBr(exit_bb);
  }

  // exit: ret
  {
    llvm::IRBuilder<> B(exit_bb);
    B.CreateRet(mem);
  }

  // dead: unreachable
  {
    llvm::IRBuilder<> B(dead_bb);
    B.CreateUnreachable();
  }

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
  EXPECT_EQ(test_fn->size(), 5u);

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

  // Chain merged + dead block removed → significant reduction
  EXPECT_LT(test_fn->size(), 5u);
  // The critical check: function must verify cleanly after all transforms
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

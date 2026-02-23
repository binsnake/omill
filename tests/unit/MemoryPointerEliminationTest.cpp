#include "omill/Passes/MemoryPointerElimination.h"

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

class MemoryPointerEliminationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::MemoryPointerEliminationPass());

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
};

TEST_F(MemoryPointerEliminationTest, MemArgReplacedWithPoison) {
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

  auto *mem = test_fn->getArg(2);

  // Use Memory* in a return (simulating remaining use after lowering)
  B.CreateRet(mem);

  // Before: arg2 (Memory*) has uses
  EXPECT_FALSE(test_fn->getArg(2)->use_empty());

  runPass(test_fn);

  // After: arg2 should have no uses (replaced with poison)
  EXPECT_TRUE(test_fn->getArg(2)->use_empty());

  // The return should now return poison
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::PoisonValue>(ret->getReturnValue()));

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(MemoryPointerEliminationTest, FunctionWithFewerThan3Args) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Only 2 args — pass should early-exit
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "two_arg_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(llvm::ConstantPointerNull::get(ptr_ty));

  runPass(test_fn);

  // arg1 should be untouched — pass did nothing
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::ConstantPointerNull>(ret->getReturnValue()));
}

TEST_F(MemoryPointerEliminationTest, MemArgAlreadyUnused) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "unused_mem", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  // Return arg0, arg2 (Memory*) is never used
  B.CreateRet(test_fn->getArg(0));

  EXPECT_TRUE(test_fn->getArg(2)->use_empty());

  runPass(test_fn);

  // arg2 still unused, function unchanged
  EXPECT_TRUE(test_fn->getArg(2)->use_empty());
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(MemoryPointerEliminationTest, MultipleUsesReplaced) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "multi_use", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *mem = test_fn->getArg(2);

  // Use 1: store mem into alloca
  auto *alloca = B.CreateAlloca(ptr_ty);
  B.CreateStore(mem, alloca);

  // Use 2: call an external function with mem
  auto *callee_ty = llvm::FunctionType::get(
      llvm::Type::getVoidTy(Ctx), {ptr_ty}, false);
  auto callee = M->getOrInsertFunction("sink", callee_ty);
  B.CreateCall(callee, {mem});

  // Use 3: return mem
  B.CreateRet(mem);

  EXPECT_EQ(mem->getNumUses(), 3u);

  runPass(test_fn);

  EXPECT_TRUE(mem->use_empty());

  // Verify all three instructions now use poison
  auto &BB = test_fn->getEntryBlock();
  auto It = BB.begin();
  ++It;  // skip alloca
  auto *store = llvm::dyn_cast<llvm::StoreInst>(&*It);
  ASSERT_NE(store, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::PoisonValue>(store->getValueOperand()));

  ++It;
  auto *call = llvm::dyn_cast<llvm::CallInst>(&*It);
  ASSERT_NE(call, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::PoisonValue>(call->getArgOperand(0)));

  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::PoisonValue>(ret->getReturnValue()));

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(MemoryPointerEliminationTest, NonLiftedFunction) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // 4 args — not a standard lifted signature, but pass still poisons arg2
  auto *fn_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, i64_ty, ptr_ty, i64_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "four_arg_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *mem = test_fn->getArg(2);
  B.CreateRet(mem);

  EXPECT_FALSE(mem->use_empty());

  runPass(test_fn);

  EXPECT_TRUE(mem->use_empty());

  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_TRUE(llvm::isa<llvm::PoisonValue>(ret->getReturnValue()));

  // arg3 should be untouched
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(MemoryPointerEliminationTest, DeclarationSkip) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  // Declaration only — no body
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "declared_only", *M);

  // arg2 has no uses in a declaration
  EXPECT_TRUE(test_fn->getArg(2)->use_empty());

  // Should not crash
  runPass(test_fn);

  EXPECT_TRUE(test_fn->getArg(2)->use_empty());
}

}  // namespace

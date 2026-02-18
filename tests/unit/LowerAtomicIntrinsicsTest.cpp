#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerAtomicIntrinsicsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Atomics));

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

TEST_F(LowerAtomicIntrinsicsTest, AtomicBeginEndRemoved) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_atomic_begin(Memory*) -> Memory*
  auto *atomic_begin_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
  M->getOrInsertFunction("__remill_atomic_begin", atomic_begin_ty);

  // Declare __remill_atomic_end(Memory*) -> Memory*
  auto *atomic_end_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
  M->getOrInsertFunction("__remill_atomic_end", atomic_end_ty);

  // Create lifted function
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *mem = test_fn->getArg(2);

  // mem1 = __remill_atomic_begin(mem)
  auto *begin_fn = M->getFunction("__remill_atomic_begin");
  auto *mem1 = B.CreateCall(begin_fn, {mem});

  // mem2 = __remill_atomic_end(mem1)
  auto *end_fn = M->getFunction("__remill_atomic_end");
  auto *mem2 = B.CreateCall(end_fn, {mem1});

  B.CreateRet(mem2);

  // Before: should have 2 calls
  unsigned call_count = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with("__remill_atomic"))
          call_count++;
  EXPECT_EQ(call_count, 2u);

  runPass(test_fn);

  // After: no more atomic calls, Memory* threaded through
  call_count = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with("__remill_atomic"))
          call_count++;
  EXPECT_EQ(call_count, 0u);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(LowerAtomicIntrinsicsTest, FetchAndAddLowered) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_fetch_and_add_32(Memory*, addr_t, value_ref) -> Memory*
  auto *fetch_add_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  M->getOrInsertFunction("__remill_fetch_and_add_32", fetch_add_ty);

  // Create lifted function
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *mem = test_fn->getArg(2);
  auto *addr = B.getInt64(0x1000);

  // Create a stack alloca for the value reference
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *val_ref = B.CreateAlloca(i32_ty, nullptr, "val_ref");
  B.CreateStore(B.getInt32(5), val_ref);

  // mem2 = __remill_fetch_and_add_32(mem, addr, val_ref)
  auto *fetch_fn = M->getFunction("__remill_fetch_and_add_32");
  auto *mem2 = B.CreateCall(fetch_fn, {mem, addr, val_ref});

  B.CreateRet(mem2);

  runPass(test_fn);

  // After: should have an atomicrmw add instruction
  bool has_atomicrmw = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *ARMW = llvm::dyn_cast<llvm::AtomicRMWInst>(&I))
        if (ARMW->getOperation() == llvm::AtomicRMWInst::Add)
          has_atomicrmw = true;
  EXPECT_TRUE(has_atomicrmw);

  // No more remill calls
  unsigned remill_calls = 0;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with("__remill_"))
          remill_calls++;
  EXPECT_EQ(remill_calls, 0u);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

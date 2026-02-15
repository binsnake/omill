#include "omill/Passes/LowerHyperCalls.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerHyperCallsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerHyperCallsPass());

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

TEST_F(LowerHyperCallsTest, SyncHyperCallLowered) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_sync_hyper_call(State*, Memory*, i32) -> Memory*
  auto *hyper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i32_ty}, false);
  M->getOrInsertFunction("__remill_sync_hyper_call", hyper_ty);

  // Create lifted function
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // mem2 = __remill_sync_hyper_call(state, mem, 42)
  auto *hyper_fn = M->getFunction("__remill_sync_hyper_call");
  auto *mem2 = B.CreateCall(hyper_fn, {state, mem, B.getInt32(42)});

  B.CreateRet(mem2);

  runPass(test_fn);

  // After: should have __omill_sync_hyper_call instead
  bool has_omill_call = false;
  bool has_remill_call = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction()) {
          if (CI->getCalledFunction()->getName() == "__omill_sync_hyper_call")
            has_omill_call = true;
          if (CI->getCalledFunction()->getName() == "__remill_sync_hyper_call")
            has_remill_call = true;
        }
      }
    }
  }
  EXPECT_TRUE(has_omill_call);
  EXPECT_FALSE(has_remill_call);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(LowerHyperCallsTest, CPUIDInlined) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *hyper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i32_ty}, false);
  M->getOrInsertFunction("__remill_sync_hyper_call", hyper_ty);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_cpuid", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // kX86CPUID = 258
  auto *hyper_fn = M->getFunction("__remill_sync_hyper_call");
  auto *mem2 = B.CreateCall(hyper_fn, {state, mem, B.getInt32(258)});
  B.CreateRet(mem2);

  runPass(test_fn);

  // Should have inline asm "cpuid", no __omill_sync_hyper_call stub.
  bool has_cpuid_asm = false;
  bool has_stub = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->isInlineAsm()) {
          auto *IA = llvm::cast<llvm::InlineAsm>(CI->getCalledOperand());
          if (IA->getAsmString().find("cpuid") != std::string::npos)
            has_cpuid_asm = true;
        }
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_sync_hyper_call")
          has_stub = true;
      }
    }
  }
  EXPECT_TRUE(has_cpuid_asm);
  EXPECT_FALSE(has_stub);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(LowerHyperCallsTest, RDTSCInlined) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *hyper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i32_ty}, false);
  M->getOrInsertFunction("__remill_sync_hyper_call", hyper_ty);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_rdtsc", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // kX86ReadTSC = 259
  auto *hyper_fn = M->getFunction("__remill_sync_hyper_call");
  auto *mem2 = B.CreateCall(hyper_fn, {state, mem, B.getInt32(259)});
  B.CreateRet(mem2);

  runPass(test_fn);

  // Should have llvm.readcyclecounter call, no stub.
  bool has_readcyclecounter = false;
  bool has_stub = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "llvm.readcyclecounter")
          has_readcyclecounter = true;
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_sync_hyper_call")
          has_stub = true;
      }
    }
  }
  EXPECT_TRUE(has_readcyclecounter);
  EXPECT_FALSE(has_stub);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(LowerHyperCallsTest, UnknownSyncFallsToStub) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *hyper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i32_ty}, false);
  M->getOrInsertFunction("__remill_sync_hyper_call", hyper_ty);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_unknown", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Unknown ID = 9999
  auto *hyper_fn = M->getFunction("__remill_sync_hyper_call");
  auto *mem2 = B.CreateCall(hyper_fn, {state, mem, B.getInt32(9999)});
  B.CreateRet(mem2);

  runPass(test_fn);

  // Should fall back to __omill_sync_hyper_call stub.
  bool has_stub = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_sync_hyper_call")
          has_stub = true;
      }
    }
  }
  EXPECT_TRUE(has_stub);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

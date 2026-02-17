#include "omill/Passes/ResolveNativeDispatch.h"

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

class ResolveNativeDispatchTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function &F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::ResolveNativeDispatchPass());

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

  /// Create a module with __omill_native_dispatch containing a switch table,
  /// plus native target functions.
  struct TestModule {
    std::unique_ptr<llvm::Module> M;
    llvm::Function *dispatch_fn;
    llvm::Function *target_native;
    llvm::Function *caller_fn;
  };

  TestModule createTestModule(bool constant_pc = true) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

    // Create target native function: i64(i64, i64)
    auto *native_fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
    auto *target_native = llvm::Function::Create(
        native_fn_ty, llvm::Function::ExternalLinkage, "sub_401000_native", *M);
    {
      auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_native);
      llvm::IRBuilder<> B(entry);
      B.CreateRet(target_native->getArg(0));
    }

    // Create __omill_native_dispatch: i64(i64 pc, i64 rcx, i64 rdx, i64 r8, i64 r9)
    auto *dispatch_fn_ty = llvm::FunctionType::get(
        i64_ty, {i64_ty, i64_ty, i64_ty, i64_ty, i64_ty}, false);
    auto *dispatch_fn = llvm::Function::Create(
        dispatch_fn_ty, llvm::Function::InternalLinkage,
        "__omill_native_dispatch", *M);

    {
      auto *entry = llvm::BasicBlock::Create(Ctx, "entry", dispatch_fn);
      auto *default_bb = llvm::BasicBlock::Create(Ctx, "unknown", dispatch_fn);
      auto *case_bb = llvm::BasicBlock::Create(Ctx, "call_401000", dispatch_fn);

      llvm::IRBuilder<> DefB(default_bb);
      DefB.CreateRet(DefB.getInt64(0));

      // Switch on pc arg
      llvm::IRBuilder<> EntryB(entry);
      auto *sw = EntryB.CreateSwitch(dispatch_fn->getArg(0), default_bb);
      sw->addCase(EntryB.getInt64(0x401000), case_bb);

      // Case: call sub_401000_native(rcx, rdx)
      llvm::IRBuilder<> CaseB(case_bb);
      auto *result = CaseB.CreateCall(
          target_native,
          {dispatch_fn->getArg(1), dispatch_fn->getArg(2)});
      CaseB.CreateRet(result);
    }

    // Create caller function that calls dispatch
    auto *caller_fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
    auto *caller_fn = llvm::Function::Create(
        caller_fn_ty, llvm::Function::ExternalLinkage, "caller", *M);

    {
      auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
      llvm::IRBuilder<> B(entry);

      llvm::Value *pc;
      if (constant_pc) {
        pc = B.getInt64(0x401000);
      } else {
        // Load a dynamic value
        pc = caller_fn->getArg(0);
      }

      auto *result = B.CreateCall(
          dispatch_fn,
          {pc, caller_fn->getArg(0), caller_fn->getArg(1),
           B.getInt64(0), B.getInt64(0)},
          "dispatch.result");
      B.CreateRet(result);
    }

    return {std::move(M), dispatch_fn, target_native, caller_fn};
  }
};

TEST_F(ResolveNativeDispatchTest, ConstantPCResolved) {
  auto [M, dispatch_fn, target_native, caller_fn] = createTestModule(true);

  // Before: caller calls __omill_native_dispatch.
  bool calls_dispatch_before = false;
  for (auto &I : caller_fn->getEntryBlock())
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
      if (CI->getCalledFunction() == dispatch_fn)
        calls_dispatch_before = true;
  ASSERT_TRUE(calls_dispatch_before);

  runPass(*caller_fn);

  // After: should call target_native directly.
  bool calls_dispatch_after = false;
  bool calls_target_directly = false;
  for (auto &I : caller_fn->getEntryBlock()) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (CI->getCalledFunction() == dispatch_fn)
        calls_dispatch_after = true;
      if (CI->getCalledFunction() == target_native)
        calls_target_directly = true;
    }
  }

  EXPECT_FALSE(calls_dispatch_after);
  EXPECT_TRUE(calls_target_directly);
  EXPECT_FALSE(llvm::verifyFunction(*caller_fn, &llvm::errs()));
}

TEST_F(ResolveNativeDispatchTest, DynamicPCPreserved) {
  auto [M, dispatch_fn, target_native, caller_fn] = createTestModule(false);

  // Before: caller calls dispatch with dynamic PC.
  bool calls_dispatch_before = false;
  for (auto &I : caller_fn->getEntryBlock())
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
      if (CI->getCalledFunction() == dispatch_fn)
        calls_dispatch_before = true;
  ASSERT_TRUE(calls_dispatch_before);

  runPass(*caller_fn);

  // After: dispatch call should remain (dynamic PC can't be resolved).
  bool calls_dispatch_after = false;
  for (auto &I : caller_fn->getEntryBlock())
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
      if (CI->getCalledFunction() == dispatch_fn)
        calls_dispatch_after = true;

  EXPECT_TRUE(calls_dispatch_after);
  EXPECT_FALSE(llvm::verifyFunction(*caller_fn, &llvm::errs()));
}

}  // namespace

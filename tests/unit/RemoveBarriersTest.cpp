#include "omill/Passes/RemoveBarriers.h"

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

class RemoveBarriersTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *void_ty = llvm::Type::getVoidTy(Ctx);

    // Declare __remill_barrier_load_store(Memory*) -> Memory*
    M->getOrInsertFunction(
        "__remill_barrier_load_store",
        llvm::FunctionType::get(ptr_ty, {ptr_ty}, false));

    // Create a test function with volatile inline asm barriers
    auto *fn_ty = llvm::FunctionType::get(
        ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> Builder(entry);

    auto *mem = test_fn->getArg(2);

    // Insert a volatile empty inline asm barrier (remill separator pattern).
    auto *asm_ty = llvm::FunctionType::get(void_ty, false);
    auto *inline_asm = llvm::InlineAsm::get(
        asm_ty, "", "~{memory}", /*hasSideEffects=*/true);
    Builder.CreateCall(inline_asm);

    // Insert a barrier intrinsic call.
    auto *barrier_fn = M->getFunction("__remill_barrier_load_store");
    auto *new_mem = Builder.CreateCall(barrier_fn, {mem});

    // Another volatile asm barrier.
    Builder.CreateCall(inline_asm);

    Builder.CreateRet(new_mem);

    return M;
  }
};

TEST_F(RemoveBarriersTest, RemovesVolatileAsmAndBarrierIntrinsics) {
  auto M = createTestModule();
  auto *test_fn = M->getFunction("test_func");
  ASSERT_NE(test_fn, nullptr);

  // Count barriers before.
  unsigned barrier_count = 0;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->isInlineAsm() || (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with("__remill_barrier"))) {
          barrier_count++;
        }
      }
    }
  }
  EXPECT_EQ(barrier_count, 3u);  // 2 inline asm + 1 barrier intrinsic

  // Run the pass.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::RemoveBarriersPass());

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

  // Count barriers after.
  barrier_count = 0;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->isInlineAsm() || (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with("__remill_barrier"))) {
          barrier_count++;
        }
      }
    }
  }
  EXPECT_EQ(barrier_count, 0u);

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

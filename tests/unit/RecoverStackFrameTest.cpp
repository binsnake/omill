#include "omill/Passes/RecoverStackFrame.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Utils/StateFieldMap.h"

#include <gtest/gtest.h>

namespace {

class RecoverStackFrameTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a function that does RSP-relative memory access
  /// via inttoptr (the pattern after LowerMemoryIntrinsics).
  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Create State struct
    auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
    auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
    state_ty->setBody({arr_ty});

    // Create __remill_basic_block with RSP at offset 48
    auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    {
      llvm::IRBuilder<> B(bb_entry);
      B.CreateConstGEP1_64(B.getInt8Ty(), bb_fn->getArg(0), 48, "RSP");
      B.CreateRet(bb_fn->getArg(2));
    }

    // Create test function
    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *mem = test_fn->getArg(2);

    // Load RSP from State
    auto *rsp_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 48, "rsp_ptr");
    auto *rsp = B.CreateLoad(i64_ty, rsp_gep, "rsp");

    // Access [RSP - 8] — local variable
    auto *addr1 = B.CreateSub(rsp, B.getInt64(8), "local_addr");
    auto *ptr1 = B.CreateIntToPtr(addr1, ptr_ty, "local_ptr");
    B.CreateStore(B.getInt32(42), ptr1);

    // Access [RSP - 16] — another local
    auto *addr2 = B.CreateSub(rsp, B.getInt64(16), "local_addr2");
    auto *ptr2 = B.CreateIntToPtr(addr2, ptr_ty, "local_ptr2");
    auto *val = B.CreateLoad(i32_ty, ptr2, "local_val");
    (void)val;

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(RecoverStackFrameTest, ReplacesIntToPtrWithAllocaGEP) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Before: should have inttoptr instructions.
  unsigned inttoptr_count_before = 0;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (llvm::isa<llvm::IntToPtrInst>(&I))
        inttoptr_count_before++;
  EXPECT_EQ(inttoptr_count_before, 2u);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::RecoverStackFramePass());

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

  // After: inttoptr should be replaced with GEPs into a stack alloca.
  unsigned inttoptr_count_after = 0;
  unsigned alloca_count = 0;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::IntToPtrInst>(&I))
        inttoptr_count_after++;
      if (llvm::isa<llvm::AllocaInst>(&I))
        alloca_count++;
    }
  }

  EXPECT_EQ(inttoptr_count_after, 0u);
  EXPECT_GE(alloca_count, 1u);  // Should have a stack_frame alloca

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

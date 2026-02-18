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

TEST_F(RecoverStackFrameTest, PositiveOffsetNoChange) {
  // Positive offset from RSP should NOT be turned into alloca —
  // it's accessing the caller's frame / return address, not a local.
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Rebuild function: only positive offset access.
  for (auto &BB : llvm::make_early_inc_range(*F))
    BB.eraseFromParent();

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *rsp_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 48, "rsp_ptr");
  auto *rsp = B.CreateLoad(i64_ty, rsp_gep, "rsp");

  // Access [RSP + 8] — positive offset, caller frame.
  auto *addr = B.CreateAdd(rsp, B.getInt64(8), "caller_addr");
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty, "caller_ptr");
  B.CreateStore(B.getInt32(99), ptr);
  B.CreateRet(mem);

  // Before: one inttoptr.
  unsigned inttoptr_before = 0;
  for (auto &BB2 : *F)
    for (auto &I : BB2)
      if (llvm::isa<llvm::IntToPtrInst>(&I))
        inttoptr_before++;
  EXPECT_EQ(inttoptr_before, 1u);

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

  // After: inttoptr should remain (positive offset, not a stack frame access).
  unsigned inttoptr_after = 0;
  for (auto &BB2 : *F)
    for (auto &I : BB2)
      if (llvm::isa<llvm::IntToPtrInst>(&I))
        inttoptr_after++;
  EXPECT_EQ(inttoptr_after, 1u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverStackFrameTest, MultipleNegativeOffsets) {
  // RSP-8, RSP-16, RSP-24, RSP-32 — all replaced with GEPs into one alloca.
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  for (auto &BB : llvm::make_early_inc_range(*F))
    BB.eraseFromParent();

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *rsp_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 48, "rsp_ptr");
  auto *rsp = B.CreateLoad(i64_ty, rsp_gep, "rsp");

  for (int off : {-8, -16, -24, -32}) {
    auto *addr = B.CreateSub(rsp, B.getInt64(-off), "local_addr");
    auto *ptr = B.CreateIntToPtr(addr, ptr_ty, "local_ptr");
    B.CreateStore(B.getInt32(42), ptr);
  }

  B.CreateRet(mem);

  unsigned inttoptr_before = 0;
  for (auto &BB2 : *F)
    for (auto &I : BB2)
      if (llvm::isa<llvm::IntToPtrInst>(&I))
        inttoptr_before++;
  EXPECT_EQ(inttoptr_before, 4u);

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

  unsigned inttoptr_after = 0;
  unsigned alloca_count = 0;
  for (auto &BB2 : *F) {
    for (auto &I : BB2) {
      if (llvm::isa<llvm::IntToPtrInst>(&I))
        inttoptr_after++;
      if (llvm::isa<llvm::AllocaInst>(&I))
        alloca_count++;
    }
  }

  EXPECT_EQ(inttoptr_after, 0u);
  EXPECT_GE(alloca_count, 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverStackFrameTest, BareRSPOffsetNotReplaced) {
  // add(RSP, -16) with non-inttoptr users (store to State) → replaced with
  // ptrtoint(GEP).
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  for (auto &BB : llvm::make_early_inc_range(*F))
    BB.eraseFromParent();

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *rsp_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 48, "rsp_ptr");
  auto *rsp = B.CreateLoad(i64_ty, rsp_gep, "rsp");

  // Create inttoptr users at RSP-8 and RSP-24 so the pass recognizes this
  // as a stack pointer field and covers the range [-24, -8].
  auto *addr1 = B.CreateSub(rsp, B.getInt64(8), "local1");
  auto *ptr1 = B.CreateIntToPtr(addr1, ptr_ty, "local_ptr1");
  B.CreateStore(B.getInt32(1), ptr1);

  auto *addr1b = B.CreateSub(rsp, B.getInt64(24), "local1b");
  auto *ptr1b = B.CreateIntToPtr(addr1b, ptr_ty, "local_ptr1b");
  B.CreateStore(B.getInt32(2), ptr1b);

  // Bare add(RSP, -16) stored to State — not used as inttoptr.
  // Offset -16 falls within the region [-24, -8].
  auto *addr2 = B.CreateAdd(rsp, B.getInt64(-16), "bare_addr");
  auto *state_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 100, "dest");
  B.CreateStore(addr2, state_gep);

  B.CreateRet(mem);

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

  // The bare add should remain; there should be no synthesized ptrtoint(GEP).
  bool found_ptrtoint = false;
  bool found_bare_add = false;
  for (auto &BB2 : *F)
    for (auto &I : BB2) {
      if (auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(&I))
        if (llvm::isa<llvm::GetElementPtrInst>(PTI->getOperand(0)))
          found_ptrtoint = true;
      if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I))
        if (BO->getOpcode() == llvm::Instruction::Add &&
            BO->getName() == "bare_addr")
          found_bare_add = true;
    }

  EXPECT_FALSE(found_ptrtoint);
  EXPECT_TRUE(found_bare_add);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

#include "omill/Passes/PromoteStateToSSA.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/Scalar/SROA.h>

#include <gtest/gtest.h>

namespace {

class PromoteStateToSSATest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a function that loads a State field, adds 1, stores back.
  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *mem = test_fn->getArg(2);

    // Load from State offset 16 (simulating a register like RBX)
    auto *gep_load = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "rbx_ptr");
    auto *val = B.CreateLoad(i64_ty, gep_load, "rbx_val");

    // val + 1
    auto *val2 = B.CreateAdd(val, B.getInt64(1), "inc");

    // Store back to State offset 16
    auto *gep_store = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "rbx_ptr2");
    B.CreateStore(val2, gep_store);

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(PromoteStateToSSATest, CreatesAllocasForStateFields) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Before: no allocas
  unsigned allocas_before = 0;
  for (auto &I : F->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      allocas_before++;
  EXPECT_EQ(allocas_before, 0u);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());

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

  // After: should have at least one alloca for the state field
  unsigned allocas_after = 0;
  for (auto &I : F->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      allocas_after++;
  EXPECT_GE(allocas_after, 1u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(PromoteStateToSSATest, SROAPromotesToSSA) {
  auto M = createTestModule();
  auto *F = M->getFunction("test_func");
  ASSERT_NE(F, nullptr);

  // Run PromoteStateToSSA then SROA.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));

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

  // After SROA, the alloca should be promoted — no allocas remaining.
  unsigned allocas_after = 0;
  for (auto &I : F->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      allocas_after++;
  EXPECT_EQ(allocas_after, 0u);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(PromoteStateToSSATest, WideStoreOverlap) {
  // Regression test: A 128-bit store at offset 16 spans both offset 16 and 24.
  // After promotion, a load from offset 24 must see the upper half of the wide
  // store, not the stale initial value.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i128_ty = llvm::Type::getInt128Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Wide 128-bit store at State+16 (covers offsets 16..31, including offset 24).
  auto *gep16 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "xmm_ptr");
  auto *wide_val = llvm::ConstantInt::get(i128_ty, llvm::APInt(128, {0xDEADBEEFCAFEBABEULL, 0x1122334455667788ULL}));
  B.CreateStore(wide_val, gep16);

  // Load i64 from State+24 — must see upper half of the wide store.
  auto *gep24 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 24, "xmm_hi_ptr");
  auto *hi_val = B.CreateLoad(i64_ty, gep24, "xmm_hi");
  (void)hi_val;

  B.CreateRet(mem);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());

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

  // After promotion, there must be a load from within the wide alloca to feed
  // the offset-24 alloca (the "wide.sub" decomposition).
  bool found_wide_sub = false;
  for (auto &BB : *test_fn)
    for (auto &I : BB)
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
        if (LI->getName().starts_with("wide.sub"))
          found_wide_sub = true;

  EXPECT_TRUE(found_wide_sub);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(PromoteStateToSSATest, FlushBeforeStateCall) {
  // Regression test: calls that take State as arg must have flush/reload.
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

  // Create an external function that takes State.
  auto *callee_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *callee = llvm::Function::Create(
      callee_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Store a value to State+16
  auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "field_ptr");
  B.CreateStore(B.getInt64(42), gep);

  // Call that takes State as arg
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Load from State+16 after the call
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16, "field_ptr2");
  auto *post_val = B.CreateLoad(i64_ty, gep2, "post_val");
  (void)post_val;

  B.CreateRet(call);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());

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

  // Count stores to State (GEP + store patterns) — there should be flush
  // stores before the call AND write-back stores before the return.
  unsigned state_stores = 0;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        // Check if storing to a GEP from arg0 (State).
        if (auto *gep_op = llvm::dyn_cast<llvm::GetElementPtrInst>(
                SI->getPointerOperand())) {
          if (gep_op->getPointerOperand() == state ||
              (llvm::isa<llvm::BitCastInst>(gep_op->getPointerOperand()) &&
               llvm::cast<llvm::BitCastInst>(gep_op->getPointerOperand())
                       ->getOperand(0) == state))
            state_stores++;
        }
      }
    }
  }

  // We expect at least 2 stores to State: one flush before call, one
  // write-back before return.
  EXPECT_GE(state_stores, 2u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(PromoteStateToSSATest, MultipleFields) {
  // Three independent fields at offsets 16, 24, and 32 each get their own
  // alloca with independent values.
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

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Store different values to three distinct offsets.
  for (unsigned off : {16u, 24u, 32u}) {
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, off);
    B.CreateStore(B.getInt64(off * 100), gep);
  }

  // Load them back.
  for (unsigned off : {16u, 24u, 32u}) {
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, off);
    auto *val = B.CreateLoad(i64_ty, gep);
    (void)val;
  }

  B.CreateRet(mem);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());

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

  // Should have at least 3 allocas (one per field).
  unsigned alloca_count = 0;
  for (auto &I : test_fn->getEntryBlock())
    if (llvm::isa<llvm::AllocaInst>(&I))
      alloca_count++;

  EXPECT_GE(alloca_count, 3u);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

TEST_F(PromoteStateToSSATest, MultiBlockPHI) {
  // State field loaded in two predecessors → PHI in successor after SROA.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1_ty = llvm::Type::getInt1Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  auto *then_bb = llvm::BasicBlock::Create(Ctx, "then", test_fn);
  auto *else_bb = llvm::BasicBlock::Create(Ctx, "else", test_fn);
  auto *merge_bb = llvm::BasicBlock::Create(Ctx, "merge", test_fn);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Entry: branch based on some condition.
  llvm::IRBuilder<> EntryB(entry);
  auto *cond_gep = EntryB.CreateConstGEP1_64(EntryB.getInt8Ty(), state, 0);
  auto *cond_val = EntryB.CreateLoad(i64_ty, cond_gep, "cond_raw");
  auto *cond = EntryB.CreateICmpNE(cond_val, EntryB.getInt64(0), "cond");
  EntryB.CreateCondBr(cond, then_bb, else_bb);

  // Then: store 42 to State+16.
  llvm::IRBuilder<> ThenB(then_bb);
  auto *gep_then = ThenB.CreateConstGEP1_64(ThenB.getInt8Ty(), state, 16);
  ThenB.CreateStore(ThenB.getInt64(42), gep_then);
  ThenB.CreateBr(merge_bb);

  // Else: store 99 to State+16.
  llvm::IRBuilder<> ElseB(else_bb);
  auto *gep_else = ElseB.CreateConstGEP1_64(ElseB.getInt8Ty(), state, 16);
  ElseB.CreateStore(ElseB.getInt64(99), gep_else);
  ElseB.CreateBr(merge_bb);

  // Merge: load from State+16 — should get PHI after SROA.
  llvm::IRBuilder<> MergeB(merge_bb);
  auto *gep_merge = MergeB.CreateConstGEP1_64(MergeB.getInt8Ty(), state, 16);
  auto *merged_val = MergeB.CreateLoad(i64_ty, gep_merge, "merged");
  (void)merged_val;
  MergeB.CreateRet(mem);

  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::PromoteStateToSSAPass());
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));

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

  // After SROA: should have a PHI node in the merge block.
  bool found_phi = false;
  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::PHINode>(&I))
        found_phi = true;
    }
  }
  EXPECT_TRUE(found_phi);
  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

#include "omill/Passes/OptimizeState.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class OptimizeStateTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  static constexpr const char *kDataLayout =
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128";

  /// Run a specific phase of OptimizeStatePass on a function.
  void runPass(llvm::Function *F, uint32_t phases) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::OptimizeStatePass(phases));

    llvm::FunctionAnalysisManager FAM;
    llvm::LoopAnalysisManager LAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    llvm::PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    FPM.run(*F, FAM);
  }

  /// Create a module with __remill_basic_block that registers flag fields.
  /// ZF at offset 200, CF at offset 201.
  std::unique_ptr<llvm::Module> createModuleWithFlags() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    auto *bb_fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);

    auto *bb_state = bb_fn->getArg(0);
    BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 200, "ZF");
    BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 201, "CF");
    BBB.CreateRet(bb_fn->getArg(2));

    return M;
  }

  /// Create a plain module (no __remill_basic_block).
  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a lifted function with remill signature: (ptr, i64, ptr) -> ptr.
  llvm::Function *createLiftedFn(llvm::Module &M,
                                  const char *name = "sub_401000") {
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage, name,
                                  M);
  }

  /// Count store instructions in a function.
  unsigned countStores(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (llvm::isa<llvm::StoreInst>(&I))
          ++count;
    return count;
  }

  /// Count load instructions in a function.
  unsigned countLoads(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (llvm::isa<llvm::LoadInst>(&I))
          ++count;
    return count;
  }
};

// ---------------------------------------------------------------------------
// Test 1: DeadFlags — two stores to same flag offset, no read between.
// First store is dead and should be eliminated.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, DeadFlagStore_Eliminated) {
  auto M = createModuleWithFlags();
  auto *F = createLiftedFn(*M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Two consecutive stores to ZF (offset 200), no intervening read.
  auto *zf_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state, 200, "zf_ptr");
  B.CreateStore(B.getInt8(1), zf_ptr);  // dead
  B.CreateStore(B.getInt8(0), zf_ptr);  // live
  B.CreateRet(mem);

  EXPECT_EQ(countStores(F), 2u);

  runPass(F, omill::OptimizePhases::DeadStores);

  EXPECT_EQ(countStores(F), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 2: DeadStores — two stores to same State offset, first killed.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, DeadStateStore_SameOffset_FirstKilled) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Two stores to offset 2216 (arbitrary), no read between.
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);  // dead
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  B.CreateStore(B.getInt64(99), gep2);  // live
  B.CreateRet(mem);

  EXPECT_EQ(countStores(F), 2u);

  runPass(F, omill::OptimizePhases::DeadStores);

  EXPECT_EQ(countStores(F), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 3: Store-load-store to same offset — first store preserved because
// of intervening read.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, StoreWithReadBetween_Preserved) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "ptr1");
  B.CreateStore(B.getInt64(42), gep1);

  // Intervening load from same offset invalidates the "dead" status.
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "ptr2");
  auto *load = B.CreateLoad(i64_ty, gep2, "val");

  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "ptr3");
  B.CreateStore(B.getInt64(99), gep3);

  B.CreateRet(mem);

  EXPECT_EQ(countStores(F), 2u);

  runPass(F, omill::OptimizePhases::DeadStores);

  // Both stores survive because the load between them makes the first live.
  EXPECT_EQ(countStores(F), 2u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 4: RedundantBytes — i32 const store followed by i8 const store that
// matches one byte of the wider value. The narrow store is redundant.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, RedundantByte_Eliminated) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);

  // Wide store: i32 0x00000000 at offset 464.
  auto *gep_wide =
      B.CreateConstGEP1_64(B.getInt8Ty(), state, 464, "wide_ptr");
  B.CreateStore(llvm::ConstantInt::get(i32_ty, 0), gep_wide);

  // Narrow store: i8 0 at offset 466 (byte 2 of the i32 zero) — redundant.
  auto *gep_narrow =
      B.CreateConstGEP1_64(B.getInt8Ty(), state, 466, "narrow_ptr");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, 0), gep_narrow);

  B.CreateRet(mem);

  EXPECT_EQ(countStores(F), 2u);

  runPass(F, omill::OptimizePhases::RedundantBytes);

  // Narrow store eliminated because byte 2 of i32(0) is already 0.
  EXPECT_EQ(countStores(F), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 5: Roundtrip — load from offset X, store same value back, single use.
// Both load and store should be eliminated.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, Roundtrip_Eliminated) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Load from offset 2216, then store the loaded value right back.
  auto *gep_load =
      B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rt_load_ptr");
  auto *val = B.CreateLoad(i64_ty, gep_load, "roundtrip_val");
  auto *gep_store =
      B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rt_store_ptr");
  B.CreateStore(val, gep_store);

  B.CreateRet(mem);

  EXPECT_EQ(countStores(F), 1u);
  EXPECT_EQ(countLoads(F), 1u);

  runPass(F, omill::OptimizePhases::Roundtrip);

  // Both the load and the store should be removed.
  EXPECT_EQ(countStores(F), 0u);
  EXPECT_EQ(countLoads(F), 0u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 6: Declaration function (no body) — pass is a no-op.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, DeclarationFunction_Skipped) {
  auto M = createModule();

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_401000", *M);
  // F is a declaration (no basic blocks).
  ASSERT_TRUE(F->isDeclaration());

  // Should not crash or modify anything.
  runPass(F, omill::OptimizePhases::All);

  EXPECT_TRUE(F->isDeclaration());
}

// ---------------------------------------------------------------------------
// Test 7: Roundtrip after call — flush, call, reload+store back = dead.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, Roundtrip_AfterCall_Eliminated) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *callee = createLiftedFn(*M, "sub_402000");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Flush: store value to State+2216 (RAX)
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);

  // Call that takes State
  auto *call1 = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Roundtrip: load from State+2216, store back immediately
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  auto *reloaded = B.CreateLoad(i64_ty, gep2, "reloaded");
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr3");
  B.CreateStore(reloaded, gep3);

  // Second call
  auto *call2 = B.CreateCall(callee, {state, B.getInt64(0), call1});
  B.CreateRet(call2);

  unsigned stores_before = countStores(F);

  runPass(F, omill::OptimizePhases::Roundtrip);

  EXPECT_LT(countStores(F), stores_before);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 8: Roundtrip with modified value — NOT a roundtrip, preserved.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, Roundtrip_ModifiedValue_Preserved) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *callee = createLiftedFn(*M, "sub_402000");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Load, modify, store — not a roundtrip.
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  auto *loaded = B.CreateLoad(i64_ty, gep2, "loaded");
  auto *modified = B.CreateAdd(loaded, B.getInt64(1), "modified");
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr3");
  B.CreateStore(modified, gep3);

  B.CreateRet(call);

  unsigned stores_before = countStores(F);

  runPass(F, omill::OptimizePhases::Roundtrip);

  EXPECT_EQ(countStores(F), stores_before);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 9: Cross-block roundtrip — load and store in different blocks,
// should be preserved (roundtrip elimination is intra-block only).
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, Roundtrip_CrossBlock_Preserved) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *callee = createLiftedFn(*M, "sub_402000");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *cont = llvm::BasicBlock::Create(Ctx, "cont", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr1");
  B.CreateStore(B.getInt64(42), gep1);
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // Load in entry block
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr2");
  auto *loaded = B.CreateLoad(i64_ty, gep2, "loaded");
  B.CreateBr(cont);

  // Store in continuation block
  B.SetInsertPoint(cont);
  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216, "rax_ptr3");
  B.CreateStore(loaded, gep3);
  B.CreateRet(call);

  unsigned stores_before = countStores(F);

  runPass(F, omill::OptimizePhases::Roundtrip);

  EXPECT_EQ(countStores(F), stores_before);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

// ---------------------------------------------------------------------------
// Test 10: RedundantBytes — non-overlapping stores preserved.
// ---------------------------------------------------------------------------
TEST_F(OptimizeStateTest, RedundantByte_NonOverlapping_Preserved) {
  auto M = createModule();
  auto *F = createLiftedFn(*M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);

  // Store i64 at offset 464
  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 464, "ptr1");
  B.CreateStore(B.getInt64(0), gep1);

  // Store i8 at offset 500 — not overlapping with 464..471
  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, 500, "ptr2");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, 42), gep2);

  B.CreateRet(mem);

  runPass(F, omill::OptimizePhases::RedundantBytes);

  EXPECT_EQ(countStores(F), 2u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

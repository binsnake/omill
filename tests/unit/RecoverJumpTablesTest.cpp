#include "omill/Passes/ResolveAndLowerControlFlow.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

class RecoverJumpTablesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  llvm::Function *createDispatchJumpDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_jump", M);
  }

  void runPass(llvm::Module *M, omill::BinaryMemoryMap map) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass(
        [&]() { return omill::BinaryMemoryAnalysis(std::move(map)); });
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    (void)MAM.getResult<omill::BinaryMemoryAnalysis>(*M);
    (void)MAM.getResult<omill::LiftedFunctionAnalysis>(*M);

    llvm::ModulePassManager MPM;
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(
        omill::ResolveAndLowerControlFlowPass(omill::ResolvePhases::RecoverTables)));
    MPM.run(*M, MAM);
  }

  unsigned countDispatchJumps(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = CI->getCalledFunction())
            if (callee->getName() == "__omill_dispatch_jump")
              ++count;
    return count;
  }

  bool hasSwitchInst(llvm::Function *F) {
    for (auto &BB : *F)
      if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
        return true;
    return false;
  }

  unsigned countSwitchCases(llvm::Function *F) {
    for (auto &BB : *F)
      if (auto *SW = llvm::dyn_cast<llvm::SwitchInst>(BB.getTerminator()))
        return SW->getNumCases();
    return 0;
  }

  /// Build the standard jump table pattern:
  ///   bounds_bb: icmp ult %idx, N → switch_bb / default_bb
  ///   switch_bb: table load + dispatch_jump + ret
  /// Returns the function.
  llvm::Function *buildJumpTablePattern(
      llvm::Module &M, unsigned num_entries, unsigned stride,
      uint64_t table_base, uint64_t image_base,
      llvm::SmallVectorImpl<llvm::BasicBlock *> &target_blocks) {
    auto *F = llvm::Function::Create(liftedFnType(),
                                      llvm::Function::ExternalLinkage,
                                      "sub_140001000", M);

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *dispatch = M.getFunction("__omill_dispatch_jump");

    // Create target blocks.
    for (unsigned i = 0; i < num_entries; ++i) {
      char name[64];
      snprintf(name, sizeof(name), "block_%llx",
               (unsigned long long)(0x140001100 + i * 0x10));
      auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
      llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
      target_blocks.push_back(bb);
    }

    auto *bounds_bb = llvm::BasicBlock::Create(Ctx, "bounds_check", F);
    auto *switch_bb = llvm::BasicBlock::Create(Ctx, "switch_bb", F);
    auto *default_bb = llvm::BasicBlock::Create(Ctx, "default_bb", F);

    // bounds_check: icmp ult %idx, N
    llvm::IRBuilder<> B(bounds_bb);
    // Use a load to produce a non-constant index.
    auto *idx_ptr = B.CreateAlloca(i64_ty);
    auto *idx = B.CreateLoad(i64_ty, idx_ptr, "idx");
    auto *cmp = B.CreateICmpULT(idx, llvm::ConstantInt::get(i64_ty, num_entries));
    B.CreateCondBr(cmp, switch_bb, default_bb);

    // switch_bb: table lookup + dispatch_jump
    B.SetInsertPoint(switch_bb);
    unsigned shift = (stride == 4) ? 2 : 3;
    auto *scaled = B.CreateShl(idx, llvm::ConstantInt::get(i64_ty, shift));
    auto *addr = B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, table_base));
    auto *ptr = B.CreateIntToPtr(addr, ptr_ty);

    llvm::Value *target;
    if (stride == 4) {
      auto *entry = B.CreateLoad(llvm::Type::getInt32Ty(Ctx), ptr, "entry");
      auto *ext = B.CreateZExt(entry, i64_ty);
      target = B.CreateAdd(ext, llvm::ConstantInt::get(i64_ty, image_base));
    } else {
      target = B.CreateLoad(i64_ty, ptr, "entry");
    }

    auto *result = B.CreateCall(
        dispatch, {F->getArg(0), target, F->getArg(2)});
    B.CreateRet(result);

    // default_bb: fallthrough
    B.SetInsertPoint(default_bb);
    auto *def_result = B.CreateCall(
        dispatch, {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
    B.CreateRet(def_result);

    // Move bounds_check to front.
    bounds_bb->moveBefore(&F->getEntryBlock());

    return F;
  }
};

TEST_F(RecoverJumpTablesTest, Absolute8ByteTable) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  auto *F = buildJumpTablePattern(*M, 4, 8, 0x140020000, 0, target_blocks);

  // Build memory: 4 entries * 8 bytes each, absolute VAs.
  uint64_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = 0x140001100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(table), 32);

  EXPECT_EQ(countDispatchJumps(F), 2u);  // switch_bb + default_bb

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, Relative4ByteTable) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  uint64_t image_base = 0x140000000;
  auto *F = buildJumpTablePattern(*M, 4, 4, 0x140020000, image_base,
                                   target_blocks);

  // Build memory: 4 entries * 4 bytes each, RVA32 relative to image_base.
  uint32_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = static_cast<uint32_t>(0x140001100 + i * 0x10 - image_base);

  omill::BinaryMemoryMap map;
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(table), 16);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, BoundsFromICmp) {
  // Same as Absolute8ByteTable but verifies that the icmp ult establishes
  // exactly 4 cases.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  auto *F = buildJumpTablePattern(*M, 4, 8, 0x140020000, 0, target_blocks);

  uint64_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = 0x140001100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  // Verify exactly 4 cases from the icmp ult %idx, 4.
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, SkipsDynamicBase) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  // Table base is a function argument (dynamic), not constant.
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr);
  auto *scaled = B.CreateShl(idx, B.getInt64(3));
  auto *addr = B.CreateAdd(scaled, F->getArg(1));  // dynamic base!
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr);
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  uint64_t dummy[4] = {0};
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(dummy), 32);

  unsigned before = countDispatchJumps(F);

  runPass(M.get(), std::move(map));

  // Should remain unchanged — base is not constant.
  EXPECT_EQ(countDispatchJumps(F), before);
  EXPECT_FALSE(hasSwitchInst(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, UnknownEntryFallsToDefault) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  auto *F = buildJumpTablePattern(*M, 4, 8, 0x140020000, 0, target_blocks);

  // 3 entries resolve to known blocks, 1 is unknown (0xDEADBEEF).
  uint64_t table[4] = {
      0x140001100,
      0x140001110,
      0xDEADBEEF,  // unknown target
      0x140001130,
  };

  omill::BinaryMemoryMap map;
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  // Should still generate a switch with 3 known cases.
  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 3u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, MixedIntraInterTargets) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  // Create an inter-function target.
  auto *inter_fn = llvm::Function::Create(liftedFnType(),
                                            llvm::Function::ExternalLinkage,
                                            "sub_140005000", *M);
  auto *inter_entry = llvm::BasicBlock::Create(Ctx, "entry", inter_fn);
  llvm::IRBuilder<>(inter_entry).CreateRet(inter_fn->getArg(2));

  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  auto *F = buildJumpTablePattern(*M, 4, 8, 0x140020000, 0, target_blocks);

  // 3 intra-function + 1 inter-function target.
  uint64_t table[4] = {
      0x140001100,
      0x140001110,
      0x140005000,  // inter-function (sub_140005000)
      0x140001130,
  };

  omill::BinaryMemoryMap map;
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);

  // Verify there's a musttail call to sub_140005000 in one of the case blocks.
  bool found_tail_call = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      if (CI->getTailCallKind() == llvm::CallInst::TCK_MustTail) {
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == "sub_140005000")
          found_tail_call = true;
      }
    }
  }
  EXPECT_TRUE(found_tail_call);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, BoundsFromAndMask) {
  // Index is bounded by AND mask: idx = and(raw, 7) → 8 entries.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch = createDispatchJumpDecl(*M);  // already created, get it
  dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140002000", *M);

  // Create 8 target blocks.
  llvm::SmallVector<llvm::BasicBlock *, 8> target_blocks;
  for (unsigned i = 0; i < 8; ++i) {
    char name[64];
    snprintf(name, sizeof(name), "block_%llx",
             (unsigned long long)(0x140002100 + i * 0x10));
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
    target_blocks.push_back(bb);
  }

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  entry->moveBefore(&F->getEntryBlock());

  llvm::IRBuilder<> B(entry);
  auto *raw_ptr = B.CreateAlloca(i64_ty);
  auto *raw = B.CreateLoad(i64_ty, raw_ptr, "raw");
  // AND with mask 7 → range [0, 8)
  auto *idx = B.CreateAnd(raw, llvm::ConstantInt::get(i64_ty, 7), "idx");
  auto *scaled = B.CreateShl(idx, llvm::ConstantInt::get(i64_ty, 3));
  auto *addr = B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140030000));
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr, "entry_val");
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  // Build memory: 8 entries * 8 bytes.
  uint64_t table[8];
  for (unsigned i = 0; i < 8; ++i)
    table[i] = 0x140002100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140030000, reinterpret_cast<const uint8_t *>(table), 64);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 8u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, BoundsFromMultiPredecessor) {
  // Index is bounded by icmp in a grandparent block (depth 2).
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140003000", *M);

  // Create 4 target blocks.
  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  for (unsigned i = 0; i < 4; ++i) {
    char name[64];
    snprintf(name, sizeof(name), "block_%llx",
             (unsigned long long)(0x140003100 + i * 0x10));
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
    target_blocks.push_back(bb);
  }

  auto *bounds_bb = llvm::BasicBlock::Create(Ctx, "bounds_check", F);
  auto *middle_bb = llvm::BasicBlock::Create(Ctx, "middle", F);
  auto *switch_bb = llvm::BasicBlock::Create(Ctx, "switch_bb", F);
  auto *default_bb = llvm::BasicBlock::Create(Ctx, "default_bb", F);

  // bounds_check: icmp ult %idx, 4 → middle / default
  llvm::IRBuilder<> B(bounds_bb);
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr, "idx");
  auto *cmp = B.CreateICmpULT(idx, llvm::ConstantInt::get(i64_ty, 4));
  B.CreateCondBr(cmp, middle_bb, default_bb);

  // middle: unconditional branch to switch_bb (simulates extra block)
  B.SetInsertPoint(middle_bb);
  B.CreateBr(switch_bb);

  // switch_bb: table load + dispatch_jump
  B.SetInsertPoint(switch_bb);
  auto *scaled = B.CreateShl(idx, llvm::ConstantInt::get(i64_ty, 3));
  auto *addr = B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140040000));
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr, "entry_val");
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  // default_bb
  B.SetInsertPoint(default_bb);
  auto *def_result = B.CreateCall(
      dispatch, {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
  B.CreateRet(def_result);

  bounds_bb->moveBefore(&F->getEntryBlock());

  uint64_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = 0x140003100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140040000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  // The bounds check is two blocks up — enhanced computeIndexRange should find it.
  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(RecoverJumpTablesTest, BoundsFromULE) {
  // Index bounded by: icmp ule %idx, 3 (bound = 4).
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140004000", *M);

  llvm::SmallVector<llvm::BasicBlock *, 4> target_blocks;
  for (unsigned i = 0; i < 4; ++i) {
    char name[64];
    snprintf(name, sizeof(name), "block_%llx",
             (unsigned long long)(0x140004100 + i * 0x10));
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
    target_blocks.push_back(bb);
  }

  auto *bounds_bb = llvm::BasicBlock::Create(Ctx, "bounds_check", F);
  auto *switch_bb = llvm::BasicBlock::Create(Ctx, "switch_bb", F);
  auto *default_bb = llvm::BasicBlock::Create(Ctx, "default_bb", F);

  // bounds_check: icmp ule %idx, 3
  llvm::IRBuilder<> B(bounds_bb);
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr, "idx");
  auto *cmp = B.CreateICmpULE(idx, llvm::ConstantInt::get(i64_ty, 3));
  B.CreateCondBr(cmp, switch_bb, default_bb);

  B.SetInsertPoint(switch_bb);
  auto *scaled = B.CreateShl(idx, llvm::ConstantInt::get(i64_ty, 3));
  auto *addr = B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140050000));
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr, "entry_val");
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  B.SetInsertPoint(default_bb);
  auto *def_result = B.CreateCall(
      dispatch, {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
  B.CreateRet(def_result);

  bounds_bb->moveBefore(&F->getEntryBlock());

  uint64_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = 0x140004100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140050000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

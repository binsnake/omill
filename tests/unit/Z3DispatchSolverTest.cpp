#if OMILL_ENABLE_Z3

#include "omill/Passes/Z3DispatchSolver.h"

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

class Z3DispatchSolverTest : public ::testing::Test {
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
    auto *ft =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
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
        omill::Z3DispatchSolverPass()));
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
};

TEST_F(Z3DispatchSolverTest, ResolvesDirectArithmetic) {
  // dispatch_jump target = add(shl(idx, 4), base)
  // where idx is bounded by icmp ult idx, 3.
  // Z3 should enumerate the 3 concrete target values.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  // Create 3 target blocks.
  for (unsigned i = 0; i < 3; ++i) {
    uint64_t addr = 0x140001100 + i * 0x10;
    char name[64];
    snprintf(name, sizeof(name), "block_%llx", (unsigned long long)addr);
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
  }

  auto *bounds_bb = llvm::BasicBlock::Create(Ctx, "bounds_check", F);
  auto *switch_bb = llvm::BasicBlock::Create(Ctx, "switch_bb", F);
  auto *default_bb = llvm::BasicBlock::Create(Ctx, "default_bb", F);

  // bounds_check: br (idx < 3), switch_bb, default_bb
  llvm::IRBuilder<> B(bounds_bb);
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr, "idx");
  auto *cmp = B.CreateICmpULT(idx, llvm::ConstantInt::get(i64_ty, 3));
  B.CreateCondBr(cmp, switch_bb, default_bb);

  // switch_bb: target = idx * 0x10 + 0x140001100
  B.SetInsertPoint(switch_bb);
  auto *scaled = B.CreateMul(idx, llvm::ConstantInt::get(i64_ty, 0x10));
  auto *target =
      B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140001100));
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  // default_bb
  B.SetInsertPoint(default_bb);
  auto *def_result = B.CreateCall(
      dispatch,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
  B.CreateRet(def_result);

  bounds_bb->moveBefore(&F->getEntryBlock());

  // No binary memory needed — targets are pure arithmetic.
  omill::BinaryMemoryMap map;
  // Add a dummy region so the pass doesn't bail out on empty map.
  uint8_t dummy = 0;
  map.addRegion(0x140000000, &dummy, 1);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 3u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(Z3DispatchSolverTest, SkipsConstantTarget) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140002000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *result = B.CreateCall(
      dispatch,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0x140003000),
       F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  uint8_t dummy = 0;
  map.addRegion(0x140000000, &dummy, 1);
  runPass(M.get(), std::move(map));

  EXPECT_EQ(countDispatchJumps(F), 1u);
  EXPECT_FALSE(hasSwitchInst(F));
}

TEST_F(Z3DispatchSolverTest, SkipsNoBinaryMemory) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140003000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *raw_ptr = B.CreateAlloca(i64_ty);
  auto *raw = B.CreateLoad(i64_ty, raw_ptr, "raw");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), raw, F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  runPass(M.get(), std::move(map));

  EXPECT_EQ(countDispatchJumps(F), 1u);
  EXPECT_FALSE(hasSwitchInst(F));
}

TEST_F(Z3DispatchSolverTest, SkipsUnconstrainedTarget) {
  // dispatch_jump with a raw load (no path constraints) should be skipped
  // because Z3 would find > 256 solutions.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140004000", *M);

  // No bounds check — the target is a raw load.
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *ptr = B.CreateAlloca(i64_ty);
  auto *load = B.CreateLoad(i64_ty, ptr, "raw_target");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), load, F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  uint8_t dummy = 0;
  map.addRegion(0x140000000, &dummy, 1);
  runPass(M.get(), std::move(map));

  // Should be skipped (too many solutions).
  EXPECT_EQ(countDispatchJumps(F), 1u);
  EXPECT_FALSE(hasSwitchInst(F));
}

TEST_F(Z3DispatchSolverTest, ResolvesWithAndMask) {
  // target = and(load, 3) * 0x10 + base
  // AND mask constrains index to [0, 3].
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140005000", *M);

  // Create 4 target blocks.
  for (unsigned i = 0; i < 4; ++i) {
    uint64_t addr = 0x140005100 + i * 0x10;
    char name[64];
    snprintf(name, sizeof(name), "block_%llx", (unsigned long long)addr);
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
  }

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  entry->moveBefore(&F->getEntryBlock());

  llvm::IRBuilder<> B(entry);
  auto *raw_ptr = B.CreateAlloca(i64_ty);
  auto *raw = B.CreateLoad(i64_ty, raw_ptr, "raw");
  // AND mask → only values 0-3 possible.
  auto *idx = B.CreateAnd(raw, llvm::ConstantInt::get(i64_ty, 3), "idx");
  auto *scaled = B.CreateMul(idx, llvm::ConstantInt::get(i64_ty, 0x10));
  auto *target =
      B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140005100));
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  uint8_t dummy = 0;
  map.addRegion(0x140000000, &dummy, 1);
  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(Z3DispatchSolverTest, ResolvesInterFunction) {
  // Two functions: dispatch_jump from sub_A targets sub_B.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  // Target function.
  auto *TargetF = llvm::Function::Create(liftedFnType(),
                                          llvm::Function::ExternalLinkage,
                                          "sub_140002000", *M);
  auto *tgt_entry = llvm::BasicBlock::Create(Ctx, "entry", TargetF);
  llvm::IRBuilder<>(tgt_entry).CreateRet(TargetF->getArg(2));

  // Source function.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *bounds_bb = llvm::BasicBlock::Create(Ctx, "bounds_check", F);
  auto *switch_bb = llvm::BasicBlock::Create(Ctx, "switch_bb", F);
  auto *default_bb = llvm::BasicBlock::Create(Ctx, "default_bb", F);

  llvm::IRBuilder<> B(bounds_bb);
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr, "idx");
  auto *cmp = B.CreateICmpULT(idx, llvm::ConstantInt::get(i64_ty, 1));
  B.CreateCondBr(cmp, switch_bb, default_bb);

  // Only one target: 0x140002000 (sub_B).
  B.SetInsertPoint(switch_bb);
  auto *target = llvm::ConstantInt::get(i64_ty, 0x140002000);
  // But we need a non-constant target for the solver to kick in.
  // Use: target = idx * 0 + 0x140002000 (add(mul(idx, 0), const)).
  auto *computed_target = B.CreateAdd(
      B.CreateMul(idx, llvm::ConstantInt::get(i64_ty, 0)),
      llvm::ConstantInt::get(i64_ty, 0x140002000));
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), computed_target, F->getArg(2)});
  B.CreateRet(result);

  B.SetInsertPoint(default_bb);
  auto *def_result = B.CreateCall(
      dispatch,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
  B.CreateRet(def_result);

  omill::BinaryMemoryMap map;
  uint8_t dummy = 0;
  map.addRegion(0x140000000, &dummy, 1);
  runPass(M.get(), std::move(map));

  // The solver should resolve the inter-function tail call.
  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(Z3DispatchSolverTest, VerifiesMultipleDispatches) {
  // Two dispatch_jumps in the same function — both should be resolved.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140006000", *M);

  // 4 target blocks.
  for (unsigned i = 0; i < 4; ++i) {
    uint64_t addr = 0x140006100 + i * 0x10;
    char name[64];
    snprintf(name, sizeof(name), "block_%llx", (unsigned long long)addr);
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
  }

  // First dispatch (AND mask bound).
  auto *bb1 = llvm::BasicBlock::Create(Ctx, "dispatch1", F);
  llvm::IRBuilder<> B1(bb1);
  auto *ptr1 = B1.CreateAlloca(i64_ty);
  auto *raw1 = B1.CreateLoad(i64_ty, ptr1);
  auto *idx1 = B1.CreateAnd(raw1, llvm::ConstantInt::get(i64_ty, 1));
  auto *target1 =
      B1.CreateAdd(B1.CreateMul(idx1, llvm::ConstantInt::get(i64_ty, 0x10)),
                   llvm::ConstantInt::get(i64_ty, 0x140006100));
  auto *call1 =
      B1.CreateCall(dispatch, {F->getArg(0), target1, F->getArg(2)});
  B1.CreateRet(call1);

  // Second dispatch (icmp bound).
  auto *bounds2 = llvm::BasicBlock::Create(Ctx, "bounds2", F);
  auto *bb2 = llvm::BasicBlock::Create(Ctx, "dispatch2", F);
  auto *def2 = llvm::BasicBlock::Create(Ctx, "def2", F);

  llvm::IRBuilder<> B2(bounds2);
  auto *ptr2 = B2.CreateAlloca(i64_ty);
  auto *idx2 = B2.CreateLoad(i64_ty, ptr2);
  auto *cmp2 = B2.CreateICmpULT(idx2, llvm::ConstantInt::get(i64_ty, 2));
  B2.CreateCondBr(cmp2, bb2, def2);

  B2.SetInsertPoint(bb2);
  auto *target2 =
      B2.CreateAdd(B2.CreateMul(idx2, llvm::ConstantInt::get(i64_ty, 0x10)),
                   llvm::ConstantInt::get(i64_ty, 0x140006120));
  auto *call2 =
      B2.CreateCall(dispatch, {F->getArg(0), target2, F->getArg(2)});
  B2.CreateRet(call2);

  B2.SetInsertPoint(def2);
  auto *def_result2 = B2.CreateCall(
      dispatch,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
  B2.CreateRet(def_result2);

  bb1->moveBefore(&F->getEntryBlock());

  omill::BinaryMemoryMap map;
  uint8_t dummy = 0;
  map.addRegion(0x140000000, &dummy, 1);
  runPass(M.get(), std::move(map));

  // Count switches — should have at least 2.
  unsigned switch_count = 0;
  for (auto &BB : *F)
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_count;
  EXPECT_GE(switch_count, 2u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

#endif  // OMILL_ENABLE_Z3

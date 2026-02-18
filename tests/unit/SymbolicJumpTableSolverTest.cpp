#include "omill/Passes/ResolveAndLowerControlFlow.h"

#include <llvm/Analysis/ScalarEvolution.h>
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

class SymbolicJumpTableSolverTest : public ::testing::Test {
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
        omill::ResolveAndLowerControlFlowPass(omill::ResolvePhases::SymbolicSolve)));
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

TEST_F(SymbolicJumpTableSolverTest, ResolvesWithAndMaskBound) {
  // The solver should use pattern-based bounding (AND mask)
  // to resolve a jump table.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  // Create target blocks.
  for (unsigned i = 0; i < 4; ++i) {
    char name[64];
    snprintf(name, sizeof(name), "block_%llx",
             (unsigned long long)(0x140001100 + i * 0x10));
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
  }

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  entry->moveBefore(&F->getEntryBlock());

  llvm::IRBuilder<> B(entry);
  auto *raw_ptr = B.CreateAlloca(i64_ty);
  auto *raw = B.CreateLoad(i64_ty, raw_ptr, "raw");
  auto *idx = B.CreateAnd(raw, llvm::ConstantInt::get(i64_ty, 3), "idx");
  auto *scaled = B.CreateShl(idx, llvm::ConstantInt::get(i64_ty, 3));
  auto *addr =
      B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140020000));
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr, "entry_val");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  uint64_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = 0x140001100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(SymbolicJumpTableSolverTest, ResolvesWithICmpBound) {
  // Standard pattern with icmp — solver should handle this as fallback.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140006000", *M);

  for (unsigned i = 0; i < 4; ++i) {
    char name[64];
    snprintf(name, sizeof(name), "block_%llx",
             (unsigned long long)(0x140006100 + i * 0x10));
    auto *bb = llvm::BasicBlock::Create(Ctx, name, F);
    llvm::IRBuilder<>(bb).CreateRet(F->getArg(2));
  }

  auto *bounds_bb = llvm::BasicBlock::Create(Ctx, "bounds_check", F);
  auto *switch_bb = llvm::BasicBlock::Create(Ctx, "switch_bb", F);
  auto *default_bb = llvm::BasicBlock::Create(Ctx, "default_bb", F);

  llvm::IRBuilder<> B(bounds_bb);
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr, "idx");
  auto *cmp = B.CreateICmpULT(idx, llvm::ConstantInt::get(i64_ty, 4));
  B.CreateCondBr(cmp, switch_bb, default_bb);

  B.SetInsertPoint(switch_bb);
  auto *scaled = B.CreateShl(idx, llvm::ConstantInt::get(i64_ty, 3));
  auto *addr =
      B.CreateAdd(scaled, llvm::ConstantInt::get(i64_ty, 0x140060000));
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr, "entry_val");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  B.SetInsertPoint(default_bb);
  auto *def_result = B.CreateCall(
      dispatch,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0), F->getArg(2)});
  B.CreateRet(def_result);

  bounds_bb->moveBefore(&F->getEntryBlock());

  uint64_t table[4];
  for (unsigned i = 0; i < 4; ++i)
    table[i] = 0x140006100 + i * 0x10;

  omill::BinaryMemoryMap map;
  map.addRegion(0x140060000, reinterpret_cast<const uint8_t *>(table), 32);

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasSwitchInst(F));
  EXPECT_EQ(countSwitchCases(F), 4u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(SymbolicJumpTableSolverTest, SkipsConstantTarget) {
  // Constant targets should be left for ResolveDispatchTargets.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140007000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *result = B.CreateCall(
      dispatch,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0x140001000),
       F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;

  unsigned before = countDispatchJumps(F);
  runPass(M.get(), std::move(map));

  // Should remain unchanged.
  EXPECT_EQ(countDispatchJumps(F), before);
  EXPECT_FALSE(hasSwitchInst(F));
}

TEST_F(SymbolicJumpTableSolverTest, SkipsDynamicBase) {
  // Non-constant base should not be resolved.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);
  createDispatchJumpDecl(*M);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140008000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *idx_ptr = B.CreateAlloca(i64_ty);
  auto *idx = B.CreateLoad(i64_ty, idx_ptr);
  auto *scaled = B.CreateShl(idx, B.getInt64(3));
  auto *addr = B.CreateAdd(scaled, F->getArg(1));  // dynamic base
  auto *ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, ptr);
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  uint64_t dummy[4] = {0};
  map.addRegion(0x140020000, reinterpret_cast<const uint8_t *>(dummy), 32);

  unsigned before = countDispatchJumps(F);
  runPass(M.get(), std::move(map));

  EXPECT_EQ(countDispatchJumps(F), before);
  EXPECT_FALSE(hasSwitchInst(F));
}

}  // namespace

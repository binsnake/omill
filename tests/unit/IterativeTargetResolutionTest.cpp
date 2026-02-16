#include "omill/Passes/IterativeTargetResolution.h"

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

class IterativeTargetResolutionTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  llvm::Function *createDispatchCallDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_call", M);
  }

  llvm::Function *createDispatchJumpDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_jump", M);
  }

  llvm::PreservedAnalyses runPass(llvm::Module *M,
                                  omill::BinaryMemoryMap map = {},
                                  unsigned max_iter = 10) {
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
    MPM.addPass(omill::IterativeTargetResolutionPass(max_iter));
    return MPM.run(*M, MAM);
  }

  unsigned countUnresolvedDispatches(llvm::Module &M) {
    unsigned count = 0;
    for (auto &F : M)
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
            if (auto *callee = CI->getCalledFunction()) {
              auto name = callee->getName();
              if (name == "__omill_dispatch_call" ||
                  name == "__omill_dispatch_jump")
                ++count;
            }
    return count;
  }

  bool hasDirectCallTo(llvm::Function *F, llvm::StringRef fn_name) {
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = CI->getCalledFunction())
            if (callee->getName() == fn_name)
              return true;
    return false;
  }
};

TEST_F(IterativeTargetResolutionTest, NoDispatches_PreservesAll) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  // A simple function with no dispatch calls.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<>(entry).CreateRet(F->getArg(2));

  auto result = runPass(M.get());

  // No dispatches → PreservedAnalyses::all() (no changes made).
  EXPECT_TRUE(result.areAllPreserved());
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(IterativeTargetResolutionTest, ConstantTarget_Resolved) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Create target function.
  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_140002000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Caller with dispatch_call(state, 0x140002000, mem).
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), B.getInt64(0x140002000), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countUnresolvedDispatches(*M));

  runPass(M.get());

  // Constant target should be resolved in first iteration.
  EXPECT_EQ(0u, countUnresolvedDispatches(*M));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(IterativeTargetResolutionTest, UnresolvableTarget_StopsAtFixpoint) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Caller with dynamic target (function arg, not constant).
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), F->getArg(1), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countUnresolvedDispatches(*M));

  runPass(M.get(), {}, 5);

  // Cannot resolve dynamic target — should still have 1 dispatch.
  EXPECT_EQ(1u, countUnresolvedDispatches(*M));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(IterativeTargetResolutionTest, MultipleIterations_MakesProgress) {
  // Target = load(inttoptr(0x140010000)) + 0x100
  // Requires ConstantMemoryFolding + InstCombine before resolution.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_140020000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *addr_ptr = B.CreateIntToPtr(B.getInt64(0x140010000), ptr_ty);
  auto *loaded = B.CreateLoad(i64_ty, addr_ptr, "indirect_val");
  auto *target = B.CreateAdd(loaded, B.getInt64(0x100), "computed_target");

  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countUnresolvedDispatches(*M));

  // Binary memory: 0x140010000 contains 0x14001FF00 (LE).
  omill::BinaryMemoryMap map;
  uint64_t stored_val = 0x14001FF00ULL;
  map.addRegion(0x140010000, reinterpret_cast<const uint8_t *>(&stored_val),
                8);

  runPass(M.get(), std::move(map), 10);

  // load(0x140010000) + 0x100 = 0x14001FF00 + 0x100 = 0x140020000
  EXPECT_EQ(0u, countUnresolvedDispatches(*M));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

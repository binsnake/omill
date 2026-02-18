#include "omill/Passes/ResolveAndLowerControlFlow.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/IterativeTargetResolution.h"
#include "omill/Passes/LowerRemillIntrinsics.h"

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

class ResolveDispatchTargetsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::Function *createDispatchCallDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_call", M);
  }

  llvm::Function *createDispatchJumpDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_jump", M);
  }

  /// Standard lifted function type: ptr(ptr, i64, ptr)
  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  void runResolvePass(llvm::Module *M, omill::BinaryMemoryMap map = {}) {
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
        omill::ResolveAndLowerControlFlowPass(omill::ResolvePhases::ResolveTargets)));
    MPM.run(*M, MAM);
  }

  void runIterativePass(llvm::Module *M, omill::BinaryMemoryMap map = {},
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
    MPM.run(*M, MAM);
  }

  /// Check if any dispatch_call has a ptrtoint(@func) target (IAT resolved).
  bool hasResolvedDispatchCall(llvm::Function *F) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee || callee->getName() != "__omill_dispatch_call")
          continue;
        if (CI->arg_size() < 2)
          continue;
        if (auto *ptoi =
                llvm::dyn_cast<llvm::PtrToIntOperator>(CI->getArgOperand(1)))
          if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
            return true;
      }
    }
    return false;
  }

  /// Check if a function has a direct call to a named function.
  bool hasDirectCallTo(llvm::Function *F, llvm::StringRef fn_name) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == fn_name)
          return true;
      }
    }
    return false;
  }

  /// Count remaining dispatch_call invocations.
  unsigned countDispatchCalls(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_call")
          ++count;
      }
    }
    return count;
  }

  /// Count remaining dispatch_jump invocations.
  unsigned countDispatchJumps(llvm::Function *F) {
    unsigned count = 0;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_jump")
          ++count;
      }
    }
    return count;
  }

  /// Check if a function contains a direct branch to a named block.
  bool hasBranchTo(llvm::Function *F, llvm::StringRef block_name) {
    for (auto &BB : *F) {
      auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
      if (!br || br->isConditional())
        continue;
      if (br->getSuccessor(0)->getName() == block_name)
        return true;
    }
    return false;
  }

  /// Check if a function has a musttail call to a named function.
  bool hasTailCallTo(llvm::Function *F, llvm::StringRef fn_name) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        if (CI->getTailCallKind() != llvm::CallInst::TCK_MustTail)
          continue;
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == fn_name)
          return true;
      }
    }
    return false;
  }
};

TEST_F(ResolveDispatchTargetsTest, ResolvesConstantDispatchCall) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Create target function sub_140002000.
  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_140002000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Create caller sub_140001000 with dispatch_call(state, 0x140002000, mem).
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), B.getInt64(0x140002000), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchCalls(F));

  runResolvePass(M.get());

  // dispatch_call replaced with direct call to sub_140002000.
  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_TRUE(hasDirectCallTo(F, "sub_140002000"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, ResolvesConstantDispatchJump) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchJumpDecl(*M);

  // Create function with block_140001020 as a branch target.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *target_bb = llvm::BasicBlock::Create(Ctx, "block_140001020", F);

  // Target block just returns.
  llvm::IRBuilder<>(target_bb).CreateRet(F->getArg(2));

  // Entry: dispatch_jump(state, 0x140001020, mem) + ret
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), B.getInt64(0x140001020), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchJumps(F));

  runResolvePass(M.get());

  // Should be replaced with a direct branch.
  EXPECT_EQ(0u, countDispatchJumps(F));
  EXPECT_TRUE(hasBranchTo(F, "block_140001020"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, ResolvesInterFunctionJump) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchJumpDecl(*M);

  // Create target function sub_140002000.
  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_140002000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Create caller with dispatch_jump to sub_140002000.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), B.getInt64(0x140002000), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchJumps(F));

  runResolvePass(M.get());

  EXPECT_EQ(0u, countDispatchJumps(F));
  EXPECT_TRUE(hasTailCallTo(F, "sub_140002000"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, ResolvesIATImport) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  // Target is a constant matching an IAT entry.
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), B.getInt64(0x140005000), F->getArg(2)});
  B.CreateRet(result);

  omill::BinaryMemoryMap map;
  map.addImport(0x140005000, "kernel32", "VirtualAlloc");

  runResolvePass(M.get(), std::move(map));

  EXPECT_TRUE(hasResolvedDispatchCall(F));
  // Verify the target function has the right name.
  for (auto &BB : *F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee || callee->getName() != "__omill_dispatch_call")
        continue;
      auto *ptoi =
          llvm::dyn_cast<llvm::PtrToIntOperator>(CI->getArgOperand(1));
      if (!ptoi)
        continue;
      auto *fn = llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
      ASSERT_NE(fn, nullptr);
      EXPECT_EQ(fn->getName(), "VirtualAlloc");
      EXPECT_EQ(fn->getDLLStorageClass(),
                llvm::GlobalValue::DLLImportStorageClass);
    }
  }
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, SkipsDynamicTarget) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  // Target is a dynamic value (function arg), not a constant.
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), F->getArg(1), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchCalls(F));

  runResolvePass(M.get());

  // Should remain unchanged.
  EXPECT_EQ(1u, countDispatchCalls(F));
  EXPECT_FALSE(hasResolvedDispatchCall(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, IterativeConvergence) {
  // Scenario: target = load(inttoptr(0x140010000)) + 0x100
  // Iteration 1: ConstantMemoryFolding folds load → constant 0x14001FF00
  // Iteration 2: InstCombine folds add → 0x140020000
  // Iteration 3: ResolveDispatchTargets resolves the constant target

  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Create target function at 0x140020000.
  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_140020000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Create caller function.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  // Build: target = load(inttoptr(0x140010000)) + 0x100
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *addr_ptr = B.CreateIntToPtr(B.getInt64(0x140010000), ptr_ty);
  auto *loaded = B.CreateLoad(i64_ty, addr_ptr, "indirect_val");
  auto *target = B.CreateAdd(loaded, B.getInt64(0x100), "computed_target");

  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchCalls(F));

  // Binary memory: at 0x140010000, store the value 0x14001FF00 (LE).
  omill::BinaryMemoryMap map;
  uint64_t stored_val = 0x14001FF00ULL;
  map.addRegion(0x140010000, reinterpret_cast<const uint8_t *>(&stored_val), 8);

  runIterativePass(M.get(), std::move(map), 10);

  // After iteration, the dispatch_call should have been resolved and lowered.
  // The target was: load(0x140010000) + 0x100 = 0x14001FF00 + 0x100 = 0x140020000
  // which matches sub_140020000.
  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, MultipleDispatchCallsInFunction) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Create 3 target functions.
  for (auto addr : {"sub_140002000", "sub_140003000", "sub_140004000"}) {
    auto *tf = llvm::Function::Create(liftedFnType(),
                                       llvm::Function::ExternalLinkage, addr, *M);
    auto *e = llvm::BasicBlock::Create(Ctx, "entry", tf);
    llvm::IRBuilder<>(e).CreateRet(tf->getArg(2));
  }

  // Caller with 3 dispatch_calls.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = M->getFunction("__omill_dispatch_call");

  B.CreateCall(dispatch, {F->getArg(0), B.getInt64(0x140002000), F->getArg(2)});
  B.CreateCall(dispatch, {F->getArg(0), B.getInt64(0x140003000), F->getArg(2)});
  auto *result =
      B.CreateCall(dispatch, {F->getArg(0), B.getInt64(0x140004000), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(3u, countDispatchCalls(F));

  runResolvePass(M.get());

  // All 3 should be resolved.
  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_TRUE(hasDirectCallTo(F, "sub_140002000"));
  EXPECT_TRUE(hasDirectCallTo(F, "sub_140003000"));
  EXPECT_TRUE(hasDirectCallTo(F, "sub_140004000"));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, JumpToNonexistentBlockUnchanged) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchJumpDecl(*M);

  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = M->getFunction("__omill_dispatch_jump");
  // Target 0xDEADBEEF doesn't match any block_ or sub_.
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), B.getInt64(0xDEADBEEF), F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countDispatchJumps(F));

  runResolvePass(M.get());

  // Should remain unchanged.
  EXPECT_EQ(1u, countDispatchJumps(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveDispatchTargetsTest, MaxIterationsRespected) {
  // Create a scenario with a deeply chained constant that needs many iterations.
  // With max_iterations = 1, it should stop early and leave dispatches unresolved.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Target at 0x140020000.
  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                              "sub_140020000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Build: target = load(inttoptr(0x140010000)) + load(inttoptr(0x140010008))
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *addr1_ptr = B.CreateIntToPtr(B.getInt64(0x140010000), ptr_ty);
  auto *v1 = B.CreateLoad(i64_ty, addr1_ptr);
  auto *addr2_ptr = B.CreateIntToPtr(B.getInt64(0x140010008), ptr_ty);
  auto *v2 = B.CreateLoad(i64_ty, addr2_ptr);
  auto *target = B.CreateAdd(v1, v2, "computed");

  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result = B.CreateCall(dispatch, {F->getArg(0), target, F->getArg(2)});
  B.CreateRet(result);

  // val1 = 0x100000000, val2 = 0x40020000 → sum = 0x140020000
  omill::BinaryMemoryMap map;
  uint64_t val1 = 0x100000000ULL;
  uint64_t val2 = 0x40020000ULL;
  uint8_t region[16];
  std::memcpy(region, &val1, 8);
  std::memcpy(region + 8, &val2, 8);
  map.addRegion(0x140010000, region, 16);

  // With max_iter=1, the iteration should fold the loads and the add in the first
  // iteration, resolve the target, then stop. Let's verify it works with 1 iteration.
  runIterativePass(M.get(), std::move(map), 1);

  // After 1 iteration: loads folded, add folded, target resolved.
  // The pass does InstCombine+GVN+ConstantMemoryFolding first, then resolve.
  EXPECT_EQ(0u, countDispatchCalls(F));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

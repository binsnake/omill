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
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/BC/TraceLiftAnalysis.h"

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

class IterativeTargetResolutionTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  std::shared_ptr<omill::IterativeLiftingSession> Session;

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
    MAM.registerPass([] { return omill::CallGraphAnalysis(); });
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });
    MAM.registerPass([] { return omill::BlockLiftAnalysis(); });
    MAM.registerPass([] { return omill::TraceLiftAnalysis(); });
    Session = std::make_shared<omill::IterativeLiftingSession>("itr-test");
    MAM.registerPass([this] {
      return omill::IterativeLiftingSessionAnalysis(Session);
    });

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

  llvm::Function *createStateFieldModel(llvm::Module &M) {
    auto *bb_fn = M.getFunction("__remill_basic_block");
    if (bb_fn)
      return bb_fn;

    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *bb_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    bb_fn = llvm::Function::Create(
        bb_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *state = bb_fn->getArg(0);
    struct RegField {
      const char *name;
      uint64_t offset;
    };
    for (auto field : {RegField{"RAX", 0}, RegField{"RCX", 16},
                       RegField{"RDX", 24}, RegField{"R8", 64},
                       RegField{"R9", 72}}) {
      B.CreateConstGEP1_64(B.getInt8Ty(), state, field.offset, field.name);
    }
    B.CreateRet(bb_fn->getArg(2));
    return bb_fn;
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
  ASSERT_TRUE(Session);
  ASSERT_NE(Session->graph().lookupNode(0x140001000), nullptr);
  ASSERT_NE(Session->graph().lookupNode(0x140002000), nullptr);
  bool found_direct = false;
  for (auto *edge : Session->graph().outgoingEdges(0x140001000)) {
    if (edge->kind == omill::LiftEdgeKind::kDirectCall &&
        edge->target_pc == 0x140002000 && edge->resolved) {
      found_direct = true;
    }
  }
  EXPECT_TRUE(found_direct);
}

TEST_F(IterativeTargetResolutionTest, UnresolvableTarget_StopsAtFixpoint) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createDispatchCallDecl(*M);

  // Caller with dynamic target (load from State pointer — truly unresolvable).
  // We can't use arg 1 because evaluateToConstant resolves arg 1 of sub_*
  // functions to the entry PC extracted from the function name.
  auto *F = llvm::Function::Create(liftedFnType(),
                                    llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dyn_target = B.CreateLoad(i64_ty, F->getArg(0), "dyn_target");
  auto *dispatch = M->getFunction("__omill_dispatch_call");
  auto *result = B.CreateCall(
      dispatch, {F->getArg(0), dyn_target, F->getArg(2)});
  B.CreateRet(result);

  EXPECT_EQ(1u, countUnresolvedDispatches(*M));

  runPass(M.get(), {}, 5);

  // Cannot resolve dynamic target — should still have 1 dispatch.
  EXPECT_EQ(1u, countUnresolvedDispatches(*M));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  ASSERT_TRUE(Session);
  bool found_unresolved = false;
  for (auto *edge : Session->graph().outgoingEdges(0x140001000)) {
    if (edge->kind == omill::LiftEdgeKind::kIndirectCall &&
        edge->target_pc == 0 && !edge->resolved) {
      found_unresolved = true;
    }
  }
  EXPECT_TRUE(found_unresolved);
  auto rounds = Session->roundSummaries();
  ASSERT_FALSE(rounds.empty());
  EXPECT_TRUE(rounds.back().stalled);
  EXPECT_EQ(rounds.back().dynamic_unresolved, 1u);
  EXPECT_EQ(rounds.back().missing_targets, 0u);
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
                8, /*read_only=*/true);

  runPass(M.get(), std::move(map), 10);

  // load(0x140010000) + 0x100 = 0x14001FF00 + 0x100 = 0x140020000
  EXPECT_EQ(0u, countUnresolvedDispatches(*M));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(IterativeTargetResolutionTest,
       IPCPResolvesCallerProvidedStateConstantInSameRun) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(kDataLayout);

  createStateFieldModel(*M);
  createDispatchCallDecl(*M);

  auto *target_fn =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                             "sub_140003000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  auto *callee =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                             "sub_140002000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", callee);
    llvm::IRBuilder<> B(entry);
    auto *target_gep = B.CreateConstGEP1_64(B.getInt8Ty(), callee->getArg(0), 16);
    auto *target_pc = B.CreateLoad(B.getInt64Ty(), target_gep, "target_pc");
    auto *dispatch = M->getFunction("__omill_dispatch_call");
    auto *result =
        B.CreateCall(dispatch, {callee->getArg(0), target_pc, callee->getArg(2)});
    B.CreateRet(result);
  }

  auto *caller =
      llvm::Function::Create(liftedFnType(), llvm::Function::ExternalLinkage,
                             "sub_140001000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *target_gep = B.CreateConstGEP1_64(B.getInt8Ty(), caller->getArg(0), 16);
    B.CreateStore(B.getInt64(0x140003000), target_gep);
    auto *result =
        B.CreateCall(callee, {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(result);
  }

  EXPECT_EQ(1u, countUnresolvedDispatches(*M));

  runPass(M.get(), {}, 4);

  EXPECT_EQ(0u, countUnresolvedDispatches(*M));
  EXPECT_TRUE(hasDirectCallTo(callee, "sub_140003000"));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

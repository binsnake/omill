#include "omill/Passes/IterativeBlockDiscovery.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Omill.h"

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class IterativeBlockDiscoveryTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  std::shared_ptr<omill::IterativeLiftingSession> Session;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  void runPass(llvm::Module &M, unsigned max_iter = 5) {
    llvm::ModulePassManager MPM;
    MPM.addPass(omill::IterativeBlockDiscoveryPass(max_iter));

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
    omill::registerModuleAnalyses(MAM);
    Session = std::make_shared<omill::IterativeLiftingSession>("block-test");
    MAM.registerPass([this] {
      return omill::IterativeLiftingSessionAnalysis(Session);
    });
    Session = MAM.getResult<omill::IterativeLiftingSessionAnalysis>(M).session;

    MPM.run(M, MAM);
  }

  /// The standard lifted function type: (State*, i64, Memory*) -> Memory*
  llvm::FunctionType *getBlockFnType() {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);
    return llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
  }

  llvm::Function *declareBlockFn(llvm::Module &M, uint64_t addr) {
    char name[64];
    snprintf(name, sizeof(name), "blk_%llx", (unsigned long long)addr);
    auto *existing = M.getFunction(name);
    if (existing)
      return existing;
    return llvm::Function::Create(getBlockFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  name, &M);
  }

  llvm::Function *declareDispatch(llvm::Module &M, const char *name) {
    auto *fn = M.getFunction(name);
    if (fn)
      return fn;
    return llvm::Function::Create(getBlockFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  name, &M);
  }

  /// Count calls to __omill_dispatch_jump in the module.
  unsigned countDispatches(llvm::Module &M) {
    unsigned count = 0;
    for (auto &F : M) {
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          auto name = callee->getName();
          if (name == "__omill_dispatch_jump" ||
              name == "__omill_dispatch_call")
            ++count;
        }
      }
    }
    return count;
  }
};

// Test: dispatch_jump with constant target pointing to existing block-function
// gets replaced with musttail call.
TEST_F(IterativeBlockDiscoveryTest, ConstantDispatchResolved) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x1000);
  auto *fn2 = declareBlockFn(*M, 0x2000);
  auto *dispatch = declareDispatch(*M, "__omill_dispatch_jump");

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // blk_1000: call dispatch_jump(state, 0x2000, mem); ret
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch,
        {fn1->getArg(0), llvm::ConstantInt::get(i64Ty, 0x2000),
         fn1->getArg(2)});
    B.CreateRet(call);
  }

  // blk_2000: ret mem (simple terminal)
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn2);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn2->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  ASSERT_EQ(countDispatches(*M), 1u);

  runPass(*M);

  // The dispatch_jump should be resolved to a direct call.
  EXPECT_EQ(countDispatches(*M), 0u);

  // Verify the call to blk_2000 exists in blk_1000.
  bool found_direct_call = false;
  for (auto &BB : *fn1) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      if (call->getCalledFunction() == fn2) {
        found_direct_call = true;
        EXPECT_EQ(call->getTailCallKind(), llvm::CallInst::TCK_MustTail);
      }
    }
  }
  EXPECT_TRUE(found_direct_call);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  ASSERT_TRUE(Session);
  ASSERT_NE(Session->graph().lookupNode(0x1000), nullptr);
  ASSERT_NE(Session->graph().lookupNode(0x2000), nullptr);
  bool found_edge = false;
  for (auto *edge : Session->graph().outgoingEdges(0x1000)) {
    if (edge->target_pc == 0x2000 &&
        edge->kind == omill::LiftEdgeKind::kDirectBranch &&
        edge->resolved) {
      found_edge = true;
    }
  }
  EXPECT_TRUE(found_edge);
}

// Test: dispatch_jump with non-constant target is left unresolved.
TEST_F(IterativeBlockDiscoveryTest, NonConstantDispatchUnresolved) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x3000);
  auto *dispatch = declareDispatch(*M, "__omill_dispatch_jump");

  // blk_3000: call dispatch_jump(state, %pc_arg, mem); ret
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch,
        {fn1->getArg(0), fn1->getArg(1), fn1->getArg(2)});
    B.CreateRet(call);
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  // Still unresolved — the target is a function argument, not constant.
  EXPECT_EQ(countDispatches(*M), 1u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: No block-functions — pass is a no-op.
TEST_F(IterativeBlockDiscoveryTest, NoBlockFunctionsIsNoOp) {
  auto M = createModule();

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                   "regular", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(llvm::ConstantInt::get(i64Ty, 0));

  runPass(*M);

  EXPECT_EQ(M->getFunction("regular"), F);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Constant dispatch to non-existent block-function left unresolved.
TEST_F(IterativeBlockDiscoveryTest, ConstantDispatchToMissingBlock) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x4000);
  auto *dispatch = declareDispatch(*M, "__omill_dispatch_jump");
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // blk_4000: dispatch_jump(state, 0x9999, mem) — target doesn't exist
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch,
        {fn1->getArg(0), llvm::ConstantInt::get(i64Ty, 0x9999),
         fn1->getArg(2)});
    B.CreateRet(call);
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  // The target block doesn't exist, so dispatch remains.
  EXPECT_EQ(countDispatches(*M), 1u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  ASSERT_TRUE(Session);
  bool found_unresolved = false;
  for (auto *edge : Session->graph().outgoingEdges(0x4000)) {
    if (edge->kind == omill::LiftEdgeKind::kIndirectBranch &&
        edge->target_pc == 0x9999 && !edge->resolved) {
      found_unresolved = true;
    }
  }
  EXPECT_TRUE(found_unresolved);
}

// Test: dispatch_call with constant target gets resolved similarly.
TEST_F(IterativeBlockDiscoveryTest, DispatchCallResolved) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x5000);
  auto *fn_target = declareBlockFn(*M, 0x5050);
  auto *dispatch = declareDispatch(*M, "__omill_dispatch_call");
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch,
        {fn1->getArg(0), llvm::ConstantInt::get(i64Ty, 0x5050),
         fn1->getArg(2)});
    B.CreateRet(call);
  }

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn_target->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  EXPECT_EQ(countDispatches(*M), 0u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Constant propagation through add resolves dispatch after optimization.
TEST_F(IterativeBlockDiscoveryTest, ConstPropResolvesDispatch) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x6000);
  auto *fn2 = declareBlockFn(*M, 0x6100);
  auto *dispatch = declareDispatch(*M, "__omill_dispatch_jump");
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // blk_6000: %target = add 0x6000, 0x100; dispatch_jump(state, target, mem)
  // After InstCombine, %target should fold to 0x6100.
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *target = B.CreateAdd(
        llvm::ConstantInt::get(i64Ty, 0x6000),
        llvm::ConstantInt::get(i64Ty, 0x100));
    auto *call = B.CreateCall(dispatch,
        {fn1->getArg(0), target, fn1->getArg(2)});
    B.CreateRet(call);
  }

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn2);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn2->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  ASSERT_EQ(countDispatches(*M), 1u);

  runPass(*M);

  // After optimization + resolution, the dispatch should be resolved.
  EXPECT_EQ(countDispatches(*M), 0u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Multiple dispatches, some resolved some not.
TEST_F(IterativeBlockDiscoveryTest, PartialResolution) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x7000);
  auto *fn2 = declareBlockFn(*M, 0x7100);
  auto *dispatch_j = declareDispatch(*M, "__omill_dispatch_jump");
  auto *dispatch_c = declareDispatch(*M, "__omill_dispatch_call");
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // blk_7000: conditional: dispatch_call(state, 0x7100, mem)
  //                     or dispatch_jump(state, %unknown, mem)
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    auto *bb_const = llvm::BasicBlock::Create(Ctx, "const_path", fn1);
    auto *bb_dyn = llvm::BasicBlock::Create(Ctx, "dyn_path", fn1);

    llvm::IRBuilder<> B(entry);
    auto *cond = B.CreateICmpEQ(fn1->getArg(1),
                                 llvm::ConstantInt::get(i64Ty, 0));
    B.CreateCondBr(cond, bb_const, bb_dyn);

    B.SetInsertPoint(bb_const);
    auto *c1 = B.CreateCall(dispatch_c,
        {fn1->getArg(0), llvm::ConstantInt::get(i64Ty, 0x7100),
         fn1->getArg(2)});
    B.CreateRet(c1);

    B.SetInsertPoint(bb_dyn);
    auto *c2 = B.CreateCall(dispatch_j,
        {fn1->getArg(0), fn1->getArg(1), fn1->getArg(2)});
    B.CreateRet(c2);
  }

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn2);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn2->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  ASSERT_EQ(countDispatches(*M), 2u);

  runPass(*M);

  // One resolved, one still dynamic.
  EXPECT_EQ(countDispatches(*M), 1u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

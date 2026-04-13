#include "omill/Passes/MergeBlockFunctions.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class MergeBlockFunctionsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  void runPass(llvm::Module &M) {
    llvm::ModulePassManager MPM;
    MPM.addPass(omill::MergeBlockFunctionsPass());

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

    MPM.run(M, MAM);
  }

  /// The standard lifted function type: (State*, i64, Memory*) -> Memory*
  llvm::FunctionType *getBlockFnType() {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);
    // (ptr %state, i64 %pc, ptr %mem) -> ptr
    return llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
  }

  /// Create a block-function declaration.
  llvm::Function *declareBlockFn(llvm::Module &M, uint64_t addr) {
    char name[64];
    snprintf(name, sizeof(name), "blk_%llx", (unsigned long long)addr);
    auto *fn = llvm::Function::Create(getBlockFnType(),
                                      llvm::GlobalValue::ExternalLinkage,
                                      name, &M);
    return fn;
  }

  /// Create a dispatch function declaration.
  llvm::Function *declareDispatch(llvm::Module &M, const char *name) {
    auto *fn = M.getFunction(name);
    if (fn)
      return fn;
    return llvm::Function::Create(getBlockFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  name, &M);
  }
};

// Test: Two blocks chained by musttail call get merged into one function.
TEST_F(MergeBlockFunctionsTest, TwoBlockLinearChain) {
  auto M = createModule();

  // blk_1000: musttail call blk_1010; ret
  auto *fn1 = declareBlockFn(*M, 0x1000);
  auto *fn2 = declareBlockFn(*M, 0x1010);

  // Block 1: entry, musttail call to block 2
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(fn2, {fn1->getArg(0), fn1->getArg(1),
                                     fn1->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  // Block 2: ret mem arg (terminal block)
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn2);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn2->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  // A merged function should exist: sub_1000
  auto *merged = M->getFunction("sub_1000");
  ASSERT_NE(merged, nullptr);
  EXPECT_FALSE(merged->isDeclaration());
  // Merged function should have >1 basic block (two blocks merged).
  EXPECT_GE(merged->size(), 2u);

  // Original block-functions should be internalized.
  EXPECT_TRUE(fn1->hasInternalLinkage());
  EXPECT_TRUE(fn2->hasInternalLinkage());

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Three blocks forming a diamond (conditional branch).
TEST_F(MergeBlockFunctionsTest, DiamondCFG) {
  auto M = createModule();

  auto *fn_entry = declareBlockFn(*M, 0x2000);
  auto *fn_true = declareBlockFn(*M, 0x2010);
  auto *fn_false = declareBlockFn(*M, 0x2020);

  // Entry: conditional branch to true/false blocks (via musttail calls)
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_entry);
    auto *bb_true = llvm::BasicBlock::Create(Ctx, "taken", fn_entry);
    auto *bb_false = llvm::BasicBlock::Create(Ctx, "not_taken", fn_entry);

    llvm::IRBuilder<> B(entry);
    auto *cond = B.CreateICmpEQ(fn_entry->getArg(1),
                                 llvm::ConstantInt::get(
                                     llvm::Type::getInt64Ty(Ctx), 42));
    B.CreateCondBr(cond, bb_true, bb_false);

    // Taken -> musttail blk_2010
    B.SetInsertPoint(bb_true);
    auto *call_true = B.CreateCall(fn_true,
        {fn_entry->getArg(0), fn_entry->getArg(1), fn_entry->getArg(2)});
    call_true->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call_true);

    // Not taken -> musttail blk_2020
    B.SetInsertPoint(bb_false);
    auto *call_false = B.CreateCall(fn_false,
        {fn_entry->getArg(0), fn_entry->getArg(1), fn_entry->getArg(2)});
    call_false->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call_false);
  }

  // True block: ret
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_true);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn_true->getArg(2));
  }

  // False block: ret
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_false);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn_false->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  auto *merged = M->getFunction("sub_2000");
  ASSERT_NE(merged, nullptr);
  EXPECT_FALSE(merged->isDeclaration());
  EXPECT_GE(merged->size(), 3u);  // entry + true + false blocks

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Block ending with dispatch_jump is NOT an internal edge.
TEST_F(MergeBlockFunctionsTest, DispatchJumpPreserved) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x3000);
  auto *dispatch = declareDispatch(*M, "__omill_dispatch_jump");

  // Block: call __omill_dispatch_jump; ret (indirect jump, not merged)
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch, {fn1->getArg(0), fn1->getArg(1),
                                          fn1->getArg(2)});
    B.CreateRet(call);
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  // Single block with no internal edges — no merge needed, but it's still
  // a valid entry so it might get a sub_ wrapper (single block group).
  // The dispatch call should be preserved.
  bool found_dispatch = false;
  for (auto &F : *M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
          if (auto *callee = call->getCalledFunction()) {
            if (callee->getName() == "__omill_dispatch_jump")
              found_dispatch = true;
          }
        }
      }
    }
  }
  EXPECT_TRUE(found_dispatch);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: No block-functions — pass is a no-op.
TEST_F(MergeBlockFunctionsTest, NoBlockFunctionsIsNoOp) {
  auto M = createModule();

  // Create a regular function, not a block-function.
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                   "regular_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(llvm::ConstantInt::get(i64Ty, 42));

  runPass(*M);

  EXPECT_EQ(M->getFunction("regular_fn"), F);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Multiple independent traces get separate merged functions.
TEST_F(MergeBlockFunctionsTest, MultipleTracesIndependent) {
  auto M = createModule();

  // Trace A: blk_4000 -> blk_4010
  auto *fn_a1 = declareBlockFn(*M, 0x4000);
  auto *fn_a2 = declareBlockFn(*M, 0x4010);

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_a1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(fn_a2, {fn_a1->getArg(0), fn_a1->getArg(1),
                                       fn_a1->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_a2);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn_a2->getArg(2));
  }

  // Trace B: blk_5000 -> blk_5010
  auto *fn_b1 = declareBlockFn(*M, 0x5000);
  auto *fn_b2 = declareBlockFn(*M, 0x5010);

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_b1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(fn_b2, {fn_b1->getArg(0), fn_b1->getArg(1),
                                       fn_b1->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_b2);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn_b2->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  EXPECT_NE(M->getFunction("sub_4000"), nullptr);
  EXPECT_NE(M->getFunction("sub_5000"), nullptr);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Self-loop (block branches to itself).
TEST_F(MergeBlockFunctionsTest, SelfLoop) {
  auto M = createModule();

  auto *fn1 = declareBlockFn(*M, 0x6000);

  // Block: musttail call to itself
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn1);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(fn1, {fn1->getArg(0), fn1->getArg(1),
                                     fn1->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  // Should still produce a merged function (even if single block).
  // The self-musttail should be replaced with a branch to itself.
  auto *merged = M->getFunction("sub_6000");
  EXPECT_NE(merged, nullptr);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(MergeBlockFunctionsTest, PreservesOutputRootFromEntryBlock) {
  auto M = createModule();

  auto *entry_fn = declareBlockFn(*M, 0x7000);
  auto *next_fn = declareBlockFn(*M, 0x7010);
  entry_fn->addFnAttr("omill.output_root");

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", entry_fn);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(next_fn, {entry_fn->getArg(0), entry_fn->getArg(1),
                                        entry_fn->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", next_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(next_fn->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  auto *merged = M->getFunction("sub_7000");
  ASSERT_NE(merged, nullptr);
  EXPECT_TRUE(merged->hasFnAttribute("omill.output_root"));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(MergeBlockFunctionsTest, PreservesClosedRootSliceAttrsFromEntryBlock) {
  auto M = createModule();

  auto *entry_fn = declareBlockFn(*M, 0x7100);
  auto *next_fn = declareBlockFn(*M, 0x7110);
  entry_fn->addFnAttr("omill.closed_root_slice", "1");
  entry_fn->addFnAttr("omill.closed_root_slice_root", "1");

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", entry_fn);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(next_fn, {entry_fn->getArg(0), entry_fn->getArg(1),
                                        entry_fn->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", next_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(next_fn->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  auto *merged = M->getFunction("sub_7100");
  ASSERT_NE(merged, nullptr);
  EXPECT_TRUE(merged->hasFnAttribute("omill.closed_root_slice"));
  EXPECT_TRUE(merged->hasFnAttribute("omill.closed_root_slice_root"));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(MergeBlockFunctionsTest, OutputRootDrivesEntrySelectionInLoop) {
  auto M = createModule();

  auto *entry_fn = declareBlockFn(*M, 0x2000);
  auto *loop_fn = declareBlockFn(*M, 0x2010);
  entry_fn->addFnAttr("omill.output_root");

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", entry_fn);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(loop_fn, {entry_fn->getArg(0), entry_fn->getArg(1),
                                        entry_fn->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", loop_fn);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(entry_fn, {loop_fn->getArg(0), loop_fn->getArg(1),
                                         loop_fn->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  auto *merged = M->getFunction("sub_2000");
  ASSERT_NE(merged, nullptr);
  EXPECT_TRUE(merged->hasFnAttribute("omill.output_root"));
  EXPECT_EQ(M->getFunction("sub_2010"), nullptr);

  auto &entry_bb = merged->getEntryBlock();
  EXPECT_EQ(entry_bb.getName(), "block_2000");
  auto *entry_ret = llvm::dyn_cast<llvm::ReturnInst>(entry_bb.getTerminator());
  ASSERT_NE(entry_ret, nullptr);
  auto *entry_call = llvm::dyn_cast<llvm::CallInst>(entry_ret->getReturnValue());
  ASSERT_NE(entry_call, nullptr);
  ASSERT_NE(entry_call->getCalledFunction(), nullptr);
  EXPECT_EQ(entry_call->getCalledFunction()->getName(), "blk_2010");

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(MergeBlockFunctionsTest, RootedSingleBlockProducesMergedTrace) {
  auto M = createModule();

  auto *entry_fn = declareBlockFn(*M, 0x3000);
  entry_fn->addFnAttr("omill.output_root");

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", entry_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(entry_fn->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  auto *merged = M->getFunction("sub_3000");
  ASSERT_NE(merged, nullptr);
  EXPECT_TRUE(merged->hasFnAttribute("omill.output_root"));
  EXPECT_TRUE(entry_fn->hasInternalLinkage());
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(MergeBlockFunctionsTest, RootedSingleBlockWithInternalLoopPhis) {
  auto M = createModule();

  auto *entry_fn = declareBlockFn(*M, 0x8000);
  entry_fn->addFnAttr("omill.output_root");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", entry_fn);
  auto *loop = llvm::BasicBlock::Create(Ctx, "loop", entry_fn);
  auto *exit = llvm::BasicBlock::Create(Ctx, "exit", entry_fn);

  {
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);
  }

  {
    llvm::IRBuilder<> B(loop);
    auto *acc = B.CreatePHI(llvm::Type::getInt64Ty(Ctx), 2);
    auto *iters = B.CreatePHI(llvm::Type::getInt64Ty(Ctx), 2);
    acc->addIncoming(entry_fn->getArg(1), entry);
    iters->addIncoming(llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 0),
                       entry);

    auto *next_acc = B.CreateAdd(
        acc, llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 3));
    auto *next_iters = B.CreateAdd(
        iters, llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 1));
    auto *keep_looping = B.CreateICmpULT(
        next_iters, llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 4));

    acc->addIncoming(next_acc, loop);
    iters->addIncoming(next_iters, loop);
    B.CreateCondBr(keep_looping, loop, exit);
  }

  {
    llvm::IRBuilder<> B(exit);
    B.CreateRet(entry_fn->getArg(2));
  }

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  auto *merged = M->getFunction("sub_8000");
  ASSERT_NE(merged, nullptr);
  EXPECT_TRUE(merged->hasFnAttribute("omill.output_root"));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

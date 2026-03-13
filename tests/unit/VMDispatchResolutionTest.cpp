#include "omill/Passes/VMDispatchResolution.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/VMTraceMap.h"

#include <gtest/gtest.h>

#include <memory>
#include <vector>

namespace {

class VMDispatchResolutionTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    return std::make_unique<llvm::Module>("test", Ctx);
  }

  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  llvm::Function *declareDispatchJump(llvm::Module &M) {
    auto *existing = M.getFunction("__omill_dispatch_jump");
    if (existing)
      return existing;
    return llvm::Function::Create(liftedFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  "__omill_dispatch_jump", M);
  }

  llvm::Function *declareDispatchCall(llvm::Module &M) {
    auto *existing = M.getFunction("__omill_dispatch_call");
    if (existing)
      return existing;
    return llvm::Function::Create(liftedFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  "__omill_dispatch_call", M);
  }

  llvm::Function *declareOpaqueBase(llvm::Module &M) {
    auto *existing = M.getFunction("opaque_base");
    if (existing)
      return existing;
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(i64_ty, {}, false);
    return llvm::Function::Create(ft, llvm::GlobalValue::ExternalLinkage,
                                  "opaque_base", M);
  }

  llvm::Function *createHandler(llvm::Module &M, llvm::StringRef name) {
    auto *F = llvm::Function::Create(liftedFnType(),
                                     llvm::GlobalValue::ExternalLinkage, name,
                                     M);
    F->addFnAttr("omill.vm_handler");
    return F;
  }

  llvm::CallInst *findDispatchJump(llvm::Function &F) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (callee && callee->getName() == "__omill_dispatch_jump")
          return call;
      }
    }
    return nullptr;
  }

  llvm::Function *extractDispatchTargetFunction(llvm::Value *V) {
    if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntInst>(V))
      return llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
    auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(V);
    if (!ptoi)
      return nullptr;
    return llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
  }

  llvm::CallInst *findDirectCall(llvm::Function &F, llvm::StringRef callee_name) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (callee && callee->getName() == callee_name)
          return call;
      }
    }
    return nullptr;
  }

  void runPass(llvm::Module &M, omill::VMTraceMap trace_map = {}) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass(
        [&] { return omill::VMTraceMapAnalysis(std::move(trace_map)); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    (void)MAM.getResult<omill::VMTraceMapAnalysis>(M);

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::VMDispatchResolutionPass());
    MPM.run(M, MAM);
  }
};

TEST_F(VMDispatchResolutionTest, ResolvesDispatchJumpFromTraceMap) {
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_100001000");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x2500));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  trace_map.recordTraceTargets(0x100001000ULL, {0x100002500ULL});
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100002500ULL);

  auto *md = M->getNamedMetadata("omill.vm_discovered_targets");
  ASSERT_NE(md, nullptr);
  ASSERT_EQ(md->getNumOperands(), 1u);
}

TEST_F(VMDispatchResolutionTest, LeavesJumpOpaqueWithoutSingleTraceTarget) {
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_100001080");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1300));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  trace_map.recordTraceTargets(0x100001080ULL,
                               {0x100001200ULL, 0x100001300ULL});
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  EXPECT_FALSE(llvm::isa<llvm::ConstantInt>(jump->getArgOperand(1)));
  EXPECT_EQ(M->getNamedMetadata("omill.vm_discovered_targets"), nullptr);
}

TEST_F(VMDispatchResolutionTest, IgnoresDispatchCallsEvenWithTraceTarget) {
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_100001100");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch_call = declareDispatchCall(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1800));
  auto *call = B.CreateCall(dispatch_call,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  trace_map.recordTraceTargets(0x100001100ULL, {0x100001800ULL});
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  EXPECT_FALSE(llvm::isa<llvm::ConstantInt>(call->getArgOperand(1)));
  EXPECT_EQ(M->getNamedMetadata("omill.vm_discovered_targets"), nullptr);
}
TEST_F(VMDispatchResolutionTest, PrefersExactTraceRecordWhenHashAttributeIsPresent) {
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_100001180");
  handler->addFnAttr("omill.vm_trace_in_hash", "abcdef");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1900));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord first;
  first.handler_va = 0x100001180ULL;
  first.incoming_hash = 0xABCDEFULL;
  first.outgoing_hash = 0x1111ULL;
  first.successors = {0x100002900ULL};

  omill::VMTraceRecord second;
  second.handler_va = 0x100001180ULL;
  second.incoming_hash = 0x123456ULL;
  second.outgoing_hash = 0x2222ULL;
  second.successors = {0x100003900ULL};

  trace_map.recordTrace(std::move(first));
  trace_map.recordTrace(std::move(second));
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100002900ULL);

  auto *md = M->getNamedMetadata("omill.vm_discovered_targets");
  ASSERT_NE(md, nullptr);
  ASSERT_EQ(md->getNumOperands(), 1u);
}




TEST_F(VMDispatchResolutionTest, RoutesExactTraceToDemergedCloneWhenPresent) {
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_1000011a0");
  handler->addFnAttr("omill.vm_trace_in_hash", "abcdef");
  auto *clone = createHandler(*M, "sub_100002900__vm_1111");
  clone->addFnAttr("omill.vm_demerged_clone", "1");
  clone->addFnAttr("omill.vm_trace_in_hash", "1111");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x2900));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord exact;
  exact.handler_va = 0x1000011A0ULL;
  exact.incoming_hash = 0xABCDEFULL;
  exact.outgoing_hash = 0x1111ULL;
  exact.successors = {0x100002900ULL};
  trace_map.recordTrace(std::move(exact));
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(jump->getArgOperand(1));
  ASSERT_NE(ptoi, nullptr);
  auto *resolved = llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getName(), "sub_100002900__vm_1111");
  EXPECT_EQ(M->getNamedMetadata("omill.vm_discovered_targets"), nullptr);
}


TEST_F(VMDispatchResolutionTest, CloneNamedSourceUsesBaseHandlerVaForExactTrace) {
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_1000011c0__vm_abcdef");
  handler->addFnAttr("omill.vm_trace_in_hash", "abcdef");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1a00));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord exact;
  exact.handler_va = 0x1000011C0ULL;
  exact.incoming_hash = 0xABCDEFULL;
  exact.outgoing_hash = 0x2222ULL;
  exact.successors = {0x100003A00ULL};
  trace_map.recordTrace(std::move(exact));
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100003A00ULL);
}

TEST_F(VMDispatchResolutionTest, EliminatesDispatchJumpForVmexitHandler) {
  auto M = createModule();

  // Handler marked as vmexit — no successors in trace.
  auto *handler = createHandler(*M, "sub_100001200");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1200));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  // Simulate continuation code after the vmexit dispatch_jump.
  auto *ret_val = B.CreateIntToPtr(handler->getArg(1),
                                   llvm::PointerType::get(Ctx, 0));
  B.CreateRet(ret_val);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord rec;
  rec.handler_va = 0x100001200ULL;
  rec.incoming_hash = 0xAAAAULL;
  rec.is_vmexit = true;
  // No successors — vmexit terminates the VM.
  trace_map.recordTrace(std::move(rec));
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The dispatch_jump should have been erased.
  bool found_dispatch = false;
  for (auto &BB : *handler) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_dispatch_jump")
          found_dispatch = true;
      }
    }
  }
  EXPECT_FALSE(found_dispatch) << "vmexit dispatch_jump should be erased";

  // No discovered targets for vmexit handler.
  EXPECT_EQ(M->getNamedMetadata("omill.vm_discovered_targets"), nullptr);
}

TEST_F(VMDispatchResolutionTest,
       VmexitEliminationOnlyFiresWhenTraceRecordIsVmexit) {
  auto M = createModule();

  // Handler with empty trace targets but NOT marked as vmexit.
  auto *handler = createHandler(*M, "sub_100001280");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1280));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Record trace with is_vmexit=false and no successors.
  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord rec;
  rec.handler_va = 0x100001280ULL;
  rec.incoming_hash = 0xBBBBULL;
  rec.is_vmexit = false;
  trace_map.recordTrace(std::move(rec));
  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Should NOT be erased — not a vmexit, so dispatch_jump stays opaque.
  EXPECT_FALSE(llvm::isa<llvm::ConstantInt>(jump->getArgOperand(1)));
}

TEST_F(VMDispatchResolutionTest,
       VmexitEliminationUsesExactHashWhenPresent) {
  auto M = createModule();

  // Handler with exact hash attribute — only the matching record's is_vmexit
  // should control elimination.
  auto *handler = createHandler(*M, "sub_100001300");
  handler->addFnAttr("omill.vm_trace_in_hash", "deadbeef");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1300));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  auto *ret_val = B.CreateIntToPtr(handler->getArg(1),
                                   llvm::PointerType::get(Ctx, 0));
  B.CreateRet(ret_val);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);

  // Two records for same handler: one is vmexit (matching hash), one is not.
  omill::VMTraceRecord vmexit_rec;
  vmexit_rec.handler_va = 0x100001300ULL;
  vmexit_rec.incoming_hash = 0xDEADBEEFULL;
  vmexit_rec.is_vmexit = true;
  trace_map.recordTrace(std::move(vmexit_rec));

  omill::VMTraceRecord normal_rec;
  normal_rec.handler_va = 0x100001300ULL;
  normal_rec.incoming_hash = 0x11111111ULL;
  normal_rec.is_vmexit = false;
  normal_rec.successors = {0x100005000ULL};
  trace_map.recordTrace(std::move(normal_rec));

  runPass(*M, std::move(trace_map));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The exact hash matches the vmexit record, so dispatch_jump is erased.
  bool found_dispatch = false;
  for (auto &BB : *handler) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_dispatch_jump")
          found_dispatch = true;
      }
    }
  }
  EXPECT_FALSE(found_dispatch) << "exact-hash vmexit dispatch_jump should be erased";
}

TEST_F(VMDispatchResolutionTest, ThunkFallbackUsesFirstHandlerEntry) {
  // When a handler VA is not in the trace map and is not recognized as a VM
  // handler by the map, the pass falls back to handlerEntries().front().
  auto M = createModule();

  // Create a handler that looks like a thunk-resolved vmenter wrapper
  auto *handler = createHandler(*M, "sub_100003000");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x1234));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Build a trace map where 0x100003000 is NOT registered as a VM handler.
  // But there IS a known handler entry (0x100005000).
  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord entry_rec;
  entry_rec.handler_va = 0x100005000ULL;
  entry_rec.incoming_hash = 0xABCDULL;
  entry_rec.successors = {0x100006000ULL};
  trace_map.recordTrace(std::move(entry_rec));

  runPass(*M, std::move(trace_map));
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The dispatch_jump should be resolved to the first handler entry.
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100005000ULL);
}

TEST_F(VMDispatchResolutionTest, GraphDerivedRecordResolvesSingleSuccessor) {
  // Records imported from the dispatch graph have a single successor.
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_100010000");
  handler->addFnAttr("omill.vm_trace_in_hash", "AABB1122CCDD3344");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x5555));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord rec;
  rec.handler_va = 0x100010000ULL;
  rec.incoming_hash = 0xAABB1122CCDD3344ULL;
  rec.outgoing_hash = 0x9999888877776666ULL;
  rec.successors = {0x100020000ULL};
  trace_map.recordTrace(std::move(rec));

  runPass(*M, std::move(trace_map));
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100020000ULL);
}

TEST_F(VMDispatchResolutionTest, NativeCallRecordWithNoSuccessorIsSkipped) {
  // When a handler's trace record has native_target_va but no successors,
  // the dispatch_jump should be left unresolved (skipped).
  auto M = createModule();

  auto *handler = createHandler(*M, "sub_100040000");
  handler->addFnAttr("omill.vm_trace_in_hash", "DEAD0000BEEF0000");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);
  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *target = B.CreateAdd(opaque_base, B.getInt64(0x7777));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord rec;
  rec.handler_va = 0x100040000ULL;
  rec.incoming_hash = 0xDEAD0000BEEF0000ULL;
  rec.native_target_va = 0x100050000ULL;
  // No successors — native call with no resolved continuation
  trace_map.recordTrace(std::move(rec));

  runPass(*M, std::move(trace_map));
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The dispatch_jump arg should NOT be a ConstantInt (left unresolved).
  EXPECT_FALSE(llvm::isa<llvm::ConstantInt>(jump->getArgOperand(1)));
}

TEST_F(VMDispatchResolutionTest,
       NewlyCreatedDemergedCloneIsResolvedInSamePass) {
  auto M = createModule();

  auto *root = createHandler(*M, "sub_100060000");
  root->addFnAttr("omill.vm_trace_in_hash", "aaaa");
  auto *root_entry = llvm::BasicBlock::Create(Ctx, "entry", root);
  llvm::IRBuilder<> root_builder(root_entry);
  auto *dispatch = declareDispatchJump(*M);
  auto *root_base = root_builder.CreateCall(declareOpaqueBase(*M));
  auto *root_target = root_builder.CreateAdd(root_base, root_builder.getInt64(0x6000));
  auto *root_jump = root_builder.CreateCall(
      dispatch, {root->getArg(0), root_target, root->getArg(2)});
  root_builder.CreateRet(root_jump);

  auto *succ = createHandler(*M, "sub_100061000");
  auto *succ_entry = llvm::BasicBlock::Create(Ctx, "entry", succ);
  llvm::IRBuilder<> succ_builder(succ_entry);
  auto *succ_base = succ_builder.CreateCall(declareOpaqueBase(*M));
  auto *succ_target = succ_builder.CreateAdd(succ_base, succ_builder.getInt64(0x6100));
  auto *succ_jump = succ_builder.CreateCall(
      dispatch, {succ->getArg(0), succ_target, succ->getArg(2)});
  succ_builder.CreateRet(succ_jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord root_rec;
  root_rec.handler_va = 0x100060000ULL;
  root_rec.incoming_hash = 0xAAAAULL;
  root_rec.outgoing_hash = 0xBBBBULL;
  root_rec.successors = {0x100061000ULL};
  trace_map.recordTrace(std::move(root_rec));

  omill::VMTraceRecord succ_rec;
  succ_rec.handler_va = 0x100061000ULL;
  succ_rec.incoming_hash = 0xBBBBULL;
  succ_rec.outgoing_hash = 0xCCCCULL;
  succ_rec.successors = {0x100062000ULL};
  trace_map.recordTrace(std::move(succ_rec));

  runPass(*M, std::move(trace_map));
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *root_target_fn = extractDispatchTargetFunction(root_jump->getArgOperand(1));
  ASSERT_NE(root_target_fn, nullptr);
  EXPECT_EQ(root_target_fn->getName(), "sub_100061000__vm_bbbb");

  auto *clone = M->getFunction("sub_100061000__vm_bbbb");
  ASSERT_NE(clone, nullptr);
  auto *clone_jump = findDispatchJump(*clone);
  ASSERT_NE(clone_jump, nullptr);
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(clone_jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100062000ULL);

  auto *md = M->getNamedMetadata("omill.vm_discovered_targets");
  ASSERT_NE(md, nullptr);
  ASSERT_EQ(md->getNumOperands(), 1u);
}

TEST_F(VMDispatchResolutionTest,
       SpecializedWrapperCloneIsResolvedInSamePass) {
  auto M = createModule();

  auto *root = createHandler(*M, "sub_100070000");
  auto *root_entry = llvm::BasicBlock::Create(Ctx, "entry", root);
  llvm::IRBuilder<> root_builder(root_entry);
  auto *dispatch = declareDispatchJump(*M);
  auto *root_base = root_builder.CreateCall(declareOpaqueBase(*M));
  auto *root_target = root_builder.CreateAdd(root_base, root_builder.getInt64(0x7000));
  auto *root_jump = root_builder.CreateCall(
      dispatch, {root->getArg(0), root_target, root->getArg(2)});
  root_builder.CreateRet(root_jump);

  auto *wrapper = createHandler(*M, "sub_100080000");
  wrapper->addFnAttr("omill.vm_wrapper");
  auto *wrapper_entry = llvm::BasicBlock::Create(Ctx, "entry", wrapper);
  llvm::IRBuilder<> wrapper_builder(wrapper_entry);
  auto *wrapper_base = wrapper_builder.CreateCall(declareOpaqueBase(*M));
  auto *wrapper_target =
      wrapper_builder.CreateAdd(wrapper_base, wrapper_builder.getInt64(0x8000));
  auto *wrapper_jump = wrapper_builder.CreateCall(
      dispatch, {wrapper->getArg(0), wrapper_target, wrapper->getArg(2)});
  wrapper_builder.CreateRet(wrapper_jump);

  auto *succ = createHandler(*M, "sub_100071000");
  auto *succ_entry = llvm::BasicBlock::Create(Ctx, "entry", succ);
  llvm::IRBuilder<> succ_builder(succ_entry);
  auto *succ_base = succ_builder.CreateCall(declareOpaqueBase(*M));
  auto *succ_target = succ_builder.CreateAdd(succ_base, succ_builder.getInt64(0x7100));
  auto *succ_jump = succ_builder.CreateCall(
      dispatch, {succ->getArg(0), succ_target, succ->getArg(2)});
  succ_builder.CreateRet(succ_jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  omill::VMTraceMap trace_map(0, 0);
  omill::VMTraceRecord root_rec;
  root_rec.handler_va = 0x100070000ULL;
  root_rec.incoming_hash = 0xAAAAULL;
  root_rec.outgoing_hash = 0xBBBBULL;
  root_rec.native_target_va = 0x100080000ULL;
  root_rec.successors = {0x100071000ULL};
  trace_map.recordTrace(std::move(root_rec));

  omill::VMTraceRecord succ_rec;
  succ_rec.handler_va = 0x100071000ULL;
  succ_rec.incoming_hash = 0xBBBBULL;
  succ_rec.outgoing_hash = 0xCCCCULL;
  succ_rec.successors = {0x100072000ULL};
  trace_map.recordTrace(std::move(succ_rec));

  runPass(*M, std::move(trace_map));
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *specialized = M->getFunction("sub_100080000__vmwrap_100071000_bbbb");
  ASSERT_NE(specialized, nullptr);
  auto *root_call =
      findDirectCall(*root, "sub_100080000__vmwrap_100071000_bbbb");
  ASSERT_NE(root_call, nullptr);

  auto *specialized_jump = findDispatchJump(*specialized);
  ASSERT_NE(specialized_jump, nullptr);
  auto *specialized_target = specialized_jump->getArgOperand(1);
  EXPECT_TRUE(llvm::isa<llvm::ConstantInt>(specialized_target) ||
              extractDispatchTargetFunction(specialized_target) != nullptr);

  auto *succ_clone = M->getFunction("sub_100071000__vm_bbbb");
  ASSERT_NE(succ_clone, nullptr);
  auto *succ_clone_jump = findDispatchJump(*succ_clone);
  ASSERT_NE(succ_clone_jump, nullptr);
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(succ_clone_jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100072000ULL);
}

}  // namespace

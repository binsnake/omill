#include "omill/Analysis/CallGraphAnalysis.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>

namespace {

class CallGraphAnalysisTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::FunctionType *liftedFnTy() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  std::unique_ptr<llvm::Module> createEmptyModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");
    return M;
  }

  llvm::Function *addLiftedFn(llvm::Module &M, const char *name) {
    auto *fn = llvm::Function::Create(
        liftedFnTy(), llvm::Function::ExternalLinkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(fn->getArg(2));
    return fn;
  }

  llvm::Function *getOrCreateDispatch(llvm::Module &M, const char *name) {
    if (auto *F = M.getFunction(name)) return F;
    return llvm::Function::Create(
        liftedFnTy(), llvm::Function::ExternalLinkage, name, M);
  }

  omill::LiftedCallGraph runAnalysis(llvm::Module &M) {
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
    MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
    MAM.registerPass([&] { return omill::CallGraphAnalysis(); });

    return MAM.getResult<omill::CallGraphAnalysis>(M);
  }
};

TEST_F(CallGraphAnalysisTest, EmptyModule) {
  auto M = createEmptyModule();
  auto graph = runAnalysis(*M);

  EXPECT_EQ(graph.size(), 0u);
  EXPECT_EQ(graph.totalUnresolved(), 0u);
  EXPECT_TRUE(graph.getBottomUpSCCs().empty());
}

TEST_F(CallGraphAnalysisTest, DirectCallBetweenFunctions) {
  auto M = createEmptyModule();
  auto *callee = addLiftedFn(*M, "sub_402000");
  auto *caller_fn = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(entry);
  auto *result = B.CreateCall(callee,
      {caller_fn->getArg(0), caller_fn->getArg(1), caller_fn->getArg(2)});
  B.CreateRet(result);

  auto graph = runAnalysis(*M);

  EXPECT_EQ(graph.size(), 2u);

  auto *caller_node = graph.getNode(caller_fn);
  ASSERT_NE(caller_node, nullptr);
  EXPECT_EQ(caller_node->callees.size(), 1u);
  EXPECT_EQ(caller_node->callees[0].callee, callee);
  EXPECT_FALSE(caller_node->callees[0].is_dispatch);
  EXPECT_FALSE(caller_node->callees[0].is_tail_call);

  auto *callee_node = graph.getNode(callee);
  ASSERT_NE(callee_node, nullptr);
  EXPECT_EQ(callee_node->callers.size(), 1u);
  EXPECT_EQ(callee_node->callers[0]->caller, caller_fn);
}

TEST_F(CallGraphAnalysisTest, DispatchCallWithConstantTarget) {
  auto M = createEmptyModule();
  auto *callee = addLiftedFn(*M, "sub_402000");
  auto *dispatch = getOrCreateDispatch(*M, "__omill_dispatch_call");

  auto *caller_fn = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(entry);

  auto *target_pc = B.getInt64(0x402000);
  auto *result = B.CreateCall(dispatch,
      {caller_fn->getArg(0), target_pc, caller_fn->getArg(2)});
  B.CreateRet(result);

  auto graph = runAnalysis(*M);

  auto *caller_node = graph.getNode(caller_fn);
  ASSERT_NE(caller_node, nullptr);
  ASSERT_EQ(caller_node->callees.size(), 1u);
  EXPECT_EQ(caller_node->callees[0].callee, callee);
  EXPECT_EQ(caller_node->callees[0].target_pc, 0x402000u);
  EXPECT_TRUE(caller_node->callees[0].is_dispatch);
  EXPECT_EQ(caller_node->unresolved_count, 0u);
}

TEST_F(CallGraphAnalysisTest, DispatchCallDynamicTarget) {
  auto M = createEmptyModule();
  auto *dispatch = getOrCreateDispatch(*M, "__omill_dispatch_call");

  auto *caller_fn = addLiftedFn(*M, "sub_401000");
  // Replace the return with a dispatch call using a non-constant target.
  caller_fn->getEntryBlock().getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&caller_fn->getEntryBlock());
  // Load a dynamic value from State as target.
  auto *dynamic_target = B.CreateLoad(B.getInt64Ty(), caller_fn->getArg(0));
  auto *result = B.CreateCall(dispatch,
      {caller_fn->getArg(0), dynamic_target, caller_fn->getArg(2)});
  B.CreateRet(result);

  auto graph = runAnalysis(*M);

  auto *node = graph.getNode(caller_fn);
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->callees.size(), 1u);
  EXPECT_EQ(node->callees[0].callee, nullptr);
  EXPECT_EQ(node->callees[0].target_pc, 0u);
  EXPECT_EQ(node->unresolved_count, 1u);
  EXPECT_EQ(graph.totalUnresolved(), 1u);
}

TEST_F(CallGraphAnalysisTest, MustTailCall) {
  auto M = createEmptyModule();
  auto *callee = addLiftedFn(*M, "sub_402000");

  auto *caller_fn = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(entry);
  auto *call = B.CreateCall(callee,
      {caller_fn->getArg(0), caller_fn->getArg(1), caller_fn->getArg(2)});
  call->setTailCallKind(llvm::CallInst::TCK_MustTail);
  B.CreateRet(call);

  auto graph = runAnalysis(*M);

  auto *node = graph.getNode(caller_fn);
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->callees.size(), 1u);
  EXPECT_TRUE(node->callees[0].is_tail_call);
}

TEST_F(CallGraphAnalysisTest, MutualRecursionSingleSCC) {
  auto M = createEmptyModule();

  // Create two functions that call each other.
  auto *fn_a = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *fn_b = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_402000", *M);

  // fn_a calls fn_b
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_a);
    llvm::IRBuilder<> B(entry);
    auto *result = B.CreateCall(fn_b,
        {fn_a->getArg(0), fn_a->getArg(1), fn_a->getArg(2)});
    B.CreateRet(result);
  }

  // fn_b calls fn_a
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn_b);
    llvm::IRBuilder<> B(entry);
    auto *result = B.CreateCall(fn_a,
        {fn_b->getArg(0), fn_b->getArg(1), fn_b->getArg(2)});
    B.CreateRet(result);
  }

  auto graph = runAnalysis(*M);

  // Should have SCCs; the mutual recursion pair should be in one SCC.
  bool found_mutual_scc = false;
  for (auto &scc : graph.getBottomUpSCCs()) {
    if (scc.size() == 2) {
      bool has_a = false, has_b = false;
      for (auto *F : scc) {
        if (F == fn_a) has_a = true;
        if (F == fn_b) has_b = true;
      }
      if (has_a && has_b) found_mutual_scc = true;
    }
  }
  EXPECT_TRUE(found_mutual_scc);
}

TEST_F(CallGraphAnalysisTest, BottomUpOrderLeavesFirst) {
  auto M = createEmptyModule();

  // leaf (no callees)
  auto *leaf = addLiftedFn(*M, "sub_403000");

  // mid calls leaf
  auto *mid = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *r = B.CreateCall(leaf,
        {mid->getArg(0), mid->getArg(1), mid->getArg(2)});
    B.CreateRet(r);
  }

  // root calls mid
  auto *root = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *r = B.CreateCall(mid,
        {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(r);
  }

  auto graph = runAnalysis(*M);

  auto &sccs = graph.getBottomUpSCCs();
  ASSERT_EQ(sccs.size(), 3u);

  // Find positions.
  int leaf_pos = -1, mid_pos = -1, root_pos = -1;
  for (int i = 0; i < (int)sccs.size(); i++) {
    ASSERT_EQ(sccs[i].size(), 1u);
    if (sccs[i][0] == leaf) leaf_pos = i;
    if (sccs[i][0] == mid) mid_pos = i;
    if (sccs[i][0] == root) root_pos = i;
  }

  EXPECT_NE(leaf_pos, -1);
  EXPECT_NE(mid_pos, -1);
  EXPECT_NE(root_pos, -1);
  // Leaf should come before mid, mid before root (bottom-up).
  EXPECT_LT(leaf_pos, mid_pos);
  EXPECT_LT(mid_pos, root_pos);
}

}  // namespace

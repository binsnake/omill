#include "omill/Analysis/IterativeLiftingSession.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class IterativeLiftingSessionTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
};

TEST_F(IterativeLiftingSessionTest, QueueAndLiftStateShareSingleNode) {
  omill::IterativeLiftingSession session("test-session");

  session.queueTarget(0x140001000);
  ASSERT_TRUE(session.hasPendingTargets());

  auto next = session.popPendingTarget();
  ASSERT_TRUE(next.has_value());
  EXPECT_EQ(*next, 0x140001000ULL);

  EXPECT_TRUE(session.noteLiftedTarget(*next));
  EXPECT_FALSE(session.noteLiftedTarget(*next));

  auto *node = session.graph().lookupNode(*next);
  ASSERT_NE(node, nullptr);
  EXPECT_TRUE(node->lifted);
  EXPECT_TRUE(session.graph().isDirty(*next));
}

TEST_F(IterativeLiftingSessionTest, EdgeUpdatesAreDeduplicatedByShape) {
  omill::LiftGraph graph;

  omill::LiftEdge edge;
  edge.kind = omill::LiftEdgeKind::kIndirectCall;
  edge.source_pc = 0x1000;
  edge.target_pc = 0x2000;

  auto &first = graph.addOrUpdateEdge(edge);
  EXPECT_FALSE(first.resolved);
  EXPECT_EQ(graph.edgeCount(), 1u);

  edge.resolved = true;
  auto &second = graph.addOrUpdateEdge(edge);
  EXPECT_EQ(&first, &second);
  EXPECT_TRUE(second.resolved);
  EXPECT_EQ(graph.edgeCount(), 1u);
}

TEST_F(IterativeLiftingSessionTest, AnalysisReturnsInjectedSession) {
  auto module = std::make_unique<llvm::Module>("test", Ctx);
  auto shared =
      std::make_shared<omill::IterativeLiftingSession>("shared-session");

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

  MAM.registerPass([shared] {
    return omill::IterativeLiftingSessionAnalysis(shared);
  });

  auto &result =
      MAM.getResult<omill::IterativeLiftingSessionAnalysis>(*module);
  ASSERT_TRUE(result.session);
  EXPECT_EQ(result.session, shared);
  EXPECT_EQ(result.session->name(), "shared-session");
}

}  // namespace

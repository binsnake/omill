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

TEST_F(IterativeLiftingSessionTest, SyncOutgoingEdgesReplacesStaleEntries) {
  omill::LiftGraph graph;

  graph.addOrUpdateEdge({omill::LiftEdgeKind::kIndirectCall, 0x1000, 0x2000,
                         false, false});
  ASSERT_EQ(graph.unresolvedEdgeCount(), 1u);

  omill::LiftEdge direct;
  direct.kind = omill::LiftEdgeKind::kDirectCall;
  direct.source_pc = 0x1000;
  direct.target_pc = 0x2000;
  direct.resolved = true;
  graph.syncOutgoingEdges(0x1000, {direct});

  EXPECT_EQ(graph.edgeCount(), 1u);
  EXPECT_EQ(graph.unresolvedEdgeCount(), 0u);
  auto outgoing = graph.outgoingEdges(0x1000);
  ASSERT_EQ(outgoing.size(), 1u);
  EXPECT_EQ(outgoing.front()->kind, omill::LiftEdgeKind::kDirectCall);
  EXPECT_TRUE(outgoing.front()->resolved);
}

TEST_F(IterativeLiftingSessionTest, RoundSummariesAreRecordedInOrder) {
  omill::IterativeLiftingSession session("summary-session");

  omill::IterativeRoundSummary first;
  first.pipeline = "trace";
  first.iteration = 0;
  first.unresolved_before = 3;
  first.unresolved_after = 1;
  first.total_ms = 17;
  first.resolve_ms = 9;
  session.recordRoundSummary(first);

  omill::IterativeRoundSummary second;
  second.pipeline = "trace";
  second.iteration = 1;
  second.unresolved_before = 1;
  second.unresolved_after = 0;
  session.recordRoundSummary(second);

  auto rounds = session.roundSummaries();
  ASSERT_EQ(rounds.size(), 2u);
  EXPECT_EQ(rounds[0].iteration, 0u);
  EXPECT_EQ(rounds[0].unresolved_after, 1u);
  EXPECT_EQ(rounds[0].total_ms, 17u);
  EXPECT_EQ(rounds[0].resolve_ms, 9u);
  EXPECT_EQ(rounds[1].iteration, 1u);
  EXPECT_EQ(rounds[1].unresolved_after, 0u);
}

TEST_F(IterativeLiftingSessionTest, PendingTargetCountTracksQueueDepth) {
  omill::IterativeLiftingSession session("pending-targets");

  EXPECT_EQ(session.pendingTargetCount(), 0u);

  session.queueTarget(0x140001000);
  session.queueTarget(0x140001100);
  session.queueTarget(0x140001000);  // duplicate

  EXPECT_EQ(session.pendingTargetCount(), 2u);

  ASSERT_TRUE(session.popPendingTarget().has_value());
  EXPECT_EQ(session.pendingTargetCount(), 1u);
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

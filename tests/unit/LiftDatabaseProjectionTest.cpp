#include <gtest/gtest.h>

#include "omill/BC/LiftDatabase.h"
#include "omill/BC/LiftDatabaseProjection.h"

namespace omill {
namespace {

TEST(LiftDatabaseProjectionTest, ProjectsFunctionBlocksInReachableOrder) {
  LiftDatabase db;
  auto &function = db.upsertFunction(0x401000);
  auto &entry = db.upsertBlock(0x401000, 0x401000);
  auto &mid = db.upsertBlock(0x401000, 0x401010);
  auto &tail = db.upsertBlock(0x401000, 0x401020);

  function.block_entries = {0x401000, 0x401010, 0x401020};
  entry.successors.push_back(
      {LiftDbEdgeKind::kFallthrough, 0x401000, 0x401010, false});
  mid.successors.push_back(
      {LiftDbEdgeKind::kBranchTaken, 0x401010, 0x401020, false});

  LiftDatabaseProjector projector(db);
  auto projection = projector.projectFunction(0x401000);
  ASSERT_TRUE(projection.has_value());
  ASSERT_EQ(projection->block_order.size(), 3u);
  EXPECT_EQ(projection->block_order[0], 0x401000u);
  EXPECT_EQ(projection->block_order[1], 0x401010u);
  EXPECT_EQ(projection->block_order[2], 0x401020u);
  EXPECT_EQ(projection->blocks.at(0x401010).predecessors.size(), 1u);
  EXPECT_EQ(projection->blocks.at(0x401010).predecessors.front(), 0x401000u);
}

TEST(LiftDatabaseProjectionTest, FindsContainingBlockForInteriorInstruction) {
  LiftDatabase db;
  auto &function = db.upsertFunction(0x401000);
  auto &entry = db.upsertBlock(0x401000, 0x401000);
  auto &tail = db.upsertBlock(0x401000, 0x401020);

  function.block_entries = {0x401000, 0x401020};
  entry.instruction_vas = {0x401000, 0x401005, 0x40100A};
  tail.instruction_vas = {0x401020};
  entry.successors.push_back(
      {LiftDbEdgeKind::kFallthrough, 0x401000, 0x401020, false});

  LiftDatabaseProjector projector(db);
  auto projection = projector.projectFunction(0x401000);
  ASSERT_TRUE(projection.has_value());

  auto *block = FindProjectionBlockContaining(*projection, 0x40100A);
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(block->entry_va, 0x401000u);
}


TEST(LiftDatabaseProjectionTest, ProjectsOverlayUsingConstrainedEdges) {
  LiftDatabase db;
  db.upsertFunction(0x500000).block_entries = {0x500000, 0x500100, 0x500200};

  auto &entry = db.upsertBlock(0x500000, 0x500000);
  auto &a = db.upsertBlock(0x500000, 0x500100);
  auto &b = db.upsertBlock(0x500000, 0x500200);

  entry.successors.push_back(
      {LiftDbEdgeKind::kFallthrough, 0x500000, 0x500100, false});
  entry.successors.push_back(
      {LiftDbEdgeKind::kBranchTaken, 0x500000, 0x500200, false});
  a.successors.push_back(
      {LiftDbEdgeKind::kFallthrough, 0x500100, 0x500200, false});

  auto &overlay = db.upsertTraceOverlay(LiftDbOverlayKey(0x500000, 0x1337));
  overlay.overlay_key = LiftDbOverlayKey(0x500000, 0x1337);
  overlay.handler_va = 0x500000;
  overlay.incoming_hash = 0x1337;
  overlay.function_entry_va = 0x500000;
  overlay.path_block_entries = {0x500000, 0x500200};
  overlay.constrained_edges.push_back(
      {LiftDbEdgeKind::kOverlay, 0x500000, 0x500200, true});

  LiftDatabaseProjector projector(db);
  auto projection = projector.projectOverlay(overlay.overlay_key);
  ASSERT_TRUE(projection.has_value());
  ASSERT_EQ(projection->block_order.size(), 2u);
  ASSERT_EQ(projection->blocks.at(0x500000).successors.size(), 1u);
  EXPECT_EQ(projection->blocks.at(0x500000).successors.front().target_block_va,
            0x500200u);
  EXPECT_EQ(projection->blocks.at(0x500200).predecessors.size(), 1u);
  EXPECT_EQ(projection->blocks.at(0x500200).predecessors.front(), 0x500000u);
  EXPECT_EQ(projection->blocks.count(0x500100), 0u);
  (void) b;
}

}  // namespace
}  // namespace omill

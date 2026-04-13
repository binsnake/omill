#include <filesystem>

#include <gtest/gtest.h>

#include "llvm/ADT/SmallString.h"
#include "llvm/Support/FileSystem.h"
#include "omill/BC/LiftDatabase.h"
#include "omill/BC/LiftDatabaseIO.h"

namespace omill {
namespace {

TEST(LiftDatabaseTest, UpsertRecordsAndPredecessors) {
  LiftDatabase db;
  db.manifest().arch = LiftDbArch::kX64;

  auto &function = db.upsertFunction(0x401000);
  auto &entry = db.upsertBlock(0x401000, 0x401000);
  auto &succ = db.upsertBlock(0x401000, 0x401010);

  entry.successors.push_back(
      {LiftDbEdgeKind::kFallthrough, 0x401000, 0x401010, false});

  auto &inst = db.upsertInstruction(0x401000);
  inst.function_entry_va = 0x401000;
  inst.block_entry_va = 0x401000;
  entry.instruction_vas.push_back(0x401000);

  db.rebuildPredecessors(0x401000);

  ASSERT_EQ(db.functions().size(), 1u);
  ASSERT_EQ(db.blocks().size(), 2u);
  ASSERT_EQ(db.instructions().size(), 1u);
  EXPECT_EQ(function.entry_va, 0x401000u);
  EXPECT_EQ(succ.predecessors.size(), 1u);
  EXPECT_EQ(succ.predecessors.front(), 0x401000u);
}

TEST(LiftDatabaseTest, RoundTripsDirectoryFormat) {
  LiftDatabase db;
  db.manifest().format_version = "1";
  db.manifest().image_path = "sample.exe";
  db.manifest().image_id = "sample.exe";
  db.manifest().arch = LiftDbArch::kX64;
  db.manifest().image_base = 0x400000;
  db.manifest().db_revision = 7;

  auto &function = db.upsertFunction(0x401000);
  auto &block = db.upsertBlock(0x401000, 0x401000);
  auto &inst = db.upsertInstruction(0x401000);
  inst.function_entry_va = 0x401000;
  inst.block_entry_va = 0x401000;
  inst.bytes_hex = "55488bec";
  inst.mnemonic = "push";
  inst.category = LiftDbCategory::kNormal;
  inst.size = 4;
  block.instruction_vas.push_back(0x401000);
  function.use_def_chains.push_back(
      {LiftDbLocation{LiftDbLocationKind::kRegister, "RSP", "", 0, 64, 1, true},
       0x401000,
       {}});

  auto &overlay = db.upsertTraceOverlay(LiftDbOverlayKey(0x500000, 0x1337));
  overlay.handler_va = 0x500000;
  overlay.incoming_hash = 0x1337;
  overlay.function_entry_va = 0x401000;
  overlay.path_block_entries.push_back(0x401000);

  llvm::SmallString<256> temp_dir;
  ASSERT_FALSE(llvm::sys::fs::createUniqueDirectory("liftdb-test", temp_dir));

  std::string error;
  ASSERT_TRUE(SaveLiftDatabaseToDirectory(db, temp_dir, &error)) << error;

  auto loaded = LoadLiftDatabaseFromDirectory(temp_dir, &error);
  ASSERT_TRUE(loaded.has_value()) << error;
  EXPECT_EQ(loaded->manifest().image_path, "sample.exe");
  EXPECT_EQ(loaded->manifest().db_revision, 7u);
  ASSERT_EQ(loaded->functions().size(), 1u);
  ASSERT_EQ(loaded->blocks().size(), 1u);
  ASSERT_EQ(loaded->instructions().size(), 1u);
  ASSERT_EQ(loaded->traceOverlays().size(), 1u);
  EXPECT_EQ(loaded->instruction(0x401000)->bytes_hex, "55488bec");

  std::filesystem::remove_all(temp_dir.str().str());
}

}  // namespace
}  // namespace omill

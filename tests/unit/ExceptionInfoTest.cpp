#include "omill/Analysis/ExceptionInfo.h"

#include "omill/Analysis/BinaryMemoryMap.h"

#include <cstdint>
#include <cstring>
#include <deque>
#include <vector>

#include <gtest/gtest.h>

namespace {

class ExceptionInfoTest : public ::testing::Test {
 protected:
  omill::ExceptionInfo info;
};

// ---------------------------------------------------------------------------
// Test 1: EmptyByDefault
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, EmptyByDefault) {
  EXPECT_TRUE(info.empty());
  EXPECT_EQ(info.lookup(0x1000), nullptr);
  EXPECT_EQ(info.lookup(0), nullptr);
}

// ---------------------------------------------------------------------------
// Test 2: AddEntryAndLookup
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, AddEntryAndLookup) {
  omill::RuntimeFunctionEntry entry{};
  entry.begin_va = 0x1000;
  entry.end_va = 0x1100;
  entry.handler_va = 0x2000;
  info.addEntry(entry);

  EXPECT_FALSE(info.empty());

  // Inside range.
  auto *found = info.lookup(0x1050);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->begin_va, 0x1000u);
  EXPECT_EQ(found->end_va, 0x1100u);

  // Outside range.
  EXPECT_EQ(info.lookup(0x1100), nullptr);
  EXPECT_EQ(info.lookup(0x2000), nullptr);
}

// ---------------------------------------------------------------------------
// Test 3: LookupBeginBoundary
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, LookupBeginBoundary) {
  omill::RuntimeFunctionEntry entry{};
  entry.begin_va = 0x5000;
  entry.end_va = 0x5100;
  info.addEntry(entry);

  auto *found = info.lookup(0x5000);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->begin_va, 0x5000u);
}

// ---------------------------------------------------------------------------
// Test 4: LookupEndBoundary — half-open range, end_va is exclusive
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, LookupEndBoundary) {
  omill::RuntimeFunctionEntry entry{};
  entry.begin_va = 0x3000;
  entry.end_va = 0x3080;
  info.addEntry(entry);

  // Last valid address.
  ASSERT_NE(info.lookup(0x307F), nullptr);
  // end_va itself is excluded.
  EXPECT_EQ(info.lookup(0x3080), nullptr);
}

// ---------------------------------------------------------------------------
// Test 5: LookupBelowRange
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, LookupBelowRange) {
  omill::RuntimeFunctionEntry entry{};
  entry.begin_va = 0x8000;
  entry.end_va = 0x9000;
  info.addEntry(entry);

  EXPECT_EQ(info.lookup(0x7FFF), nullptr);
  EXPECT_EQ(info.lookup(0x0), nullptr);
}

// ---------------------------------------------------------------------------
// Test 6: MultipleEntriesUnsorted — lazy sort on lookup
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, MultipleEntriesUnsorted) {
  // Insert entries deliberately out of order.
  omill::RuntimeFunctionEntry e3{};
  e3.begin_va = 0x6000;
  e3.end_va = 0x6100;
  info.addEntry(e3);

  omill::RuntimeFunctionEntry e1{};
  e1.begin_va = 0x2000;
  e1.end_va = 0x2100;
  info.addEntry(e1);

  omill::RuntimeFunctionEntry e2{};
  e2.begin_va = 0x4000;
  e2.end_va = 0x4100;
  info.addEntry(e2);

  // All three should be found.
  ASSERT_NE(info.lookup(0x2050), nullptr);
  EXPECT_EQ(info.lookup(0x2050)->begin_va, 0x2000u);

  ASSERT_NE(info.lookup(0x4050), nullptr);
  EXPECT_EQ(info.lookup(0x4050)->begin_va, 0x4000u);

  ASSERT_NE(info.lookup(0x6050), nullptr);
  EXPECT_EQ(info.lookup(0x6050)->begin_va, 0x6000u);

  // Gaps between entries.
  EXPECT_EQ(info.lookup(0x3000), nullptr);
  EXPECT_EQ(info.lookup(0x5000), nullptr);
}

// ---------------------------------------------------------------------------
// Test 7: GetHandlerVAsDedup
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, GetHandlerVAsDedup) {
  omill::RuntimeFunctionEntry e1{};
  e1.begin_va = 0x1000;
  e1.end_va = 0x1100;
  e1.handler_va = 0xA000;
  info.addEntry(e1);

  omill::RuntimeFunctionEntry e2{};
  e2.begin_va = 0x2000;
  e2.end_va = 0x2100;
  e2.handler_va = 0xB000;
  info.addEntry(e2);

  omill::RuntimeFunctionEntry e3{};
  e3.begin_va = 0x3000;
  e3.end_va = 0x3100;
  e3.handler_va = 0xA000;  // duplicate
  info.addEntry(e3);

  auto vas = info.getHandlerVAs();
  ASSERT_EQ(vas.size(), 2u);
  // Sorted.
  EXPECT_EQ(vas[0], 0xA000u);
  EXPECT_EQ(vas[1], 0xB000u);
}

// ---------------------------------------------------------------------------
// Test 8: GetHandlerVAsSkipsZero
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, GetHandlerVAsSkipsZero) {
  omill::RuntimeFunctionEntry e1{};
  e1.begin_va = 0x1000;
  e1.end_va = 0x1100;
  e1.handler_va = 0;  // no handler
  info.addEntry(e1);

  omill::RuntimeFunctionEntry e2{};
  e2.begin_va = 0x2000;
  e2.end_va = 0x2100;
  e2.handler_va = 0xC000;
  info.addEntry(e2);

  auto vas = info.getHandlerVAs();
  ASSERT_EQ(vas.size(), 1u);
  EXPECT_EQ(vas[0], 0xC000u);
}

// ---------------------------------------------------------------------------
// Test 9: ImageBase round-trip
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, ImageBase) {
  EXPECT_EQ(info.imageBase(), 0u);
  info.setImageBase(0x140000000ULL);
  EXPECT_EQ(info.imageBase(), 0x140000000ULL);
}

// ---------------------------------------------------------------------------
// Test 10: BuildSyntheticDCs
// ---------------------------------------------------------------------------

TEST_F(ExceptionInfoTest, BuildSyntheticDCs) {
  constexpr uint64_t kImageBase = 0x140000000ULL;
  constexpr uint64_t kSyntheticDCBase = 0x7FFE000000000000ULL;
  constexpr uint64_t kSyntheticCtxBase = 0x7FFD000000000000ULL;

  // Entry 0: has handler_data_va → gets synthetic DC.
  omill::RuntimeFunctionEntry e0{};
  e0.begin_va = 0x140001000;
  e0.end_va = 0x140001100;
  e0.handler_va = 0x140005000;
  e0.handler_data_va = 0x14000A000;
  info.addEntry(e0);

  // Entry 1: handler_data_va == 0 → skipped.
  omill::RuntimeFunctionEntry e1{};
  e1.begin_va = 0x140002000;
  e1.end_va = 0x140002100;
  e1.handler_va = 0x140005000;
  e1.handler_data_va = 0;
  info.addEntry(e1);

  // Entry 2: has handler_data_va → gets synthetic DC at idx=2.
  omill::RuntimeFunctionEntry e2{};
  e2.begin_va = 0x140003000;
  e2.end_va = 0x140003100;
  e2.handler_va = 0x140006000;
  e2.handler_data_va = 0x14000B000;
  info.addEntry(e2);

  std::deque<std::vector<uint8_t>> storage;
  omill::BinaryMemoryMap mem_map;

  info.buildSyntheticDCs(storage, mem_map, kImageBase);

  // Entry 0 → idx 0, DC at kSyntheticDCBase + 0*0x100.
  {
    uint64_t dc_va = kSyntheticDCBase;
    // Read handler_data_va at [dc_va + 0x38].
    auto hd = mem_map.readInt(dc_va + 0x38, 8);
    ASSERT_TRUE(hd.has_value());
    EXPECT_EQ(*hd, 0x14000A000ULL);

    // Read image_base at [dc_va + 0x08].
    auto ib = mem_map.readInt(dc_va + 0x08, 8);
    ASSERT_TRUE(ib.has_value());
    EXPECT_EQ(*ib, kImageBase);

    // Synthetic CONTEXT at kSyntheticCtxBase + 0*0x200.
    uint64_t ctx_va = kSyntheticCtxBase;
    auto rip = mem_map.readInt(ctx_va + 0xF8, 8);
    ASSERT_TRUE(rip.has_value());
    EXPECT_EQ(*rip, 0x140001000ULL);
  }

  // Entry 1 (idx 1) — skipped, no DC. Verify no region there.
  {
    uint64_t dc_va_skip = kSyntheticDCBase + 0x100;
    EXPECT_FALSE(mem_map.readInt(dc_va_skip + 0x38, 8).has_value());
  }

  // Entry 2 → idx 2, DC at kSyntheticDCBase + 2*0x100.
  {
    uint64_t dc_va = kSyntheticDCBase + 2 * 0x100;
    auto hd = mem_map.readInt(dc_va + 0x38, 8);
    ASSERT_TRUE(hd.has_value());
    EXPECT_EQ(*hd, 0x14000B000ULL);

    auto ib = mem_map.readInt(dc_va + 0x08, 8);
    ASSERT_TRUE(ib.has_value());
    EXPECT_EQ(*ib, kImageBase);

    uint64_t ctx_va = kSyntheticCtxBase + 2 * 0x200;
    auto rip = mem_map.readInt(ctx_va + 0xF8, 8);
    ASSERT_TRUE(rip.has_value());
    EXPECT_EQ(*rip, 0x140003000ULL);
  }
}

}  // namespace

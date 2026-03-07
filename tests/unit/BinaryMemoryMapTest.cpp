#include "omill/Analysis/BinaryMemoryMap.h"

#include <cstdint>
#include <cstring>
#include <memory>
#include <vector>

#include <gtest/gtest.h>

namespace {

class BinaryMemoryMapTest : public ::testing::Test {
 protected:
  omill::BinaryMemoryMap map;

  /// Allocate a buffer that outlives the map (stored in `bufs_`).
  const uint8_t *allocBuf(std::initializer_list<uint8_t> data) {
    auto buf = std::make_unique<uint8_t[]>(data.size());
    std::memcpy(buf.get(), data.begin(), data.size());
    auto *ptr = buf.get();
    bufs_.push_back(std::move(buf));
    return ptr;
  }

  /// Allocate a buffer of `size` bytes filled with a pattern.
  const uint8_t *allocBuf(size_t size, uint8_t fill = 0xCC) {
    auto buf = std::make_unique<uint8_t[]>(size);
    std::memset(buf.get(), fill, size);
    auto *ptr = buf.get();
    bufs_.push_back(std::move(buf));
    return ptr;
  }

 private:
  std::vector<std::unique_ptr<uint8_t[]>> bufs_;
};

// ===----------------------------------------------------------------------===
// Test 1: Add region and read bytes back
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, AddRegionAndRead) {
  auto *data = allocBuf({0x41, 0x42, 0x43, 0x44});
  map.addRegion(0x1000, data, 4, /*read_only=*/true);

  uint8_t out[4] = {};
  ASSERT_TRUE(map.read(0x1000, out, 4));
  EXPECT_EQ(out[0], 0x41);
  EXPECT_EQ(out[1], 0x42);
  EXPECT_EQ(out[2], 0x43);
  EXPECT_EQ(out[3], 0x44);

  // Partial read from middle of region.
  uint8_t mid[2] = {};
  ASSERT_TRUE(map.read(0x1001, mid, 2));
  EXPECT_EQ(mid[0], 0x42);
  EXPECT_EQ(mid[1], 0x43);
}

// ===----------------------------------------------------------------------===
// Test 2: Read spanning end of region fails
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ReadAcrossRegionBoundary) {
  auto *data = allocBuf({0x01, 0x02, 0x03, 0x04});
  map.addRegion(0x2000, data, 4, /*read_only=*/true);

  uint8_t out[4] = {};
  // Starts at offset 2, wants 4 bytes → overflows by 2.
  EXPECT_FALSE(map.read(0x2002, out, 4));
}

// ===----------------------------------------------------------------------===
// Test 3: Read at address below any region fails
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ReadBeforeRegion) {
  auto *data = allocBuf({0xAA, 0xBB});
  map.addRegion(0x5000, data, 2, /*read_only=*/true);

  uint8_t out[1] = {};
  EXPECT_FALSE(map.read(0x4FFF, out, 1));
  EXPECT_FALSE(map.read(0x0000, out, 1));
}

// ===----------------------------------------------------------------------===
// Test 4: readInt decodes little-endian correctly for 1/2/4/8 byte sizes
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ReadInt_LE) {
  // 0xDEADBEEFCAFEBABE in little-endian byte order.
  auto *data = allocBuf({0xBE, 0xBA, 0xFE, 0xCA, 0xEF, 0xBE, 0xAD, 0xDE});
  map.addRegion(0x3000, data, 8, /*read_only=*/true);

  // 1-byte
  auto v1 = map.readInt(0x3000, 1);
  ASSERT_TRUE(v1.has_value());
  EXPECT_EQ(*v1, 0xBEu);

  // 2-byte
  auto v2 = map.readInt(0x3000, 2);
  ASSERT_TRUE(v2.has_value());
  EXPECT_EQ(*v2, 0xBABEu);

  // 4-byte
  auto v4 = map.readInt(0x3000, 4);
  ASSERT_TRUE(v4.has_value());
  EXPECT_EQ(*v4, 0xCAFEBABEu);

  // 8-byte
  auto v8 = map.readInt(0x3000, 8);
  ASSERT_TRUE(v8.has_value());
  EXPECT_EQ(*v8, 0xDEADBEEFCAFEBABEu);
}

// ===----------------------------------------------------------------------===
// Test 5: readInt with byte_size > 8 returns nullopt
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ReadInt_TooLarge) {
  auto *data = allocBuf(16, 0xFF);
  map.addRegion(0x4000, data, 16, /*read_only=*/true);

  EXPECT_FALSE(map.readInt(0x4000, 9).has_value());
  EXPECT_FALSE(map.readInt(0x4000, 16).has_value());
}

// ===----------------------------------------------------------------------===
// Test 6: Multiple non-contiguous regions, read from each
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, MultipleRegions) {
  auto *d1 = allocBuf({0x11, 0x22});
  auto *d2 = allocBuf({0x33, 0x44});
  map.addRegion(0x1000, d1, 2, /*read_only=*/true);
  map.addRegion(0x9000, d2, 2, /*read_only=*/true);

  uint8_t out1[2] = {};
  ASSERT_TRUE(map.read(0x1000, out1, 2));
  EXPECT_EQ(out1[0], 0x11);
  EXPECT_EQ(out1[1], 0x22);

  uint8_t out2[2] = {};
  ASSERT_TRUE(map.read(0x9000, out2, 2));
  EXPECT_EQ(out2[0], 0x33);
  EXPECT_EQ(out2[1], 0x44);

  // Gap between regions is unmapped.
  uint8_t gap[1] = {};
  EXPECT_FALSE(map.read(0x5000, gap, 1));
}

// ===----------------------------------------------------------------------===
// Test 7: Import lookup returns correct entry
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ImportLookup) {
  map.addImport(0x140010000, "kernel32.dll", "VirtualAlloc");

  auto *entry = map.lookupImport(0x140010000);
  ASSERT_NE(entry, nullptr);
  EXPECT_EQ(entry->module, "kernel32.dll");
  EXPECT_EQ(entry->function, "VirtualAlloc");
}

// ===----------------------------------------------------------------------===
// Test 8: Import lookup for unknown VA returns nullptr
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ImportLookup_Miss) {
  map.addImport(0x140010000, "kernel32.dll", "VirtualAlloc");
  EXPECT_EQ(map.lookupImport(0x140010008), nullptr);
  EXPECT_EQ(map.lookupImport(0x0), nullptr);
}

// ===----------------------------------------------------------------------===
// Test 9: Basic relocation check
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, Relocation_Basic) {
  map.addRelocation(0x140001000, 8);
  map.finalizeRelocations();

  EXPECT_TRUE(map.isRelocated(0x140001000, 8));
  // Partial overlap: query inside the relocated range.
  EXPECT_TRUE(map.isRelocated(0x140001004, 4));
}

// ===----------------------------------------------------------------------===
// Test 10: Non-relocated address returns false
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, Relocation_NoOverlap) {
  map.addRelocation(0x140001000, 8);
  map.finalizeRelocations();

  // Before the relocation.
  EXPECT_FALSE(map.isRelocated(0x140000FF0, 8));
  // After the relocation.
  EXPECT_FALSE(map.isRelocated(0x140001008, 4));
}

// ===----------------------------------------------------------------------===
// Test 11: classifyRelocatedValue — NormalAddress when in image range
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ClassifyRelocated_Normal) {
  map.setImageBase(0x140000000);
  map.setImageSize(0x100000);
  map.addRelocation(0x140001000, 8);
  map.finalizeRelocations();

  // On-disk value within [image_base, image_base + image_size).
  auto kind = map.classifyRelocatedValue(0x140001000, 8, 0x140050000);
  EXPECT_EQ(kind, omill::RelocValueKind::NormalAddress);
}

// ===----------------------------------------------------------------------===
// Test 12: classifyRelocatedValue — Suspicious when outside image range
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ClassifyRelocated_Suspicious) {
  map.setImageBase(0x140000000);
  map.setImageSize(0x100000);
  map.addRelocation(0x140001000, 8);
  map.finalizeRelocations();

  // On-disk value outside image range → suspicious.
  auto kind = map.classifyRelocatedValue(0x140001000, 8, 0xDEADBEEF);
  EXPECT_EQ(kind, omill::RelocValueKind::Suspicious);
}

// ===----------------------------------------------------------------------===
// Test 13: classifyRelocatedValue — NotRelocated for non-relocated addr
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, ClassifyRelocated_NotRelocated) {
  map.setImageBase(0x140000000);
  map.setImageSize(0x100000);
  map.finalizeRelocations();

  auto kind = map.classifyRelocatedValue(0x140002000, 8, 0x140050000);
  EXPECT_EQ(kind, omill::RelocValueKind::NotRelocated);
}

// ===----------------------------------------------------------------------===
// Test 14: isSuspiciousImageBase — zero, kernel, system DLL ranges
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, SuspiciousImageBase) {
  // Zero base.
  map.setImageBase(0);
  EXPECT_TRUE(map.isSuspiciousImageBase());

  // Kernel-mode range.
  map.setImageBase(0x8000000000000000ULL);
  EXPECT_TRUE(map.isSuspiciousImageBase());

  // System DLL range (0x7FF*'****'0000).
  map.setImageBase(0x7FF800000000ULL);
  EXPECT_TRUE(map.isSuspiciousImageBase());

  // Low address (below 64KB).
  map.setImageBase(0x1000);
  EXPECT_TRUE(map.isSuspiciousImageBase());

  // Normal user-mode PE base — not suspicious.
  map.setImageBase(0x140000000);
  EXPECT_FALSE(map.isSuspiciousImageBase());

  // 32-bit typical base — not suspicious.
  map.setImageBase(0x00400000);
  EXPECT_FALSE(map.isSuspiciousImageBase());
}

// ===----------------------------------------------------------------------===
// Test 15: empty() on fresh map
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, Empty) {
  EXPECT_TRUE(map.empty());

  auto *data = allocBuf({0x00});
  map.addRegion(0x1000, data, 1, /*read_only=*/true);
  EXPECT_FALSE(map.empty());
}

// ===----------------------------------------------------------------------===
// Test 16: empty() with only imports
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, EmptyWithImport) {
  EXPECT_TRUE(map.empty());
  map.addImport(0x140010000, "ntdll.dll", "RtlInitUnicodeString");
  EXPECT_FALSE(map.empty());
}

// ===----------------------------------------------------------------------===
// Test 17: Multiple relocations with finalization
// ===----------------------------------------------------------------------===

TEST_F(BinaryMemoryMapTest, MultipleRelocations) {
  map.addRelocation(0x140003000, 8);
  map.addRelocation(0x140001000, 4);
  map.addRelocation(0x140002000, 8);
  map.finalizeRelocations();

  EXPECT_TRUE(map.isRelocated(0x140001000, 4));
  EXPECT_TRUE(map.isRelocated(0x140002000, 8));
  EXPECT_TRUE(map.isRelocated(0x140003000, 8));
  EXPECT_FALSE(map.isRelocated(0x140004000, 4));
}

}  // namespace

#include "omill/Utils/ProtectedBoundaryUtils.h"

#include <gtest/gtest.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace {

TEST(ProtectedBoundaryUtilsTest, RecognizesVmEntryPushJumpStub) {
  omill::BinaryMemoryMap mem;

  uint8_t region[0x40] = {};
  region[0x00] = 0x68;  // push imm32
  region[0x01] = 0x25;
  region[0x02] = 0x87;
  region[0x03] = 0x22;
  region[0x04] = 0x43;
  region[0x05] = 0xE9;  // jmp +0x14 -> 0x101e
  region[0x06] = 0x14;
  region[0x1E] = 0xE9;  // jmp +0x0b -> 0x102e
  region[0x1F] = 0x0B;
  region[0x2E] = 0x90;
  region[0x2F] = 0x90;
  region[0x30] = 0xC3;

  mem.addRegion(0x1000, region, sizeof(region), /*read_only=*/true);

  auto info = omill::classifyProtectedBoundary(mem, 0x1000);
  ASSERT_TRUE(info.has_value());
  EXPECT_TRUE(info->is_vm_entry_stub);
  EXPECT_EQ(info->entry_va, 0x1000u);
  EXPECT_EQ(info->canonical_target_va, 0x102Eu);
}

TEST(ProtectedBoundaryUtilsTest, RejectsPlainRelativeJumpThunk) {
  omill::BinaryMemoryMap mem;

  const uint8_t thunk[] = {
      0xE9, 0x0B, 0x00, 0x00, 0x00,
  };
  mem.addRegion(0x2000, thunk, sizeof(thunk), /*read_only=*/true);

  auto info = omill::classifyProtectedBoundary(mem, 0x2000);
  EXPECT_FALSE(info.has_value());
}

}  // namespace

#include "omill/Analysis/VMTraceEmulator.h"

#include "omill/Analysis/BinaryMemoryMap.h"

#include <cstdint>
#include <cstring>
#include <memory>
#include <vector>

#include <gtest/gtest.h>

namespace {

/// Helper that builds a BinaryMemoryMap with a single executable code
/// region starting at \p base and returns the (owned) map.
class CallTargetBridgeFixture : public ::testing::Test {
 protected:
  static constexpr uint64_t kBase = 0x140001000ULL;

  /// Store \p bytes as the code region and return the map.  The backing
  /// buffer is owned by \p owned_bytes_.  Automatically pads the region
  /// with NOPs so the emulator can always read 15 bytes past every
  /// instruction and any in-range jmp destination lands in executable
  /// memory.
  void setCode(std::initializer_list<uint8_t> bytes) {
    owned_bytes_.assign(bytes.begin(), bytes.end());
    owned_bytes_.resize(owned_bytes_.size() + 32, 0x90);
    map_.addRegion(kBase, owned_bytes_.data(), owned_bytes_.size(),
                   /*read_only=*/true, /*executable=*/true);
  }

  /// Variant using a vector for larger sequences.
  void setCode(std::vector<uint8_t> bytes) {
    owned_bytes_ = std::move(bytes);
    owned_bytes_.resize(owned_bytes_.size() + 32, 0x90);
    map_.addRegion(kBase, owned_bytes_.data(), owned_bytes_.size(),
                   /*read_only=*/true, /*executable=*/true);
  }

  omill::BinaryMemoryMap map_;
  std::vector<uint8_t> owned_bytes_;
};

// 1. `push imm32; jmp rel32` (10 bytes): the canonical VMProtect return
//    address thunk.  Expect one -8 stack write with the pushed imm and a
//    net RSP delta of -8.
TEST_F(CallTargetBridgeFixture, PushImmJmp10Byte) {
  // 0x00: 68 01 02 03 04         push 0x04030201
  // 0x05: E9 00 00 00 00         jmp +0 (-> 0x0A)
  // 0x0A: 90                     (padding nop so target is executable)
  setCode({0x68, 0x01, 0x02, 0x03, 0x04, 0xE9, 0x00, 0x00, 0x00, 0x00,
           0x90});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  ASSERT_TRUE(effect.has_value());
  ASSERT_EQ(effect->stack_writes.size(), 1u);
  EXPECT_EQ(effect->stack_writes[0].rsp_offset, -8);
  EXPECT_EQ(effect->stack_writes[0].size_bytes, 8u);
  EXPECT_EQ(effect->stack_writes[0].value, 0x04030201ULL);
  EXPECT_EQ(effect->net_rsp_delta, -8);
  EXPECT_EQ(effect->final_jump_target_pc, kBase + 10);
  EXPECT_EQ(effect->terminator,
            omill::CallTargetBridgeEffect::Terminator::kJmpConst);
}

// 2. `push imm32; lea rsp,[rsp+disp8]; jmp rel32` (15 bytes): VMProtect's
//    push-imm + RSP-adjust thunk.  Net RSP delta = disp8 - 8.
TEST_F(CallTargetBridgeFixture, PushImmLeaJmp15Byte) {
  // 0x00: 68 11 22 33 44            push 0x44332211
  // 0x05: 48 8D 64 24 18            lea rsp, [rsp+0x18]
  // 0x0A: E9 00 00 00 00            jmp +0 (-> 0x0F)
  setCode({0x68, 0x11, 0x22, 0x33, 0x44,
           0x48, 0x8D, 0x64, 0x24, 0x18,
           0xE9, 0x00, 0x00, 0x00, 0x00,
           0x90});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  ASSERT_TRUE(effect.has_value());
  ASSERT_EQ(effect->stack_writes.size(), 1u);
  EXPECT_EQ(effect->stack_writes[0].rsp_offset, -8);
  EXPECT_EQ(effect->stack_writes[0].value, 0x44332211ULL);
  EXPECT_EQ(effect->net_rsp_delta, 0x10);  // 0x18 - 8
  EXPECT_EQ(effect->final_jump_target_pc, kBase + 15);
}

// 3. `lea rsp,[rsp+disp8]; jmp rel32`: no stack writes, non-zero RSP
//    delta, jump terminator.
TEST_F(CallTargetBridgeFixture, LeaJmpOnly) {
  // 0x00: 48 8D 64 24 10    lea rsp, [rsp+0x10]
  // 0x05: E9 00 00 00 00    jmp +0 (-> 0x0A)
  setCode({0x48, 0x8D, 0x64, 0x24, 0x10,
           0xE9, 0x00, 0x00, 0x00, 0x00,
           0x90});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  ASSERT_TRUE(effect.has_value());
  EXPECT_TRUE(effect->stack_writes.empty());
  EXPECT_EQ(effect->net_rsp_delta, 0x10);
  EXPECT_EQ(effect->terminator,
            omill::CallTargetBridgeEffect::Terminator::kJmpConst);
  EXPECT_EQ(effect->final_jump_target_pc, kBase + 10);
}

// 4. `mov qword [rsp+disp8], imm32; jmp rel32`: overwrite an arbitrary
//    stack slot with a constant and then jmp.
TEST_F(CallTargetBridgeFixture, MovRspDispImmJmp) {
  // 0x00: 48 C7 44 24 08 11 22 33 44  mov qword [rsp+8], 0x44332211
  // 0x09: E9 00 00 00 00              jmp +0 (-> 0x0E)
  setCode({0x48, 0xC7, 0x44, 0x24, 0x08, 0x11, 0x22, 0x33, 0x44,
           0xE9, 0x00, 0x00, 0x00, 0x00,
           0x90});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  ASSERT_TRUE(effect.has_value());
  ASSERT_EQ(effect->stack_writes.size(), 1u);
  EXPECT_EQ(effect->stack_writes[0].rsp_offset, 8);
  EXPECT_EQ(effect->stack_writes[0].value, 0x44332211ULL);
  EXPECT_EQ(effect->net_rsp_delta, 0);
  EXPECT_EQ(effect->final_jump_target_pc, kBase + 14);
}

// 5. Pure trampoline: `jmp rel32`.  No stack writes, no RSP delta.
TEST_F(CallTargetBridgeFixture, PureJmp) {
  // 0x00: E9 00 00 00 00    jmp +0 (-> 0x05)
  setCode({0xE9, 0x00, 0x00, 0x00, 0x00, 0x90});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  ASSERT_TRUE(effect.has_value());
  EXPECT_TRUE(effect->stack_writes.empty());
  EXPECT_EQ(effect->net_rsp_delta, 0);
  EXPECT_EQ(effect->terminator,
            omill::CallTargetBridgeEffect::Terminator::kJmpConst);
  EXPECT_EQ(effect->final_jump_target_pc, kBase + 5);
}

// 6. `push imm32; dec r8w; jmp rel32`: push + 16-bit scratch op.  The
//    scratch op writes to a tainted register but nothing is spilled to
//    the stack, so folding should still succeed.
TEST_F(CallTargetBridgeFixture, PushImmArithJmp) {
  // 0x00: 68 AA BB CC DD          push 0xDDCCBBAA
  // 0x05: 66 41 FF C8             dec r8w
  // 0x09: E9 00 00 00 00          jmp +0 (-> 0x0E)
  setCode({0x68, 0xAA, 0xBB, 0xCC, 0xDD,
           0x66, 0x41, 0xFF, 0xC8,
           0xE9, 0x00, 0x00, 0x00, 0x00,
           0x90});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  ASSERT_TRUE(effect.has_value());
  ASSERT_EQ(effect->stack_writes.size(), 1u);
  EXPECT_EQ(effect->stack_writes[0].rsp_offset, -8);
  // 0xDDCCBBAA sign-extends to 0xFFFFFFFFDDCCBBAA.
  EXPECT_EQ(effect->stack_writes[0].value, 0xFFFFFFFFDDCCBBAAULL);
  EXPECT_EQ(effect->net_rsp_delta, -8);
}

// 7. Real call: `call rel32; ret`.  Must be refused so nested calls
//    don't get folded into their caller.
TEST_F(CallTargetBridgeFixture, RejectsRealCall) {
  // 0x00: E8 00 00 00 00    call +0 (-> 0x05)
  // 0x05: C3                ret
  setCode({0xE8, 0x00, 0x00, 0x00, 0x00, 0xC3});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  EXPECT_FALSE(effect.has_value());
}

// 8. `mov [rsp], rcx; jmp rel32` with rcx uninitialized.  We can't fold
//    symbolic stores to the stack.
TEST_F(CallTargetBridgeFixture, RejectsSymbolicStackWrite) {
  // 0x00: 48 89 0C 24        mov [rsp], rcx
  // 0x04: E9 00 00 00 00     jmp +0 (-> 0x09)
  setCode({0x48, 0x89, 0x0C, 0x24, 0xE9, 0x00, 0x00, 0x00, 0x00});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  EXPECT_FALSE(effect.has_value());
}

// 9. Indirect jump: `jmp [rip+0]`.  Refused because we can't prove the
//    target.
TEST_F(CallTargetBridgeFixture, RejectsIndirectJmp) {
  // 0x00: FF 25 00 00 00 00    jmp [rip+0]  (disp goes past code buf)
  setCode({0xFF, 0x25, 0x00, 0x00, 0x00, 0x00});

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  EXPECT_FALSE(effect.has_value());
}

// 10. Step limit: 17 NOPs followed by a jmp.  Must bail because
//     kMaxSteps = 16.
TEST_F(CallTargetBridgeFixture, StepLimitBailout) {
  // The bridge analyzer uses a two-tier step budget (16 + 512).
  // 513 NOPs exceeds both tiers.
  std::vector<uint8_t> bytes;
  for (int i = 0; i < 513; ++i) {
    bytes.push_back(0x90);  // nop
  }
  bytes.insert(bytes.end(),
               {0xE9, 0x00, 0x00, 0x00, 0x00});  // jmp +0
  setCode(std::move(bytes));

  auto effect = omill::analyzeCallTargetBridgeEffect(map_, kBase);
  EXPECT_FALSE(effect.has_value());
}

}  // namespace

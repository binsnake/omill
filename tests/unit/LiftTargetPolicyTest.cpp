#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Arch/ArchABI.h"
#include "omill/BC/LiftTargetPolicy.h"
#include "omill/BC/DecodeInstruction.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <memory>
#include <vector>

namespace {

class LiftTargetPolicyTest : public ::testing::Test {
 protected:
  omill::BinaryMemoryMap map;

  const uint8_t *alloc(std::initializer_list<uint8_t> data) {
    auto buf = std::make_unique<uint8_t[]>(data.size());
    std::memcpy(buf.get(), data.begin(), data.size());
    auto *ptr = buf.get();
    bufs_.push_back(std::move(buf));
    return ptr;
  }

 private:
  std::vector<std::unique_ptr<uint8_t[]>> bufs_;
};

TEST_F(LiftTargetPolicyTest, ResolveLiftTargetReturnsExactFallthroughEntry) {
  auto *code = alloc({0xE8, 0x00, 0x00, 0x00, 0x00, 0xC3});
  map.addRegion(0x18000188E, code, 6, /*read_only=*/true,
                /*executable=*/true);

  auto policy = omill::createBinaryLiftTargetPolicy(
      &map, omill::TargetArch::kX86_64);
  auto decision = policy->ResolveLiftTarget(
      0x18000188E, 0x180001893,
      omill::LiftTargetEdgeKind::kCallFallthrough);

  EXPECT_EQ(decision.classification,
            omill::LiftTargetClassification::kExactFallthroughEntry);
  EXPECT_EQ(decision.trust, omill::LiftTargetTrust::kExactFallthrough);
  ASSERT_TRUE(decision.effective_target_pc.has_value());
  EXPECT_EQ(*decision.effective_target_pc, 0x180001893ULL);
  EXPECT_TRUE(decision.is_exact_fallthrough);
}

TEST_F(LiftTargetPolicyTest, ResolveDecodeFailureInvalidatesSuspiciousEntry) {
  auto *code = alloc({0xE8, 0x11, 0x22, 0x33, 0x44, 0x90, 0x90, 0x90});
  map.addRegion(0x1800B5B30, code, 8, /*read_only=*/true,
                /*executable=*/true);

  auto policy = omill::createBinaryLiftTargetPolicy(
      &map, omill::TargetArch::kX86_64);
  auto decision = policy->ResolveDecodeFailure(
      0x1800B5B31, 0x1800B5B35, {},
      omill::DecodeFailureContext{
          omill::LiftTargetEdgeKind::kDecodeFailureContinuation});

  EXPECT_EQ(decision.action, omill::DecodeFailureAction::kInvalidateEntry);
  EXPECT_EQ(decision.target.classification,
            omill::LiftTargetClassification::kInvalidatedExecutableEntry);
  EXPECT_EQ(decision.target.trust, omill::LiftTargetTrust::kInvalidatedEntry);
  EXPECT_EQ(decision.target.raw_target_pc, 0x1800B5B31ULL);
  ASSERT_TRUE(decision.target.invalidated_entry_source_pc.has_value());
  ASSERT_TRUE(decision.target.invalidated_entry_failed_pc.has_value());
  EXPECT_EQ(*decision.target.invalidated_entry_source_pc, 0x1800B5B31ULL);
  EXPECT_EQ(*decision.target.invalidated_entry_failed_pc, 0x1800B5B35ULL);
}
TEST_F(LiftTargetPolicyTest, ResolveDecodeFailureRedirectsWrappedDirectCallTarget) {
  auto *wrapper = alloc({
      0x48, 0x8D, 0x64, 0x24, 0x18,       // lea rsp, [rsp+18h]
      0xE8, 0x56, 0x00, 0x00, 0x00,       // call 0x180001060
      0x79, 0x23,                         // jns 0x180001032
      0x01, 0x06,                         // add [rsi], eax
      0x02, 0x00,                         // add al, [rax]
      0xCC, 0xCC,                         // trap padding
  });
  auto *callee = alloc({0xC3});
  map.addRegion(0x180001000, wrapper, 18, /*read_only=*/true,
                /*executable=*/true);
  map.addRegion(0x180001060, callee, 1, /*read_only=*/true,
                /*executable=*/true);

  auto policy = omill::createBinaryLiftTargetPolicy(
      &map, omill::TargetArch::kX86_64);
  auto decision = policy->ResolveDecodeFailure(
      0x18000100C, 0x180001010, {0x180001000},
      omill::DecodeFailureContext{
          omill::LiftTargetEdgeKind::kDecodeFailureContinuation});

  EXPECT_EQ(decision.action, omill::DecodeFailureAction::kRedirectToTarget);
  EXPECT_EQ(decision.target.classification,
            omill::LiftTargetClassification::kCanonicalOwner);
  ASSERT_TRUE(decision.target.effective_target_pc.has_value());
  EXPECT_EQ(*decision.target.effective_target_pc, 0x180001060ULL);
  ASSERT_TRUE(decision.target.invalidated_entry_source_pc.has_value());
  ASSERT_TRUE(decision.target.invalidated_entry_failed_pc.has_value());
  EXPECT_EQ(*decision.target.invalidated_entry_source_pc, 0x18000100CULL);
  EXPECT_EQ(*decision.target.invalidated_entry_failed_pc, 0x180001010ULL);
}

TEST_F(LiftTargetPolicyTest, DecodeInstructionRejectsOverlappingMovImmEntry) {
  auto *code = alloc({
      0x48, 0xB8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
      0xC3,
  });
  map.addRegion(0x180001690, code, 11, /*read_only=*/true,
                /*executable=*/true);

  const auto overlap_status =
      omill::ProbeDecodeInstruction(omill::TargetArch::kX86_64, map, 0x180001692);
  EXPECT_FALSE(overlap_status.usable);
}

TEST_F(LiftTargetPolicyTest, ResolveLiftTargetPreservesExactSequentialTargets) {
  auto *code = alloc({
      0x48, 0x0F, 0xCA,  // bswap rdx
      0x48, 0xF7, 0xE1,  // mul rcx
      0x41, 0xF7, 0xF6,  // div r14d
      0xC3,
  });
  map.addRegion(0x180001BE2, code, 10, /*read_only=*/true,
                /*executable=*/true);

  auto policy = omill::createBinaryLiftTargetPolicy(
      &map, omill::TargetArch::kX86_64);

  const auto trace_next = policy->ResolveLiftTarget(
      0x180001BDF, 0x180001BE2, omill::LiftTargetEdgeKind::kTraceNext);
  ASSERT_TRUE(trace_next.effective_target_pc.has_value());
  EXPECT_EQ(trace_next.classification,
            omill::LiftTargetClassification::kLiftableEntry);
  EXPECT_EQ(*trace_next.effective_target_pc, 0x180001BE2ULL);

  const auto call_fallthrough = policy->ResolveLiftTarget(
      0x180001BE2, 0x180001BE5, omill::LiftTargetEdgeKind::kCallFallthrough);
  ASSERT_TRUE(call_fallthrough.effective_target_pc.has_value());
  EXPECT_EQ(call_fallthrough.classification,
            omill::LiftTargetClassification::kLiftableEntry);
  EXPECT_EQ(*call_fallthrough.effective_target_pc, 0x180001BE5ULL);

  const auto div_fallthrough = policy->ResolveLiftTarget(
      0x180001BE5, 0x180001BE8, omill::LiftTargetEdgeKind::kTraceNext);
  ASSERT_TRUE(div_fallthrough.effective_target_pc.has_value());
  EXPECT_EQ(div_fallthrough.classification,
            omill::LiftTargetClassification::kLiftableEntry);
  EXPECT_EQ(*div_fallthrough.effective_target_pc, 0x180001BE8ULL);
}




}  // namespace

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Arch/ArchABI.h"
#include "omill/BC/LiftTargetPolicy.h"

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

}  // namespace

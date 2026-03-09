#include "omill/Analysis/VMTraceMap.h"

#include <gtest/gtest.h>

namespace {

TEST(VMTraceMapTest, PreservesPerHashTraceRecords) {
  omill::VMTraceMap trace_map(0x1402A1000ULL, 0x1402A112BULL);

  omill::VMTraceRecord first;
  first.handler_va = 0x140C5416EULL;
  first.incoming_hash = 0xA26346B5C9C0B6DBULL;
  first.outgoing_hash = 0xE5D3BDF5888D2147ULL;
  first.exit_target_va = 0x14032958FULL;
  first.successors = {0x141448082ULL};

  omill::VMTraceRecord second;
  second.handler_va = 0x140C5416EULL;
  second.incoming_hash = 0x1111222233334444ULL;
  second.outgoing_hash = 0x5555666677778888ULL;
  second.exit_target_va = 0x140329600ULL;
  second.successors = {0x141449999ULL};
  second.passed_vmexit = true;
  second.native_target_va = 0x140123456ULL;

  trace_map.recordTrace(std::move(first));
  trace_map.recordTrace(std::move(second));

  auto first_record =
      trace_map.getTraceForHash(0x140C5416EULL, 0xA26346B5C9C0B6DBULL);
  ASSERT_TRUE(first_record.has_value());
  EXPECT_EQ(first_record->outgoing_hash, 0xE5D3BDF5888D2147ULL);
  ASSERT_EQ(first_record->successors.size(), 1u);
  EXPECT_EQ(first_record->successors.front(), 0x141448082ULL);
  EXPECT_FALSE(first_record->passed_vmexit);

  auto second_record =
      trace_map.getTraceForHash(0x140C5416EULL, 0x1111222233334444ULL);
  ASSERT_TRUE(second_record.has_value());
  EXPECT_EQ(second_record->native_target_va, 0x140123456ULL);
  EXPECT_TRUE(second_record->passed_vmexit);
  ASSERT_EQ(second_record->successors.size(), 1u);
  EXPECT_EQ(second_record->successors.front(), 0x141449999ULL);

  auto records = trace_map.getTraceRecords(0x140C5416EULL);
  ASSERT_EQ(records.size(), 2u);

  auto aggregate = trace_map.getTraceTargets(0x140C5416EULL);
  ASSERT_EQ(aggregate.size(), 2u);
  EXPECT_EQ(aggregate[0], 0x141448082ULL);
  EXPECT_EQ(aggregate[1], 0x141449999ULL);
}

TEST(VMTraceMapTest, ReplacesMatchingIncomingHash) {
  omill::VMTraceMap trace_map(0, 0);

  omill::VMTraceRecord original;
  original.handler_va = 0x140111111ULL;
  original.incoming_hash = 0xABCDEFULL;
  original.outgoing_hash = 0x1111ULL;
  original.successors = {0x140222222ULL};

  omill::VMTraceRecord updated;
  updated.handler_va = 0x140111111ULL;
  updated.incoming_hash = 0xABCDEFULL;
  updated.outgoing_hash = 0x2222ULL;
  updated.exit_target_va = 0x140300000ULL;
  updated.successors = {0x140333333ULL};

  trace_map.recordTrace(std::move(original));
  trace_map.recordTrace(std::move(updated));

  auto record = trace_map.getTraceForHash(0x140111111ULL, 0xABCDEFULL);
  ASSERT_TRUE(record.has_value());
  EXPECT_EQ(record->outgoing_hash, 0x2222ULL);
  EXPECT_EQ(record->exit_target_va, 0x140300000ULL);
  ASSERT_EQ(record->successors.size(), 1u);
  EXPECT_EQ(record->successors.front(), 0x140333333ULL);

  auto records = trace_map.getTraceRecords(0x140111111ULL);
  ASSERT_EQ(records.size(), 1u);
}

TEST(VMTraceMapTest, FollowsConcreteHashThreadedPath) {
  omill::VMTraceMap trace_map(0x1402A1000ULL, 0x1402A112BULL);

  omill::VMTraceRecord wrapper;
  wrapper.handler_va = 0x1402A2000ULL;
  wrapper.incoming_hash = 0xAAAABBBBCCCCDDDDULL;
  wrapper.outgoing_hash = 0xAAAABBBBCCCCDDDDULL;
  wrapper.exit_target_va = 0x140C5416EULL;
  wrapper.successors = {0x140C5416EULL};

  omill::VMTraceRecord first;
  first.handler_va = 0x140C5416EULL;
  first.incoming_hash = 0xAAAABBBBCCCCDDDDULL;
  first.outgoing_hash = 0x1111222233334444ULL;
  first.exit_target_va = 0x141448082ULL;
  first.successors = {0x141448082ULL};

  omill::VMTraceRecord second;
  second.handler_va = 0x141448082ULL;
  second.incoming_hash = 0x1111222233334444ULL;
  second.outgoing_hash = 0x5555666677778888ULL;
  second.exit_target_va = 0x1402A112BULL;
  second.successors = {0x1402A112BULL};
  second.is_vmexit = true;
  second.passed_vmexit = true;
  second.native_target_va = 0x140123456ULL;

  trace_map.recordTrace(std::move(wrapper));
  trace_map.recordTrace(std::move(first));
  trace_map.recordTrace(std::move(second));

  auto flat =
      trace_map.followFlatTrace(0x1402A2000ULL, 0xAAAABBBBCCCCDDDDULL);
  ASSERT_TRUE(flat.completed());
  ASSERT_EQ(flat.stop_reason, omill::VMFlatTraceStopReason::VmExit);
  ASSERT_EQ(flat.records.size(), 3u);
  EXPECT_EQ(flat.records[0].handler_va, 0x1402A2000ULL);
  EXPECT_EQ(flat.records[1].handler_va, 0x140C5416EULL);
  EXPECT_EQ(flat.records[2].native_target_va, 0x140123456ULL);
}

TEST(VMTraceMapTest, StopsOnAmbiguousSuccessor) {
  omill::VMTraceMap trace_map(0, 0);

  omill::VMTraceRecord root;
  root.handler_va = 0x140111111ULL;
  root.incoming_hash = 0x1234ULL;
  root.outgoing_hash = 0x5678ULL;
  root.successors = {0x140222222ULL, 0x140333333ULL};

  trace_map.recordTrace(std::move(root));

  auto flat = trace_map.followFlatTrace(0x140111111ULL, 0x1234ULL);
  ASSERT_EQ(flat.stop_reason, omill::VMFlatTraceStopReason::AmbiguousSuccessor);
  ASSERT_EQ(flat.records.size(), 1u);
  EXPECT_EQ(flat.stop_handler_va, 0x140111111ULL);
  EXPECT_EQ(flat.stop_hash, 0x1234ULL);
}


}  // namespace

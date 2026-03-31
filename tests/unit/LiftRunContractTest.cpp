#include "omill/Tools/LiftRunContract.h"

#include <gtest/gtest.h>

#include <llvm/Support/JSON.h>

#include <algorithm>

namespace {

using namespace omill::tools;

TEST(LiftRunContractTest, RequestRoundTripJSON) {
  LiftRunRequest req;
  req.input_filename = "input.bin";
  req.va = "0x140001000";
  req.raw = true;
  req.base = 0x140000000;
  req.output_filename = "out.ll";
  req.deobfuscate = true;
  req.devirtualize = true;
  req.resolve_targets = true;
  req.max_iterations = 42;
  req.event_jsonl = "events.jsonl";
  req.event_detail = EventDetailLevel::kDetailed;

  auto obj = toJSON(req);
  auto parsed = parseLiftRunRequest(llvm::json::Value(std::move(obj)));
  ASSERT_TRUE(parsed.has_value());
  EXPECT_EQ(parsed->input_filename, req.input_filename);
  EXPECT_EQ(parsed->va, req.va);
  EXPECT_EQ(parsed->raw, req.raw);
  EXPECT_EQ(parsed->base, req.base);
  EXPECT_EQ(parsed->output_filename, req.output_filename);
  EXPECT_EQ(parsed->deobfuscate, req.deobfuscate);
  EXPECT_EQ(parsed->devirtualize, req.devirtualize);
  EXPECT_EQ(parsed->resolve_targets, req.resolve_targets);
  EXPECT_EQ(parsed->max_iterations, req.max_iterations);
  EXPECT_EQ(parsed->event_jsonl, req.event_jsonl);
  EXPECT_EQ(parsed->event_detail, req.event_detail);
}

TEST(LiftRunContractTest, EventSchemaValidation) {
  llvm::json::Object obj;
  obj["schema_version"] = LiftRunEvent::kSchemaVersion + 1;
  obj["run_id"] = "run_1";
  obj["seq"] = 1;
  obj["timestamp_ms"] = 1;
  obj["kind"] = "run_started";
  obj["severity"] = "info";
  obj["message"] = "x";
  obj["payload"] = llvm::json::Object{};

  auto parsed = parseLiftRunEvent(llvm::json::Value(std::move(obj)));
  EXPECT_FALSE(parsed.has_value());
}

TEST(LiftRunContractTest, BuildArgsIncludesRequestedOptions) {
  LiftRunRequest req;
  req.input_filename = "sample.exe";
  req.va = "0x1234";
  req.output_filename = "lifted.ll";
  req.deobfuscate = true;
  req.devirtualize = true;
  req.resolve_targets = true;
  req.max_iterations = 7;
  req.raw = true;
  req.base = 4096;
  req.event_jsonl = "events.jsonl";
  req.event_detail = EventDetailLevel::kDetailed;

  auto args = buildOmillLiftArgs(req);
  ASSERT_GE(args.size(), 2u);
  EXPECT_EQ(args[0], "sample.exe");

  auto contains = [&](llvm::StringRef token) {
    return std::find(args.begin(), args.end(), token.str()) != args.end();
  };

  EXPECT_TRUE(contains("--va"));
  EXPECT_TRUE(contains("0x1234"));
  EXPECT_TRUE(contains("-o"));
  EXPECT_TRUE(contains("lifted.ll"));
  EXPECT_TRUE(contains("--deobfuscate"));
  EXPECT_TRUE(contains("--devirtualize"));
  EXPECT_TRUE(contains("--resolve-targets"));
  EXPECT_TRUE(contains("--max-iterations"));
  EXPECT_TRUE(contains("7"));
  EXPECT_TRUE(contains("--raw"));
  EXPECT_TRUE(contains("--base"));
  EXPECT_TRUE(contains("4096"));
  EXPECT_TRUE(contains("--event-jsonl"));
  EXPECT_TRUE(contains("events.jsonl"));
  EXPECT_TRUE(contains("--event-detail"));
  EXPECT_TRUE(contains("detailed"));
}

TEST(LiftRunContractTest, ParseEventDetailLevel) {
  auto basic = parseEventDetailLevel("basic");
  auto detailed = parseEventDetailLevel("detailed");
  auto invalid = parseEventDetailLevel("verbose");
  ASSERT_TRUE(basic.has_value());
  ASSERT_TRUE(detailed.has_value());
  EXPECT_EQ(*basic, EventDetailLevel::kBasic);
  EXPECT_EQ(*detailed, EventDetailLevel::kDetailed);
  EXPECT_FALSE(invalid.has_value());
}

}  // namespace

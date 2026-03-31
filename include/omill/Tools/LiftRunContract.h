#pragma once

#include <llvm/Support/JSON.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace omill::tools {

enum class EventDetailLevel {
  kBasic,
  kDetailed,
};

struct LiftRunRequest {
  std::string input_filename;
  std::string va;
  bool raw = false;
  uint64_t base = 0;
  std::string output_filename = "-";

  bool no_abi = false;
  bool deobfuscate = false;
  bool devirtualize = false;
  bool resolve_targets = false;
  unsigned max_iterations = 10;
  bool ipcp = false;
  bool resolve_exceptions = false;
  bool block_lift = false;
  bool dump_ir = false;
  std::string vm_entry;
  std::string vm_exit;
  bool omill_time_passes = false;
  bool verify_each = false;
  std::string trace_func;
  bool dump_func_phases = false;
  std::string scan_section;
  std::string scan_output = "-";
  bool scan_all = false;
  std::string deobf_targets;
  std::string deobf_section;
  unsigned min_func_size = 64;

  std::string event_jsonl;
  EventDetailLevel event_detail = EventDetailLevel::kBasic;
};

struct LiftRunEvent {
  static constexpr int kSchemaVersion = 1;

  int schema_version = kSchemaVersion;
  std::string run_id;
  uint64_t seq = 0;
  int64_t timestamp_ms = 0;
  std::string kind;
  std::string severity = "info";
  std::string message;
  llvm::json::Object payload;
};

struct LiftRunResult {
  int exit_code = 0;
  std::vector<std::string> artifacts;
  std::vector<std::string> warnings;
  std::vector<std::string> errors;
};

class IExecutor {
 public:
  virtual ~IExecutor() = default;
  virtual std::string name() const = 0;
  virtual std::vector<std::string> buildInvocation(
      const LiftRunRequest &request) const = 0;
};

class SubprocessExecutor final : public IExecutor {
 public:
  explicit SubprocessExecutor(std::string binary_path = "omill-lift")
      : binary_path_(std::move(binary_path)) {}

  std::string name() const override { return "subprocess"; }
  std::vector<std::string> buildInvocation(
      const LiftRunRequest &request) const override;

 private:
  std::string binary_path_;
};

class InProcessExecutor final : public IExecutor {
 public:
  std::string name() const override { return "in_process"; }
  std::vector<std::string> buildInvocation(
      const LiftRunRequest &request) const override;
};

llvm::json::Object toJSON(const LiftRunRequest &request);
std::optional<LiftRunRequest> parseLiftRunRequest(const llvm::json::Value &v);

llvm::json::Object toJSON(const LiftRunEvent &event);
std::optional<LiftRunEvent> parseLiftRunEvent(const llvm::json::Value &v);

llvm::json::Object toJSON(const LiftRunResult &result);
std::optional<LiftRunResult> parseLiftRunResult(const llvm::json::Value &v);

std::vector<std::string> buildOmillLiftArgs(const LiftRunRequest &request);

const char *toString(EventDetailLevel level);
std::optional<EventDetailLevel> parseEventDetailLevel(llvm::StringRef text);

}  // namespace omill::tools

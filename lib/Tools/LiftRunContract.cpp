#include "omill/Tools/LiftRunContract.h"

#include <llvm/ADT/StringRef.h>

#include <utility>

namespace omill::tools {

namespace {

void pushFlag(std::vector<std::string> &args, bool enabled, const char *flag) {
  if (enabled)
    args.emplace_back(flag);
}

void pushValue(std::vector<std::string> &args, llvm::StringRef flag,
               const std::string &value) {
  if (value.empty())
    return;
  args.emplace_back(flag.str());
  args.emplace_back(value);
}

void pushUnsigned(std::vector<std::string> &args, llvm::StringRef flag,
                  uint64_t value, uint64_t default_value) {
  if (value == default_value)
    return;
  args.emplace_back(flag.str());
  args.emplace_back(std::to_string(value));
}

}  // namespace

const char *toString(EventDetailLevel level) {
  switch (level) {
    case EventDetailLevel::kBasic:
      return "basic";
    case EventDetailLevel::kDetailed:
      return "detailed";
  }
  return "basic";
}

std::optional<EventDetailLevel> parseEventDetailLevel(llvm::StringRef text) {
  if (text.equals_insensitive("basic"))
    return EventDetailLevel::kBasic;
  if (text.equals_insensitive("detailed"))
    return EventDetailLevel::kDetailed;
  return std::nullopt;
}

std::vector<std::string> buildOmillLiftArgs(const LiftRunRequest &request) {
  std::vector<std::string> args;
  if (!request.input_filename.empty())
    args.push_back(request.input_filename);

  pushValue(args, "--va", request.va);
  pushFlag(args, request.raw, "--raw");
  pushUnsigned(args, "--base", request.base, 0);
  pushValue(args, "-o", request.output_filename);

  pushFlag(args, request.no_abi, "--no-abi");
  pushFlag(args, request.deobfuscate, "--deobfuscate");
  pushFlag(args, request.devirtualize, "--devirtualize");
  pushFlag(args, request.resolve_targets, "--resolve-targets");
  pushUnsigned(args, "--max-iterations", request.max_iterations, 10);
  pushFlag(args, request.ipcp, "--ipcp");
  pushFlag(args, request.resolve_exceptions, "--resolve-exceptions");
  pushFlag(args, request.block_lift, "--block-lift");
  pushFlag(args, request.dump_ir, "--dump-ir");
  pushValue(args, "--vm-entry", request.vm_entry);
  pushValue(args, "--vm-exit", request.vm_exit);
  pushFlag(args, request.omill_time_passes, "--omill-time-passes");
  pushFlag(args, request.verify_each, "--verify-each");
  pushValue(args, "--trace-func", request.trace_func);
  pushFlag(args, request.dump_func_phases, "--dump-func-phases");
  pushValue(args, "--scan-section", request.scan_section);
  pushValue(args, "--scan-output", request.scan_output);
  pushFlag(args, request.scan_all, "--scan-all");
  pushValue(args, "--deobf-targets", request.deobf_targets);
  pushValue(args, "--deobf-section", request.deobf_section);
  pushUnsigned(args, "--min-func-size", request.min_func_size, 64);

  pushValue(args, "--event-jsonl", request.event_jsonl);
  if (!request.event_jsonl.empty() || request.event_detail != EventDetailLevel::kBasic) {
    args.emplace_back("--event-detail");
    args.emplace_back(toString(request.event_detail));
  }

  return args;
}

std::vector<std::string> SubprocessExecutor::buildInvocation(
    const LiftRunRequest &request) const {
  auto args = buildOmillLiftArgs(request);
  args.insert(args.begin(), binary_path_);
  return args;
}

std::vector<std::string> InProcessExecutor::buildInvocation(
    const LiftRunRequest &) const {
  return {"<in-process-not-implemented>"};
}

llvm::json::Object toJSON(const LiftRunRequest &request) {
  llvm::json::Object obj;
  obj["input_filename"] = request.input_filename;
  obj["va"] = request.va;
  obj["raw"] = request.raw;
  obj["base"] = static_cast<int64_t>(request.base);
  obj["output_filename"] = request.output_filename;
  obj["no_abi"] = request.no_abi;
  obj["deobfuscate"] = request.deobfuscate;
  obj["devirtualize"] = request.devirtualize;
  obj["resolve_targets"] = request.resolve_targets;
  obj["max_iterations"] = static_cast<int64_t>(request.max_iterations);
  obj["ipcp"] = request.ipcp;
  obj["resolve_exceptions"] = request.resolve_exceptions;
  obj["block_lift"] = request.block_lift;
  obj["dump_ir"] = request.dump_ir;
  obj["vm_entry"] = request.vm_entry;
  obj["vm_exit"] = request.vm_exit;
  obj["omill_time_passes"] = request.omill_time_passes;
  obj["verify_each"] = request.verify_each;
  obj["trace_func"] = request.trace_func;
  obj["dump_func_phases"] = request.dump_func_phases;
  obj["scan_section"] = request.scan_section;
  obj["scan_output"] = request.scan_output;
  obj["scan_all"] = request.scan_all;
  obj["deobf_targets"] = request.deobf_targets;
  obj["deobf_section"] = request.deobf_section;
  obj["min_func_size"] = static_cast<int64_t>(request.min_func_size);
  obj["event_jsonl"] = request.event_jsonl;
  obj["event_detail"] = toString(request.event_detail);
  return obj;
}

std::optional<LiftRunRequest> parseLiftRunRequest(const llvm::json::Value &v) {
  const auto *obj = v.getAsObject();
  if (!obj)
    return std::nullopt;

  LiftRunRequest request;
  if (auto s = obj->getString("input_filename"))
    request.input_filename = std::string(*s);
  if (auto s = obj->getString("va"))
    request.va = std::string(*s);
  if (auto b = obj->getBoolean("raw"))
    request.raw = *b;
  if (auto n = obj->getInteger("base"))
    request.base = static_cast<uint64_t>(*n);
  if (auto s = obj->getString("output_filename"))
    request.output_filename = std::string(*s);

  if (auto b = obj->getBoolean("no_abi"))
    request.no_abi = *b;
  if (auto b = obj->getBoolean("deobfuscate"))
    request.deobfuscate = *b;
  if (auto b = obj->getBoolean("devirtualize"))
    request.devirtualize = *b;
  if (auto b = obj->getBoolean("resolve_targets"))
    request.resolve_targets = *b;
  if (auto n = obj->getInteger("max_iterations"))
    request.max_iterations = static_cast<unsigned>(*n);
  if (auto b = obj->getBoolean("ipcp"))
    request.ipcp = *b;
  if (auto b = obj->getBoolean("resolve_exceptions"))
    request.resolve_exceptions = *b;
  if (auto b = obj->getBoolean("block_lift"))
    request.block_lift = *b;
  if (auto b = obj->getBoolean("dump_ir"))
    request.dump_ir = *b;
  if (auto s = obj->getString("vm_entry"))
    request.vm_entry = std::string(*s);
  if (auto s = obj->getString("vm_exit"))
    request.vm_exit = std::string(*s);
  if (auto b = obj->getBoolean("omill_time_passes"))
    request.omill_time_passes = *b;
  if (auto b = obj->getBoolean("verify_each"))
    request.verify_each = *b;
  if (auto s = obj->getString("trace_func"))
    request.trace_func = std::string(*s);
  if (auto b = obj->getBoolean("dump_func_phases"))
    request.dump_func_phases = *b;
  if (auto s = obj->getString("scan_section"))
    request.scan_section = std::string(*s);
  if (auto s = obj->getString("scan_output"))
    request.scan_output = std::string(*s);
  if (auto b = obj->getBoolean("scan_all"))
    request.scan_all = *b;
  if (auto s = obj->getString("deobf_targets"))
    request.deobf_targets = std::string(*s);
  if (auto s = obj->getString("deobf_section"))
    request.deobf_section = std::string(*s);
  if (auto n = obj->getInteger("min_func_size"))
    request.min_func_size = static_cast<unsigned>(*n);
  if (auto s = obj->getString("event_jsonl"))
    request.event_jsonl = std::string(*s);
  if (auto s = obj->getString("event_detail")) {
    auto parsed = parseEventDetailLevel(*s);
    if (!parsed)
      return std::nullopt;
    request.event_detail = *parsed;
  }

  return request;
}

llvm::json::Object toJSON(const LiftRunEvent &event) {
  llvm::json::Object obj;
  obj["schema_version"] = event.schema_version;
  obj["run_id"] = event.run_id;
  obj["seq"] = static_cast<int64_t>(event.seq);
  obj["timestamp_ms"] = event.timestamp_ms;
  obj["kind"] = event.kind;
  obj["severity"] = event.severity;
  obj["message"] = event.message;
  obj["payload"] = llvm::json::Value(llvm::json::Object(event.payload));
  return obj;
}

std::optional<LiftRunEvent> parseLiftRunEvent(const llvm::json::Value &v) {
  const auto *obj = v.getAsObject();
  if (!obj)
    return std::nullopt;

  LiftRunEvent event;
  if (auto n = obj->getInteger("schema_version"))
    event.schema_version = static_cast<int>(*n);
  if (event.schema_version != LiftRunEvent::kSchemaVersion)
    return std::nullopt;
  if (auto s = obj->getString("run_id"))
    event.run_id = std::string(*s);
  if (auto n = obj->getInteger("seq"))
    event.seq = static_cast<uint64_t>(*n);
  if (auto n = obj->getInteger("timestamp_ms"))
    event.timestamp_ms = *n;
  if (auto s = obj->getString("kind"))
    event.kind = std::string(*s);
  if (auto s = obj->getString("severity"))
    event.severity = std::string(*s);
  if (auto s = obj->getString("message"))
    event.message = std::string(*s);
  if (const auto *payload = obj->getObject("payload"))
    event.payload = *payload;
  return event;
}

llvm::json::Object toJSON(const LiftRunResult &result) {
  llvm::json::Object obj;
  obj["exit_code"] = result.exit_code;

  llvm::json::Array artifacts;
  for (const auto &a : result.artifacts)
    artifacts.push_back(a);
  obj["artifacts"] = std::move(artifacts);

  llvm::json::Array warnings;
  for (const auto &w : result.warnings)
    warnings.push_back(w);
  obj["warnings"] = std::move(warnings);

  llvm::json::Array errors;
  for (const auto &e : result.errors)
    errors.push_back(e);
  obj["errors"] = std::move(errors);

  return obj;
}

std::optional<LiftRunResult> parseLiftRunResult(const llvm::json::Value &v) {
  const auto *obj = v.getAsObject();
  if (!obj)
    return std::nullopt;

  LiftRunResult result;
  if (auto n = obj->getInteger("exit_code"))
    result.exit_code = static_cast<int>(*n);

  if (const auto *arr = obj->getArray("artifacts")) {
    for (const auto &item : *arr) {
      if (auto s = item.getAsString())
        result.artifacts.emplace_back(std::string(*s));
    }
  }

  if (const auto *arr = obj->getArray("warnings")) {
    for (const auto &item : *arr) {
      if (auto s = item.getAsString())
        result.warnings.emplace_back(std::string(*s));
    }
  }

  if (const auto *arr = obj->getArray("errors")) {
    for (const auto &item : *arr) {
      if (auto s = item.getAsString())
        result.errors.emplace_back(std::string(*s));
    }
  }

  return result;
}

}  // namespace omill::tools

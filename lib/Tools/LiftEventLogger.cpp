#include "omill/Tools/LiftEventLogger.h"

#include "omill/Omill.h"

#include <llvm/ADT/Twine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/Process.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/raw_ostream.h>

#include <chrono>
#include <cstdlib>
#include <string>
#include <vector>

using namespace llvm;

namespace omill::tools {


std::string hexString(uint64_t value) {
  return ("0x" + Twine::utohexstr(value)).str();
}

const char *controlTransferKindName(omill::RemillControlTransferKind kind) {
  switch (kind) {
    case omill::RemillControlTransferKind::kUnknown:
      return "unknown";
    case omill::RemillControlTransferKind::kConditionalBranch:
      return "conditional_branch";
    case omill::RemillControlTransferKind::kIndirectJump:
      return "indirect_jump";
    case omill::RemillControlTransferKind::kIndirectCall:
      return "indirect_call";
    case omill::RemillControlTransferKind::kDirectJump:
      return "direct_jump";
    case omill::RemillControlTransferKind::kDirectCall:
      return "direct_call";
  }
  return "unknown";
}

llvm::json::Array jsonPcArray(llvm::ArrayRef<uint64_t> values) {
  llvm::json::Array arr;
  for (uint64_t value : values)
    arr.push_back(hexString(value));
  return arr;
}

namespace {

bool wantIterativeSessionReport() {
  const char *env = std::getenv("OMILL_REPORT_ITERATIVE_SESSION");
  if (!env || env[0] == '\0')
    return false;
  return !(env[0] == '0' && env[1] == '\0');
}

const char *edgeKindName(omill::LiftEdgeKind kind) {
  switch (kind) {
    case omill::LiftEdgeKind::kDirectBranch:
      return "direct-branch";
    case omill::LiftEdgeKind::kDirectCall:
      return "direct-call";
    case omill::LiftEdgeKind::kIndirectBranch:
      return "indirect-branch";
    case omill::LiftEdgeKind::kIndirectCall:
      return "indirect-call";
    case omill::LiftEdgeKind::kReturn:
      return "return";
    case omill::LiftEdgeKind::kVmTrace:
      return "vm-trace";
  }
  return "unknown";
}


const char *runtimeArtifactStageName(
    omill::RuntimeArtifactStage stage) {
  switch (stage) {
    case omill::RuntimeArtifactStage::kFrontierRound:
      return "frontier_round";
    case omill::RuntimeArtifactStage::kOutputRecoveryRound:
      return "output_recovery_round";
    case omill::RuntimeArtifactStage::kOutputRecoveryImportRound:
      return "output_recovery_import_round";
    case omill::RuntimeArtifactStage::kFinalization:
      return "finalization";
  }
  return "unknown";
}

const char *importEligibilityName(omill::ImportEligibility eligibility) {
  switch (eligibility) {
    case omill::ImportEligibility::kImportable:
      return "importable";
    case omill::ImportEligibility::kRetryable:
      return "retryable";
    case omill::ImportEligibility::kRejected:
      return "rejected";
  }
  return "rejected";
}

const char *recoveryRejectionReasonName(
    omill::RecoveryRejectionReason reason) {
  switch (reason) {
    case omill::RecoveryRejectionReason::kNone:
      return "none";
    case omill::RecoveryRejectionReason::kChildLiftFailed:
      return "child_lift_failed";
    case omill::RecoveryRejectionReason::kImportFailed:
      return "import_failed";
    case omill::RecoveryRejectionReason::kTypeMismatch:
      return "type_mismatch";
    case omill::RecoveryRejectionReason::kParseFailed:
      return "parse_failed";
    case omill::RecoveryRejectionReason::kMissingRoot:
      return "missing_root";
    case omill::RecoveryRejectionReason::kDisallowedFunction:
      return "disallowed_function";
    case omill::RecoveryRejectionReason::kDeclarationRejected:
      return "declaration_rejected";
    case omill::RecoveryRejectionReason::kGlobalRejected:
      return "global_rejected";
    case omill::RecoveryRejectionReason::kRuntimeLeak:
      return "runtime_leak";
    case omill::RecoveryRejectionReason::kNotSelfContained:
      return "not_self_contained";
    case omill::RecoveryRejectionReason::kUnsupported:
      return "unsupported";
  }
  return "unsupported";
}

const char *solvedIntegerValueKindName(
    omill::SolvedIntegerValueKind kind) {
  switch (kind) {
    case omill::SolvedIntegerValueKind::kUnknown:
      return "unknown";
    case omill::SolvedIntegerValueKind::kConstant:
      return "constant";
    case omill::SolvedIntegerValueKind::kSet:
      return "set";
  }
  return "unknown";
}

std::string joinHexList(llvm::ArrayRef<uint64_t> values) {
  std::string joined;
  raw_string_ostream os(joined);
  for (size_t i = 0; i < values.size(); ++i) {
    if (i)
      os << ", ";
    os << hexString(values[i]);
  }
  return joined;
}

llvm::json::Array jsonStringArray(
    const std::vector<std::string> &values) {
  llvm::json::Array arr;
  for (const auto &value : values)
    arr.push_back(value);
  return arr;
}

llvm::json::Array jsonSolverStateValueArray(
    const std::vector<omill::SolverStateValueFact> &values) {
  llvm::json::Array arr;
  for (const auto &value : values) {
    llvm::json::Object obj;
    obj["name"] = value.name;
    obj["bit_width"] = static_cast<int64_t>(value.bit_width);
    obj["values"] = jsonPcArray(value.values);
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonSolverEdgeArtifactArray(
    const std::vector<omill::RoundArtifactBundle::SolverEdgeArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["identity"] = artifact.identity;
    obj["owner_function"] = artifact.owner_function;
    obj["site_index"] = static_cast<int64_t>(artifact.site_index);
    if (artifact.site_pc)
      obj["site_pc"] = hexString(*artifact.site_pc);
    if (artifact.target_pc)
      obj["target_pc"] = hexString(*artifact.target_pc);
    obj["kind"] = artifact.kind;
    obj["status"] = artifact.status;
    obj["possible_target_pcs"] = jsonPcArray(artifact.possible_target_pcs);
    if (artifact.branch_taken)
      obj["branch_taken"] = *artifact.branch_taken;
    obj["state_values"] = jsonSolverStateValueArray(artifact.state_values);
    if (artifact.handler_va)
      obj["handler_va"] = hexString(*artifact.handler_va);
    if (artifact.incoming_hash)
      obj["incoming_hash"] = hexString(*artifact.incoming_hash);
    if (artifact.overlay_key)
      obj["overlay_key"] = *artifact.overlay_key;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonRejectedImportArray(
    const std::vector<omill::RejectedImportArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["target_pc"] = hexString(artifact.target_pc);
    obj["reason"] = recoveryRejectionReasonName(artifact.reason);
    obj["detail"] = artifact.detail;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonImportDecisionArray(
    const std::vector<omill::ImportDecisionArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["label"] = artifact.label;
    obj["target_pc"] = hexString(artifact.target_pc);
    obj["eligibility"] = importEligibilityName(artifact.eligibility);
    obj["rejection_reason"] =
        recoveryRejectionReasonName(artifact.rejection_reason);
    if (artifact.selected_root_pc)
      obj["selected_root_pc"] = hexString(*artifact.selected_root_pc);
    if (artifact.import_class)
      obj["import_class"] = omill::toString(*artifact.import_class);
    obj["proof_summary"] = artifact.proof_summary;
    obj["resolution_summary"] = artifact.resolution_summary;
    obj["detail"] = artifact.detail;
    obj["imported"] = artifact.imported;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonCleanupActionArray(
    const std::vector<omill::CleanupActionArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["label"] = artifact.label;
    obj["changed"] = artifact.changed;
    obj["detail"] = artifact.detail;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonPlannedRecoveryActionArray(
    const std::vector<omill::FinalStateRecoveryAction> &actions) {
  llvm::json::Array arr;
  for (const auto &action : actions) {
    llvm::json::Object obj;
    obj["kind"] = omill::toString(action.kind);
    obj["target_pc"] = hexString(action.target_pc);
    obj["source_stage"] = runtimeArtifactStageName(action.source_stage);
    obj["source_label"] = action.source_label;
    obj["final_state_class"] = action.final_state_class;
    obj["reason"] = action.reason;
    obj["retry_budget"] = static_cast<int64_t>(action.retry_budget);
    obj["planned_resolver_path"] = action.planned_resolver_path;
    obj["expected_outcome"] = action.expected_outcome;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonExecutedRecoveryActionArray(
    const std::vector<omill::ExecutedRecoveryActionArtifact> &actions) {
  llvm::json::Array arr;
  for (const auto &action : actions) {
    llvm::json::Object obj;
    obj["kind"] = omill::toString(action.kind);
    obj["target_pc"] = hexString(action.target_pc);
    obj["attempted"] = action.attempted;
    obj["disposition"] = omill::toString(action.disposition);
    obj["detail"] = action.detail;
    obj["module_changed"] = action.module_changed;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonBoundaryRecoveryActionArray(
    const std::vector<omill::BoundaryTailRecoveryAction> &actions) {
  llvm::json::Array arr;
  for (const auto &action : actions) {
    llvm::json::Object obj;
    obj["kind"] = omill::toString(action.kind);
    obj["target_pc"] = hexString(action.target_pc);
    if (action.continuation_pc)
      obj["continuation_pc"] = hexString(*action.continuation_pc);
    obj["source_label"] = action.source_label;
    obj["reason"] = action.reason;
    obj["expected_outcome"] = action.expected_outcome;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Array jsonBoundaryRecoveryResultArray(
    const std::vector<omill::BoundaryTailRecoveryActionResult> &results) {
  llvm::json::Array arr;
  for (const auto &result : results) {
    llvm::json::Object obj;
    obj["kind"] = omill::toString(result.kind);
    obj["target_pc"] = hexString(result.target_pc);
    if (result.continuation_pc)
      obj["continuation_pc"] = hexString(*result.continuation_pc);
    obj["attempted"] = result.attempted;
    obj["disposition"] = omill::toString(result.disposition);
    obj["detail"] = result.detail;
    obj["module_changed"] = result.module_changed;
    arr.push_back(std::move(obj));
  }
  return arr;
}

llvm::json::Object jsonRecoveryQualitySummary(
    const omill::RecoveryQualitySummary &summary) {
  llvm::json::Object obj;
  obj["structurally_closed"] = summary.structurally_closed;
  obj["functionally_recovered"] = summary.functionally_recovered;
  obj["dispatcher_heavy"] = summary.dispatcher_heavy;
  obj["dispatcher_shell"] = summary.dispatcher_shell;
  obj["modeled_intra_owner_continuations"] =
      jsonPcArray(summary.modeled_intra_owner_continuations);
  obj["lifted_intra_owner_continuations"] =
      jsonPcArray(summary.lifted_intra_owner_continuations);
  obj["modeled_pc_relative_return_thunks"] =
      jsonPcArray(summary.modeled_pc_relative_return_thunks);
  obj["modeled_controlled_returns"] =
      jsonPcArray(summary.modeled_controlled_returns);
  obj["controlled_return_unresolved"] =
      jsonPcArray(summary.controlled_return_unresolved);
  obj["lifted_controlled_return_continuations"] =
      jsonPcArray(summary.lifted_controlled_return_continuations);
  obj["terminal_modeled_targets"] =
      jsonPcArray(summary.terminal_modeled_targets);
  obj["terminal_modeled_children"] =
      jsonPcArray(summary.terminal_modeled_children);
  obj["terminal_modeled_boundaries"] =
      jsonPcArray(summary.terminal_modeled_boundaries);
  obj["modeled_reentry_boundaries"] =
      jsonPcArray(summary.modeled_reentry_boundaries);
  obj["lifted_boundary_continuations"] =
      jsonPcArray(summary.lifted_boundary_continuations);
  obj["lowering_helper_callees"] =
      jsonStringArray(summary.lowering_helper_callees);
  obj["accepted_external_leaf_calls"] =
      jsonStringArray(summary.accepted_external_leaf_calls);
  obj["hard_rejected_targets"] =
      jsonPcArray(summary.hard_rejected_targets);
  return obj;
}

std::string runtimeArtifactReportPath(llvm::StringRef output_path) {
  llvm::SmallString<256> report_path(output_path);
  llvm::sys::path::replace_extension(report_path, ".artifacts.txt");
  return std::string(report_path.str());
}

void appendReportLine(raw_ostream &os, llvm::StringRef text,
                             unsigned indent = 0) {
  for (unsigned i = 0; i < indent; ++i)
    os << ' ';
  os << text << '\n';
}

void appendReportStringList(raw_ostream &os, llvm::StringRef label,
                                   const std::vector<std::string> &values,
                                   unsigned indent = 0) {
  if (values.empty())
    return;
  appendReportLine(os, label, indent);
  for (const auto &value : values)
    appendReportLine(os, value, indent + 2);
}

void appendReportPcList(raw_ostream &os, llvm::StringRef label,
                               const std::vector<uint64_t> &values,
                               unsigned indent = 0) {
  if (values.empty())
    return;
  appendReportLine(os, label, indent);
  for (uint64_t value : values)
    appendReportLine(os, hexString(value), indent + 2);
}

void appendReportPcListWithEmpty(raw_ostream &os, llvm::StringRef label,
                                        const std::vector<uint64_t> &values,
                                        unsigned indent = 0) {
  appendReportLine(os, label, indent);
  if (values.empty()) {
    appendReportLine(os, "<none>", indent + 2);
    return;
  }
  for (uint64_t value : values)
    appendReportLine(os, hexString(value), indent + 2);
}

void appendReportSolverEdges(
    raw_ostream &os, llvm::StringRef label,
    const std::vector<omill::RoundArtifactBundle::SolverEdgeArtifact> &artifacts,
    unsigned indent = 0) {
  if (artifacts.empty())
    return;

  appendReportLine(os, label, indent);
  for (const auto &artifact : artifacts) {
    appendReportLine(
        os, (llvm::Twine("edge=") + artifact.identity +
             " owner=" + artifact.owner_function +
             " site_index=" + llvm::Twine(artifact.site_index) +
             (artifact.site_pc ? " site_pc=" + hexString(*artifact.site_pc) : "") +
             (artifact.target_pc ? " target=" + hexString(*artifact.target_pc) : "") +
             " kind=" + artifact.kind +
             " status=" + artifact.status).str(),
        indent + 2);
    if (!artifact.possible_target_pcs.empty()) {
      appendReportLine(
          os, (llvm::Twine("possible_targets=") +
               joinHexList(artifact.possible_target_pcs)).str(),
          indent + 4);
    }
    if (artifact.branch_taken) {
      appendReportLine(
          os, (llvm::Twine("branch_taken=") +
               (*artifact.branch_taken ? "true" : "false")).str(),
          indent + 4);
    }
    if (artifact.handler_va || artifact.incoming_hash || artifact.overlay_key) {
      appendReportLine(
          os, (llvm::Twine("overlay handler=") +
               (artifact.handler_va ? hexString(*artifact.handler_va) : "<none>") +
               " incoming_hash=" +
               (artifact.incoming_hash ? hexString(*artifact.incoming_hash)
                                       : "<none>") +
               " key=" +
               (artifact.overlay_key ? *artifact.overlay_key : "<none>")).str(),
          indent + 4);
    }
    for (const auto &state_value : artifact.state_values) {
      appendReportLine(
          os, (llvm::Twine("state ") + state_value.name +
               " bits=" + llvm::Twine(state_value.bit_width) +
               " values=[" + joinHexList(state_value.values) + "]").str(),
          indent + 4);
    }
  }
}

void appendUniqueStringValue(std::vector<std::string> &dst,
                                    llvm::StringRef value) {
  if (value.empty())
    return;
  const auto value_str = value.str();
  if (llvm::find(dst, value_str) == dst.end())
    dst.push_back(value_str);
}

void appendUniquePcValue(std::vector<uint64_t> &dst, uint64_t value) {
  if (!value)
    return;
  if (llvm::find(dst, value) == dst.end())
    dst.push_back(value);
}

}  // namespace

llvm::json::Object jsonSolvedIntegerValue(
    const omill::SolvedIntegerValue &value) {
  llvm::json::Object obj;
  obj["kind"] = solvedIntegerValueKindName(value.kind);
  obj["bit_width"] = static_cast<int64_t>(value.bit_width);
  obj["values"] = jsonPcArray(value.values);
  return obj;
}

void emitRuntimeArtifactBundleEvents(
    LiftEventLogger &events, llvm::StringRef source,
    const std::vector<omill::RoundArtifactBundle> &bundles) {
  if (!events.enabled() || !events.detailed())
    return;
  for (const auto &bundle : bundles) {
    llvm::json::Object payload;
    payload["source"] = source.str();
    payload["stage"] = runtimeArtifactStageName(bundle.stage);
    payload["label"] = bundle.label;
    if (bundle.round)
      payload["round"] = static_cast<int64_t>(*bundle.round);
    payload["module_fingerprint"] = hexString(bundle.module_fingerprint);
    payload["changed"] = bundle.changed;
    payload["output_root_names"] = jsonStringArray(bundle.output_root_names);
    payload["executable_placeholder_targets"] =
        jsonPcArray(bundle.executable_placeholder_targets);
    payload["native_boundary_targets"] =
        jsonPcArray(bundle.native_boundary_targets);
    payload["remill_runtime_callees"] =
        jsonStringArray(bundle.remill_runtime_callees);
    payload["external_callees"] = jsonStringArray(bundle.external_callees);
    payload["lowering_helper_callees"] =
        jsonStringArray(bundle.lowering_helper_callees);
    payload["imported_targets"] = jsonPcArray(bundle.imported_targets);
    payload["rejected_imports"] =
        jsonRejectedImportArray(bundle.rejected_imports);
    payload["import_decisions"] =
        jsonImportDecisionArray(bundle.import_decisions);
    payload["cleanup_actions"] =
        jsonCleanupActionArray(bundle.cleanup_actions);
    payload["planned_recovery_actions"] =
        jsonPlannedRecoveryActionArray(bundle.planned_recovery_actions);
    payload["executed_recovery_actions"] =
        jsonExecutedRecoveryActionArray(bundle.executed_recovery_actions);
      payload["boundary_recovery_actions"] =
          jsonBoundaryRecoveryActionArray(bundle.boundary_recovery_actions);
      payload["boundary_recovery_results"] =
          jsonBoundaryRecoveryResultArray(bundle.boundary_recovery_results);
      payload["solver_edges"] = jsonSolverEdgeArtifactArray(bundle.solver_edges);
      payload["recovery_quality"] =
          jsonRecoveryQualitySummary(bundle.recovery_quality);
      payload["notes"] = jsonStringArray(bundle.notes);
    events.emitInfo("runtime_artifact_bundle", "runtime artifact bundle",
                    std::move(payload));
  }
}


void emitIterativeSessionReport(
    const std::shared_ptr<omill::IterativeLiftingSession> &session) {
  if (!session || !wantIterativeSessionReport())
    return;

  errs() << "Iterative session report [" << session->name() << "]\n";
  errs() << "  nodes=" << session->graph().nodeCount()
         << " edges=" << session->graph().edgeCount()
         << " unresolved_edges=" << session->graph().unresolvedEdgeCount()
         << " dirty_nodes=" << session->graph().dirtyNodes().size() << "\n";

  for (const auto &round : session->roundSummaries()) {
    errs() << "  round[" << round.pipeline << "#" << round.iteration << "] "
           << "dirty=" << round.dirty_functions
           << "->" << round.dirty_functions_after
           << " affected=" << round.affected_functions
           << " optimized=" << round.optimized_functions
           << " unresolved=" << round.unresolved_before << "->"
           << round.unresolved_after
           << " new_targets=" << round.new_targets
           << " pending=" << round.pending_targets
           << " total=" << round.total_ms << "ms"
           << " opt=" << round.optimize_ms << "ms"
           << " resolve=" << round.resolve_ms << "ms"
           << " ipcp=" << round.ipcp_ms << "ms"
           << " lift=" << round.lift_ms << "ms"
           << " lower=" << round.lower_ms << "ms"
           << " inline=" << round.inline_ms << "ms"
           << " reverse_inline=" << round.reverse_inline_ms << "ms"
           << " ipcp=" << (round.ipcp_changed ? "yes" : "no")
           << " lifted=" << (round.lifted_new ? "yes" : "no");
    if (round.stalled) {
      errs() << " stalled(dynamic=" << round.dynamic_unresolved
             << ", missing=" << round.missing_targets
             << ", blocked=" << round.blocked_unresolved << ")";
    }
    errs() << "\n";
  }

  auto unresolved = session->graph().unresolvedEdges();
  if (!unresolved.empty()) {
    errs() << "  unresolved edges:\n";
    for (const auto *edge : unresolved) {
      errs() << "    0x" << Twine::utohexstr(edge->source_pc) << " -> ";
      if (edge->target_pc != 0)
        errs() << "0x" << Twine::utohexstr(edge->target_pc);
      else
        errs() << "<dynamic>";
      errs() << " [" << edgeKindName(edge->kind) << "]\n";
    }
  }
}


bool LiftEventLogger::init(llvm::StringRef sink_path,
                           llvm::StringRef detail_text,
                           llvm::StringRef input_file) {
  if (sink_path.empty()) {
    enabled_ = false;
    return true;
  }
  auto parsed = parseEventDetailLevel(detail_text);
  if (!parsed) {
    errs() << "Invalid --event-detail: " << detail_text
           << " (expected basic|detailed)\n";
    return false;
  }
  detail_ = *parsed;
  enabled_ = true;
  run_id_ = buildRunId(input_file);

  if (sink_path == "-") {
    os_ = &outs();
    return true;
  }

  std::error_code ec;
  file_ = std::make_unique<raw_fd_ostream>(sink_path, ec, sys::fs::OF_Text);
  if (ec) {
    errs() << "Error opening --event-jsonl output '" << sink_path
           << "': " << ec.message() << "\n";
    return false;
  }
  os_ = file_.get();
  return true;
}

void LiftEventLogger::emit(llvm::StringRef kind, llvm::StringRef severity,
                           llvm::StringRef message,
                           llvm::json::Object payload) {
  if (!enabled_ || !os_)
    return;
  LiftRunEvent event;
  event.run_id = run_id_;
  event.seq = ++seq_;
  event.timestamp_ms = nowMs();
  event.kind = kind.str();
  event.severity = severity.str();
  event.message = message.str();
  event.payload = std::move(payload);
  *os_ << llvm::json::Value(toJSON(event)) << "\n";
  os_->flush();
}

void LiftEventLogger::emitInfo(llvm::StringRef kind, llvm::StringRef message,
                               llvm::json::Object payload) {
  emit(kind, "info", message, std::move(payload));
}
void LiftEventLogger::emitInfo(llvm::StringRef kind, llvm::StringRef message,
                               std::initializer_list<EventKV> payload) {
  emit(kind, "info", message, llvm::json::Object(payload));
}

void LiftEventLogger::emitWarn(llvm::StringRef kind, llvm::StringRef message,
                               llvm::json::Object payload) {
  emit(kind, "warning", message, std::move(payload));
}
void LiftEventLogger::emitWarn(llvm::StringRef kind, llvm::StringRef message,
                               std::initializer_list<EventKV> payload) {
  emit(kind, "warning", message, llvm::json::Object(payload));
}

void LiftEventLogger::emitError(llvm::StringRef kind, llvm::StringRef message,
                                llvm::json::Object payload) {
  emit(kind, "error", message, std::move(payload));
}
void LiftEventLogger::emitError(llvm::StringRef kind, llvm::StringRef message,
                                std::initializer_list<EventKV> payload) {
  emit(kind, "error", message, llvm::json::Object(payload));
}

void LiftEventLogger::emitTerminalSuccess(llvm::StringRef output_file) {
  llvm::json::Object payload;
  payload["status"] = "success";
  payload["output_file"] = output_file;
  emitInfo("run_done", "completed", std::move(payload));
}

void LiftEventLogger::emitTerminalFailure(int exit_code, llvm::StringRef reason) {
  llvm::json::Object payload;
  payload["status"] = "failed";
  payload["exit_code"] = exit_code;
  payload["reason"] = reason;
  emitError("run_done", "failed", std::move(payload));
}

int64_t LiftEventLogger::nowMs() {
  auto now = std::chrono::system_clock::now().time_since_epoch();
  return std::chrono::duration_cast<std::chrono::milliseconds>(now).count();
}

std::string LiftEventLogger::buildRunId(llvm::StringRef input_file) {
  auto ms = nowMs();
  uint64_t pid = static_cast<uint64_t>(llvm::sys::Process::getProcessId());
  std::string basename = input_file.str();
  size_t slash = basename.find_last_of("/\\");
  if (slash != std::string::npos)
    basename = basename.substr(slash + 1);
  return ("run_" + std::to_string(ms) + "_" + std::to_string(pid) +
          "_" + basename);
}


void emitIterativeSessionEvents(
    LiftEventLogger &events,
    const std::shared_ptr<omill::IterativeLiftingSession> &session,
    llvm::StringRef stage) {
  if (!events.enabled() || !events.detailed() || !session)
    return;

  for (const auto &round : session->roundSummaries()) {
    events.emitInfo(
        "iterative_round", "iterative resolution round",
        {{"stage", stage.str()},
         {"pipeline", round.pipeline},
         {"iteration", static_cast<int64_t>(round.iteration)},
         {"dirty_before", static_cast<int64_t>(round.dirty_functions)},
         {"dirty_after", static_cast<int64_t>(round.dirty_functions_after)},
         {"affected_functions",
          static_cast<int64_t>(round.affected_functions)},
         {"optimized_functions",
          static_cast<int64_t>(round.optimized_functions)},
         {"unresolved_before",
          static_cast<int64_t>(round.unresolved_before)},
         {"unresolved_after", static_cast<int64_t>(round.unresolved_after)},
         {"new_targets", static_cast<int64_t>(round.new_targets)},
         {"pending_targets", static_cast<int64_t>(round.pending_targets)},
         {"dynamic_unresolved",
          static_cast<int64_t>(round.dynamic_unresolved)},
         {"missing_targets", static_cast<int64_t>(round.missing_targets)},
         {"blocked_unresolved", static_cast<int64_t>(round.blocked_unresolved)},
         {"total_ms", static_cast<int64_t>(round.total_ms)},
         {"optimize_ms", static_cast<int64_t>(round.optimize_ms)},
         {"resolve_ms", static_cast<int64_t>(round.resolve_ms)},
         {"ipcp_ms", static_cast<int64_t>(round.ipcp_ms)},
         {"lift_ms", static_cast<int64_t>(round.lift_ms)},
         {"lower_ms", static_cast<int64_t>(round.lower_ms)},
         {"inline_ms", static_cast<int64_t>(round.inline_ms)},
         {"reverse_inline_ms",
          static_cast<int64_t>(round.reverse_inline_ms)},
         {"ipcp_changed", round.ipcp_changed},
         {"lifted_new", round.lifted_new},
         {"stalled", round.stalled}});
  }
}

bool writeRuntimeArtifactReport(
    llvm::StringRef output_path,
    const std::vector<omill::RoundArtifactBundle> &bundles,
    const std::optional<omill::ProtectorValidationReport> &protector_report,
    std::string *written_path) {
  if (output_path.empty() || output_path == "-")
    return false;

  const auto report_path = runtimeArtifactReportPath(output_path);
  std::error_code ec;
  ToolOutputFile out(report_path, ec, sys::fs::OF_Text);
  if (ec)
    return false;

  auto &os = out.os();
  appendReportLine(os, "OMILL Runtime Artifact Report");
  appendReportLine(os, (llvm::Twine("Output: ") + output_path).str());
  appendReportLine(os, (llvm::Twine("Bundles: ") +
                        llvm::Twine(static_cast<uint64_t>(bundles.size())))
                           .str());
  os << '\n';

  if (!bundles.empty()) {
    const auto &final_bundle = bundles.back();
    std::vector<uint64_t> imported_targets;
    std::vector<std::string> final_rejections;
    for (const auto &bundle : bundles) {
      for (uint64_t target : bundle.imported_targets)
        appendUniquePcValue(imported_targets, target);
    }
    for (const auto &decision : final_bundle.import_decisions) {
      if (decision.imported ||
          decision.eligibility == omill::ImportEligibility::kImportable) {
        continue;
      }
      std::string line =
          (llvm::Twine("target=") + hexString(decision.target_pc) +
           " eligibility=" + importEligibilityName(decision.eligibility) +
           " reason=" +
           recoveryRejectionReasonName(decision.rejection_reason) +
           (decision.detail.empty() ? "" : " detail=" + decision.detail))
              .str();
      appendUniqueStringValue(final_rejections, line);
    }
    for (const auto &rejected : final_bundle.rejected_imports) {
      std::string line =
          (llvm::Twine("target=") + hexString(rejected.target_pc) +
           " reason=" + recoveryRejectionReasonName(rejected.reason) +
           (rejected.detail.empty() ? "" : " detail=" + rejected.detail))
              .str();
      appendUniqueStringValue(final_rejections, line);
    }

    appendReportLine(os, "Final State");
    appendReportLine(
        os, (llvm::Twine("  Latest Bundle: ") + final_bundle.label).str());
    appendReportLine(
        os, (llvm::Twine("  Latest Stage: ") +
             runtimeArtifactStageName(final_bundle.stage))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Final Fingerprint: ") +
             hexString(final_bundle.module_fingerprint))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Final Changed: ") +
             (final_bundle.changed ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Structurally Closed: ") +
             (final_bundle.recovery_quality.structurally_closed ? "true"
                                                                : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Functionally Recovered: ") +
             (final_bundle.recovery_quality.functionally_recovered ? "true"
                                                                   : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Dispatcher Heavy: ") +
             (final_bundle.recovery_quality.dispatcher_heavy ? "true"
                                                             : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Dispatcher Shell: ") +
             (final_bundle.recovery_quality.dispatcher_shell ? "true"
                                                             : "false"))
                .str());
    appendReportStringList(os, "  Final Output Roots:",
                           final_bundle.output_root_names);
    appendReportPcList(os, "  Final Executable Placeholders:",
                       final_bundle.executable_placeholder_targets, 2);
    appendReportPcList(os, "  Final Native Boundaries:",
                       final_bundle.native_boundary_targets, 2);
    appendReportStringList(os, "  Final External Callees:",
                           final_bundle.external_callees, 2);
    appendReportStringList(os, "  Final Remill Runtime Callees:",
                           final_bundle.remill_runtime_callees, 2);
    appendReportLine(
        os, (llvm::Twine("  Solver Edge Count: ") +
             llvm::Twine(static_cast<uint64_t>(final_bundle.solver_edges.size())))
                .str());
    appendReportSolverEdges(os, "  Solver Edges:", final_bundle.solver_edges, 2);
    appendReportPcList(os, "  Imported Targets Across Rounds:", imported_targets,
                       2);
    appendReportPcListWithEmpty(
        os, "  Modeled Intra-Owner Continuations:",
        final_bundle.recovery_quality.modeled_intra_owner_continuations, 2);
    appendReportPcListWithEmpty(
        os, "  Lifted Intra-Owner Continuations:",
        final_bundle.recovery_quality.lifted_intra_owner_continuations, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled PC-Relative Return Thunks:",
        final_bundle.recovery_quality.modeled_pc_relative_return_thunks, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled Controlled Returns:",
        final_bundle.recovery_quality.modeled_controlled_returns, 2);
    appendReportPcListWithEmpty(
        os, "  Controlled Return Unresolved:",
        final_bundle.recovery_quality.controlled_return_unresolved, 2);
    appendReportPcListWithEmpty(
        os, "  Lifted Controlled Return Continuations:",
        final_bundle.recovery_quality.lifted_controlled_return_continuations,
        2);
    appendReportPcListWithEmpty(
        os, "  Terminal Modeled Imported Targets:",
        final_bundle.recovery_quality.terminal_modeled_children, 2);
    appendReportPcListWithEmpty(
        os, "  Terminal Modeled Boundaries:",
        final_bundle.recovery_quality.terminal_modeled_boundaries, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled Reentry Boundaries:",
        final_bundle.recovery_quality.modeled_reentry_boundaries, 2);
    appendReportPcListWithEmpty(
        os, "  Lifted Boundary Continuations:",
        final_bundle.recovery_quality.lifted_boundary_continuations, 2);
    appendReportStringList(os, "  Lowering Helper Callees:",
                           final_bundle.recovery_quality.lowering_helper_callees,
                           2);
    appendReportStringList(os, "  Accepted External Leaf Calls:",
                           final_bundle.recovery_quality
                               .accepted_external_leaf_calls,
                           2);
    appendReportPcListWithEmpty(
        os, "  Hard Rejected Targets:",
        final_bundle.recovery_quality.hard_rejected_targets, 2);
    appendReportStringList(os, "  Final Rejected Continuations:",
                           final_rejections, 2);
    appendReportLine(os, "  Final State Recovery Plan:");
    if (!final_bundle.planned_recovery_actions.empty()) {
      for (const auto &action : final_bundle.planned_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 (action.reason.empty() ? "" : " reason=" + action.reason))
                    .str());
      }
    } else {
      appendReportLine(os, "    <none>");
    }
    appendReportLine(os, "  Final State Recovery Outcomes:");
    if (!final_bundle.executed_recovery_actions.empty()) {
      for (const auto &action : final_bundle.executed_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " disposition=" + omill::toString(action.disposition) +
                 " attempted=" + (action.attempted ? "true" : "false") +
                 (action.detail.empty() ? "" : " detail=" + action.detail))
                    .str());
      }
    } else {
      appendReportLine(os, "    <none>");
    }
    appendReportLine(os, "  Boundary Tail Recovery Outcomes:");
    if (!final_bundle.boundary_recovery_results.empty()) {
      for (const auto &action : final_bundle.boundary_recovery_results) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " disposition=" + omill::toString(action.disposition) +
                 (action.continuation_pc
                      ? " continuation=" + hexString(*action.continuation_pc)
                      : "") +
                 " attempted=" + (action.attempted ? "true" : "false") +
                 (action.detail.empty() ? "" : " detail=" + action.detail))
                    .str());
      }
    } else {
      appendReportLine(os, "    <none>");
    }
    if (protector_report) {
      appendReportLine(
          os, (llvm::Twine("  Protector Issue Count: ") +
               llvm::Twine(
                   static_cast<uint64_t>(protector_report->issues.size())))
                  .str());
    }
    os << '\n';
  }

  for (size_t i = 0; i < bundles.size(); ++i) {
    const auto &bundle = bundles[i];
    appendReportLine(
        os, (llvm::Twine("Bundle ") + llvm::Twine(i + 1) + ": " + bundle.label)
                .str());
    appendReportLine(
        os, (llvm::Twine("  Stage: ") + runtimeArtifactStageName(bundle.stage))
                .str());
    if (bundle.round) {
      appendReportLine(
          os, (llvm::Twine("  Round: ") + llvm::Twine(*bundle.round)).str());
    }
    appendReportLine(
        os, (llvm::Twine("  Changed: ") + (bundle.changed ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Module Fingerprint: ") +
             hexString(bundle.module_fingerprint))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Structurally Closed: ") +
             (bundle.recovery_quality.structurally_closed ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Functionally Recovered: ") +
             (bundle.recovery_quality.functionally_recovered ? "true"
                                                             : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Dispatcher Heavy: ") +
             (bundle.recovery_quality.dispatcher_heavy ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Dispatcher Shell: ") +
             (bundle.recovery_quality.dispatcher_shell ? "true" : "false"))
                .str());
    appendReportStringList(os, "  Output Roots:", bundle.output_root_names);
    appendReportPcList(os, "  Executable Placeholders:",
                       bundle.executable_placeholder_targets, 2);
    appendReportPcList(os, "  Native Boundaries:", bundle.native_boundary_targets,
                       2);
    appendReportPcListWithEmpty(
        os, "  Modeled Intra-Owner Continuations:",
        bundle.recovery_quality.modeled_intra_owner_continuations, 2);
    appendReportPcListWithEmpty(
        os, "  Lifted Intra-Owner Continuations:",
        bundle.recovery_quality.lifted_intra_owner_continuations, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled PC-Relative Return Thunks:",
        bundle.recovery_quality.modeled_pc_relative_return_thunks, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled Controlled Returns:",
        bundle.recovery_quality.modeled_controlled_returns, 2);
    appendReportPcListWithEmpty(
        os, "  Controlled Return Unresolved:",
        bundle.recovery_quality.controlled_return_unresolved, 2);
    appendReportPcListWithEmpty(
        os, "  Lifted Controlled Return Continuations:",
        bundle.recovery_quality.lifted_controlled_return_continuations, 2);
    appendReportPcListWithEmpty(
        os, "  Terminal Modeled Targets:",
        bundle.recovery_quality.terminal_modeled_children, 2);
    appendReportPcListWithEmpty(
        os, "  Terminal Modeled Boundaries:",
        bundle.recovery_quality.terminal_modeled_boundaries, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled Reentry Boundaries:",
        bundle.recovery_quality.modeled_reentry_boundaries, 2);
    appendReportPcListWithEmpty(
        os, "  Lifted Boundary Continuations:",
        bundle.recovery_quality.lifted_boundary_continuations, 2);
    appendReportStringList(os, "  Lowering Helper Callees:",
                           bundle.recovery_quality.lowering_helper_callees, 2);
    appendReportStringList(os, "  Accepted External Leaf Calls:",
                           bundle.recovery_quality.accepted_external_leaf_calls,
                           2);
    appendReportPcListWithEmpty(
        os, "  Hard Rejected Targets:",
        bundle.recovery_quality.hard_rejected_targets, 2);
    appendReportStringList(os, "  Remill Runtime Callees:",
                           bundle.remill_runtime_callees, 2);
    appendReportStringList(os, "  External Callees:", bundle.external_callees,
                           2);
    appendReportSolverEdges(os, "  Solver Edges:", bundle.solver_edges, 2);
    appendReportPcList(os, "  Imported Targets:", bundle.imported_targets, 2);
    if (!bundle.import_decisions.empty()) {
      appendReportLine(os, "  Import Decisions:");
      for (const auto &decision : bundle.import_decisions) {
        std::string line =
            (llvm::Twine("    ") + decision.label + " target=" +
             hexString(decision.target_pc) +
             " eligibility=" + importEligibilityName(decision.eligibility) +
             " imported=" + (decision.imported ? "true" : "false"))
                .str();
        appendReportLine(os, line);
        if (decision.selected_root_pc) {
          appendReportLine(
              os, (llvm::Twine("      selected_root=") +
                   hexString(*decision.selected_root_pc))
                      .str());
        }
        if (decision.import_class) {
          appendReportLine(
              os, (llvm::Twine("      import_class=") +
                   omill::toString(*decision.import_class))
                      .str());
        }
        if (!decision.proof_summary.empty())
          appendReportLine(
              os, (llvm::Twine("      proof=") + decision.proof_summary).str());
        if (!decision.resolution_summary.empty())
          appendReportLine(
              os,
              (llvm::Twine("      resolution=") + decision.resolution_summary)
                  .str());
        if (!decision.detail.empty()) {
          appendReportLine(
              os, (llvm::Twine("      detail=") + decision.detail).str());
        } else if (decision.rejection_reason !=
                   omill::RecoveryRejectionReason::kNone) {
          appendReportLine(
              os, (llvm::Twine("      rejection_reason=") +
                   recoveryRejectionReasonName(decision.rejection_reason))
                      .str());
        }
      }
    }
    if (!bundle.rejected_imports.empty()) {
      appendReportLine(os, "  Rejected Imports:");
      for (const auto &rejected : bundle.rejected_imports) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(rejected.target_pc) +
                 " reason=" +
                 recoveryRejectionReasonName(rejected.reason) +
                 (rejected.detail.empty() ? "" : " detail=" + rejected.detail))
                    .str());
      }
    }
    if (!bundle.cleanup_actions.empty()) {
      appendReportLine(os, "  Cleanup Actions:");
      for (const auto &cleanup : bundle.cleanup_actions) {
        appendReportLine(
            os, (llvm::Twine("    ") + cleanup.label + " changed=" +
                 (cleanup.changed ? "true" : "false") +
                 (cleanup.detail.empty() ? "" : " detail=" + cleanup.detail))
                    .str());
      }
    }
    if (!bundle.planned_recovery_actions.empty()) {
      appendReportLine(os, "  Final State Recovery Plan:");
      for (const auto &action : bundle.planned_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 " final_state_class=" + action.final_state_class +
                 " retry_budget=" + llvm::Twine(action.retry_budget) +
                 (action.reason.empty() ? "" : " reason=" + action.reason))
                    .str());
        if (!action.planned_resolver_path.empty()) {
          appendReportLine(
              os, (llvm::Twine("      resolver_path=") +
                   action.planned_resolver_path)
                      .str());
        }
        if (!action.expected_outcome.empty()) {
          appendReportLine(
              os, (llvm::Twine("      expected_outcome=") +
                   action.expected_outcome)
                      .str());
        }
      }
    }
    if (!bundle.executed_recovery_actions.empty()) {
      appendReportLine(os, "  Final State Recovery Outcomes:");
      for (const auto &action : bundle.executed_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 " disposition=" + omill::toString(action.disposition) +
                 " attempted=" + (action.attempted ? "true" : "false") +
                 " changed=" + (action.module_changed ? "true" : "false") +
                 (action.detail.empty() ? "" : " detail=" + action.detail))
                    .str());
      }
    }
    if (!bundle.boundary_recovery_actions.empty()) {
      appendReportLine(os, "  Boundary Tail Recovery Plan:");
      for (const auto &action : bundle.boundary_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 (action.continuation_pc
                      ? " continuation=" + hexString(*action.continuation_pc)
                      : "") +
                 (action.reason.empty() ? "" : " reason=" + action.reason))
                    .str());
        if (!action.expected_outcome.empty()) {
          appendReportLine(
              os, (llvm::Twine("      expected_outcome=") +
                   action.expected_outcome)
                      .str());
        }
      }
    }
    if (!bundle.boundary_recovery_results.empty()) {
      appendReportLine(os, "  Boundary Tail Recovery Outcomes:");
      for (const auto &action : bundle.boundary_recovery_results) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 " disposition=" + omill::toString(action.disposition) +
                 (action.continuation_pc
                      ? " continuation=" + hexString(*action.continuation_pc)
                      : "") +
                 " attempted=" + (action.attempted ? "true" : "false") +
                 " changed=" + (action.module_changed ? "true" : "false") +
                 (action.detail.empty() ? "" : " detail=" + action.detail))
                    .str());
      }
    }
    appendReportStringList(os, "  Notes:", bundle.notes, 2);
    os << '\n';
  }

  if (protector_report) {
    appendReportLine(os, "Protector Validation Report");
    appendReportLine(
        os,
        (llvm::Twine("  Issue Count: ") +
         llvm::Twine(static_cast<uint64_t>(protector_report->issues.size())))
            .str());
    if (!protector_report->counts_by_class.empty()) {
      appendReportLine(os, "  Counts By Class:");
      for (const auto &[klass, count] : protector_report->counts_by_class) {
        appendReportLine(
            os, (llvm::Twine("    ") + klass + "=" + llvm::Twine(count)).str());
      }
    }
    if (!protector_report->issues.empty()) {
      appendReportLine(os, "  Issues:");
      for (const auto &issue : protector_report->issues) {
        appendReportLine(
            os, (llvm::Twine("    ") + omill::toString(issue.issue_class) +
                 " " + issue.message)
                    .str());
      }
    }
  }

  out.keep();
  if (written_path)
    *written_path = report_path;
  return true;
}

}  // namespace omill::tools

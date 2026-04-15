#pragma once

#include "omill/Tools/LiftRunContract.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Analysis/RemillStateVariableSolver.h"
#include "omill/Devirtualization/Runtime.h"
#include "omill/Devirtualization/ProtectorModel.h"

#include <llvm/ADT/ArrayRef.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/raw_ostream.h>

#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace omill::tools {

/// JSONL structured event sink for omill-lift run events.
///
/// Call init() once after CLI parsing; then emit*() at each pipeline stage.
/// Events are written as one JSON object per line to a file or stdout.
class LiftEventLogger {
 public:
  using EventKV = llvm::json::Object::KV;

  LiftEventLogger() = default;

  bool init(llvm::StringRef sink_path, llvm::StringRef detail_text,
            llvm::StringRef input_file);

  bool enabled() const { return enabled_; }
  bool detailed() const { return detail_ == EventDetailLevel::kDetailed; }
  llvm::StringRef runId() const { return run_id_; }

  void emit(llvm::StringRef kind, llvm::StringRef severity,
            llvm::StringRef message = "",
            llvm::json::Object payload = {});

  void emitInfo(llvm::StringRef kind, llvm::StringRef message = "",
                llvm::json::Object payload = {});
  void emitInfo(llvm::StringRef kind, llvm::StringRef message,
                std::initializer_list<EventKV> payload);

  void emitWarn(llvm::StringRef kind, llvm::StringRef message = "",
                llvm::json::Object payload = {});
  void emitWarn(llvm::StringRef kind, llvm::StringRef message,
                std::initializer_list<EventKV> payload);

  void emitError(llvm::StringRef kind, llvm::StringRef message = "",
                 llvm::json::Object payload = {});
  void emitError(llvm::StringRef kind, llvm::StringRef message,
                 std::initializer_list<EventKV> payload);

  void emitTerminalSuccess(llvm::StringRef output_file);
  void emitTerminalFailure(int exit_code, llvm::StringRef reason);

 private:
  static int64_t nowMs();
  static std::string buildRunId(llvm::StringRef input_file);

  bool enabled_ = false;
  EventDetailLevel detail_ = EventDetailLevel::kBasic;
  std::string run_id_;
  uint64_t seq_ = 0;
  llvm::raw_ostream *os_ = nullptr;
  std::unique_ptr<llvm::raw_fd_ostream> file_;
};

// ---------------------------------------------------------------------------
// Diagnostic helpers — emit to stderr / events
// ---------------------------------------------------------------------------

/// Emit runtime artifact bundle events to the event logger.
void emitRuntimeArtifactBundleEvents(
    LiftEventLogger &events, llvm::StringRef source,
    const std::vector<RoundArtifactBundle> &bundles);

/// Emit detailed per-round diagnostics for an iterative session to events.
void emitIterativeSessionEvents(
    LiftEventLogger &events,
    const std::shared_ptr<IterativeLiftingSession> &session,
    llvm::StringRef stage);

/// Print a summary of the iterative session to stderr if
/// OMILL_REPORT_ITERATIVE_SESSION is set.
void emitIterativeSessionReport(
    const std::shared_ptr<IterativeLiftingSession> &session);

// ---------------------------------------------------------------------------
// JSON serialization helpers (used in main pipeline stages)
// ---------------------------------------------------------------------------

/// Return "0xHEX" string for a 64-bit address.
std::string hexString(uint64_t value);

/// Build a JSON array of hex strings from a list of PCs.
llvm::json::Array jsonPcArray(llvm::ArrayRef<uint64_t> values);

/// Serialize a SolvedIntegerValue to a JSON object.
llvm::json::Object jsonSolvedIntegerValue(const SolvedIntegerValue &value);

/// Human-readable name for a RemillControlTransferKind.
const char *controlTransferKindName(RemillControlTransferKind kind);

// ---------------------------------------------------------------------------
// Artifact report writer
// ---------------------------------------------------------------------------

/// Write a human-readable .artifacts.txt report alongside the output file.
/// Returns false if output_path is empty or "-".  Optionally writes the
/// report path to *written_path.
bool writeRuntimeArtifactReport(
    llvm::StringRef output_path,
    const std::vector<RoundArtifactBundle> &bundles,
    const std::optional<ProtectorValidationReport> &protector_report,
    std::string *written_path = nullptr);

}  // namespace omill::tools

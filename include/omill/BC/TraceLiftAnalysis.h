#pragma once

#include <llvm/IR/PassManager.h>

#include <functional>

namespace omill {

/// Callback type that lifts a trace (function) at a given PC.
/// Returns true if the trace was successfully lifted (or already existed).
/// This is the interface between IterativeTargetResolutionPass and the
/// actual TraceLifter.
using TraceLiftCallback = std::function<bool(uint64_t pc)>;

/// Module-level analysis that provides a trace-lifting callback.
///
/// The consumer (e.g. omill-lift main.cpp) registers this analysis with
/// a callback that wraps TraceLifter::Lift.  If not registered,
/// IterativeTargetResolutionPass cannot lift new functions from resolved
/// dispatch targets and will only resolve to existing lifted functions.
///
/// This decouples the pass from remill: the pass itself is pure LLVM IR
/// manipulation; only the callback touches remill.
class TraceLiftAnalysis
    : public llvm::AnalysisInfoMixin<TraceLiftAnalysis> {
  friend llvm::AnalysisInfoMixin<TraceLiftAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  struct Result {
    TraceLiftCallback lift_trace;

    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      return false;
    }
  };

  TraceLiftAnalysis() = default;

  explicit TraceLiftAnalysis(TraceLiftCallback cb)
      : callback_(std::move(cb)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    return {callback_};
  }

 private:
  TraceLiftCallback callback_;
};

}  // namespace omill

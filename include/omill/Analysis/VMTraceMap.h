#pragma once

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

namespace llvm {
class Module;
}  // namespace llvm

namespace omill {

class VMTraceEmulator;

/// Trace record keyed by (handler VA, incoming hash). This preserves the
/// concrete per-op exit selected inside merged handlers, which is required for
/// handler demerging and trampoline-aware follow-up analysis.
struct VMTraceRecord {
  uint64_t handler_va = 0;
  uint64_t incoming_hash = 0;
  uint64_t outgoing_hash = 0;
  uint64_t exit_target_va = 0;
  uint64_t native_target_va = 0;
  llvm::SmallVector<uint64_t, 2> successors;
  bool passed_vmexit = false;
  bool is_vmexit = false;
  bool is_error = false;
};

/// Result of following a single concrete hash-threaded path through the
/// trace records.
enum class VMFlatTraceStopReason {
  MissingRecord,
  AmbiguousSuccessor,
  VmExit,
  Error,
  LoopDetected,
  StepLimit,
};

struct VMFlatTraceResult {
  std::vector<VMTraceRecord> records;
  VMFlatTraceStopReason stop_reason = VMFlatTraceStopReason::MissingRecord;
  uint64_t stop_handler_va = 0;
  uint64_t stop_hash = 0;

  bool completed() const { return stop_reason == VMFlatTraceStopReason::VmExit; }
};

/// Immutable handler-to-successor map produced from concrete richardvm traces.
///
/// The previous implementation mixed byte-pattern graph recovery with emulator
/// results. The new hash-dispatch architecture is trace-first: this map stores
/// both aggregate handler successors and per-(handler,incoming_hash) trace
/// records proven by the emulator for concrete wrapper/hash executions.
class VMTraceMap {
 public:
  VMTraceMap() = default;
  VMTraceMap(uint64_t vmenter_va, uint64_t vmexit_va)
      : vmenter_va_(vmenter_va), vmexit_va_(vmexit_va) {}

  const std::vector<uint64_t> &handlerEntries() const {
    return handler_entries_;
  }
  uint64_t entryHandlerVA() const { return entry_handler_va_; }

  uint64_t vmenterVA() const { return vmenter_va_; }
  uint64_t vmexitVA() const { return vmexit_va_; }

  bool isVMHandler(uint64_t va) const { return handler_set_.count(va); }
  bool empty() const { return handler_entries_.empty(); }

  /// Record the flat successors observed for one traced handler.
  void recordTraceTargets(uint64_t handler_va,
                          llvm::ArrayRef<uint64_t> successors);

  /// Record one concrete trace keyed by (handler_va, incoming_hash).
  void recordTrace(VMTraceRecord trace);

  /// Merge all entries emitted by the emulator's last trace run.
  void mergeTraceResults(const VMTraceEmulator &trace);

  /// Aggregate successor targets for a handler across all known trace records.
  llvm::SmallVector<uint64_t, 2> getTraceTargets(uint64_t handler_va) const;

  /// Exact trace record for a handler under a specific incoming hash.
  std::optional<VMTraceRecord> getTraceForHash(uint64_t handler_va,
                                               uint64_t incoming_hash) const;

  /// All concrete trace records seen for a handler.
  llvm::ArrayRef<VMTraceRecord> getTraceRecords(uint64_t handler_va) const;

  /// Follow one concrete flat path using exact (handler, incoming_hash) trace
  /// records until vmexit, ambiguity, missing data, loop, or step limit.
  VMFlatTraceResult followFlatTrace(uint64_t handler_va, uint64_t incoming_hash,
                                    unsigned max_steps = 4096) const;

  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  void noteHandler(uint64_t va);
  void sortHandlers();
  void rebuildAggregateTargets(uint64_t handler_va);

  uint64_t vmenter_va_ = 0;
  uint64_t vmexit_va_ = 0;
  uint64_t entry_handler_va_ = 0;

  std::vector<uint64_t> handler_entries_;
  llvm::DenseSet<uint64_t> handler_set_;
  llvm::DenseMap<uint64_t, llvm::SmallVector<uint64_t, 2>> trace_targets_;
  llvm::DenseMap<uint64_t, std::vector<VMTraceRecord>> trace_records_;
};

/// Module-level analysis providing the emulator-derived trace map.
class VMTraceMapAnalysis
    : public llvm::AnalysisInfoMixin<VMTraceMapAnalysis> {
  friend llvm::AnalysisInfoMixin<VMTraceMapAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = VMTraceMap;

  VMTraceMapAnalysis() = default;
  explicit VMTraceMapAnalysis(VMTraceMap trace_map)
      : trace_map_(std::move(trace_map)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);

 private:
  VMTraceMap trace_map_;
};

}  // namespace omill

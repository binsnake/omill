#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>

#include <cstdint>
#include <cstring>
#include <optional>
#include <vector>

namespace omill {

/// Snapshot of emulator state at a vmexit native call point.
/// Captures GPR values and vmcontext memory so per-callsite clones
/// can be specialized with emulator-derived constants.
struct NativeCallInfo {
  uint64_t handler_va = 0;   ///< Handler that triggered vmexit.
  uint64_t target_va = 0;    ///< Native function VA being called.
  uint64_t hash = 0;         ///< Hash from vmcontext at [R12+0x190].
  uint64_t gprs[16] = {};    ///< GPR snapshot (indexed by x86 encoding order:
                              ///< RAX=0, RCX=1, RDX=2, RBX=3, RSP=4, RBP=5,
                              ///< RSI=6, RDI=7, R8..R15=8..15).
  uint64_t r12_base = 0;     ///< Vmcontext base pointer (R12 value).
  std::vector<uint8_t> vmcontext_snapshot; ///< Memory at [R12..R12+0x200].
};

class BinaryMemoryMap;

/// Concrete x86-64 emulator for the EasyAntiCheat hash-dispatch VM.
///
/// The architecture is flat and trace-driven: a wrapper seeds [r12+0x190] with
/// an incoming hash, dispatches into a merged handler body, and the handler's
/// MBA-obfuscated hash selection deterministically chooses one outgoing path for
/// that specific hash. This emulator follows that concrete path and records the
/// resulting handler-to-handler trace without relying on IR hash elimination or
/// byte-pattern graph recovery.
class VMTraceEmulator {
 public:
  /// One concrete handler step in a flat trace.
  struct TraceEntry {
    uint64_t handler_va = 0;
    uint64_t incoming_hash = 0;
    uint64_t outgoing_hash = 0;
    uint64_t exit_target_va = 0;
    uint64_t native_target_va = 0;

    /// Resolved successor handler VAs (normally one, occasionally two when the
    /// traced exit fans out into a trampoline-driven continuation).
    llvm::SmallVector<uint64_t, 2> successors;

    /// True if execution passed through the vmexit trampoline while producing
    /// this entry's final outcome (native call, terminal exit, or re-entry).
    bool passed_vmexit = false;

    /// True if this handler exits the VM without a traced successor handler.
    bool is_vmexit = false;

    /// True if the emulator hit an unsupported instruction or unresolved exit.
    bool is_error = false;
  };

  /// \param mem        Binary memory map with all loaded sections.
  /// \param image_base PE image base address.
  /// \param vmenter_va VA of the VM entry function (context save).
  /// \param vmexit_va  VA of the VM exit function (context restore).
  VMTraceEmulator(const BinaryMemoryMap &mem, uint64_t image_base,
                  uint64_t vmenter_va, uint64_t vmexit_va);

  /// Trace starting from a VM entry wrapper function.
  ///
  /// The wrapper is expected to seed the hash and dispatch through the
  /// hash-dispatch preamble described in VM_ARCHITECTURE.md.
  std::vector<TraceEntry> traceFromWrapper(uint64_t wrapper_va);

  /// Trace from a wrapper with caller-provided vmcontext contents.
  /// The snapshot is copied into synthetic memory at syntheticVMContextBase().
  std::vector<TraceEntry> traceFromWrapperWithSnapshot(
      uint64_t wrapper_va, const std::vector<uint8_t> &vmcontext_snapshot);

  /// Trace from a wrapper with caller-provided vmcontext contents while
  /// overriding the initial hash accumulator value.
  std::vector<TraceEntry> traceFromWrapperWithSnapshotAndHash(
      uint64_t wrapper_va, const std::vector<uint8_t> &vmcontext_snapshot,
      uint64_t initial_hash);

  /// Trace from a known handler VA with an explicit initial vmcontext state
  /// (delta and hash already known).
  std::vector<TraceEntry> traceFromHandler(uint64_t handler_va, uint64_t delta,
                                           uint64_t initial_hash);

  /// Trace from a known handler using caller-provided vmcontext contents while
  /// overriding the initial hash accumulator value.
  std::vector<TraceEntry> traceFromHandlerWithSnapshot(
      uint64_t handler_va, uint64_t delta, uint64_t initial_hash,
      const std::vector<uint8_t> &vmcontext_snapshot);

  /// All unique handler VAs discovered across all trace calls.
  const std::vector<uint64_t> &discoveredHandlers() const {
    return discovered_handlers_;
  }

  /// Entries from the last traceFromWrapper/traceFromHandler call.
  /// Includes the wrapper -> first handler mapping when tracing from a wrapper.
  const std::vector<TraceEntry> &traceEntries() const {
    return last_trace_results_;
  }

  uint64_t lastDelta() const { return last_delta_; }

  /// Native function VAs called through the vmexit -> call [rsp+8] -> vmentry
  /// trampoline pattern.
  const std::vector<uint64_t> &nativeCallTargets() const {
    return native_call_targets_;
  }

  /// Per-callsite native call info with emulator state snapshots.
  /// Ordered by encounter during tracing (NOT deduplicated by target VA).
  const std::vector<NativeCallInfo> &nativeCallInfos() const {
    return native_call_infos_;
  }

  /// Set maximum number of handlers to trace before giving up.
  void setMaxHandlers(unsigned max) { max_handlers_ = max; }

  /// Set maximum emulation steps per handler.
  void setMaxStepsPerHandler(unsigned max) { max_steps_per_handler_ = max; }

  /// VA range for the VM handler segment (seg006 in EAC).
  void setHandlerSegmentRange(uint64_t start, uint64_t end) {
    handler_seg_start_ = start;
    handler_seg_end_ = end;
  }

  /// Synthetic vmcontext base address used by the concrete emulator.
  static uint64_t syntheticVMContextBase();

 private:
  /// Parse a VM entry wrapper to extract initial state.
  struct WrapperInfo {
    uint64_t delta = 0;           ///< base_delta from the vmenter helper.
    uint64_t initial_hash = 0;    ///< Constant stored to [r12+0x190].
    uint64_t first_handler_va = 0;///< First handler VA after thunk following.
    std::vector<uint8_t> vmcontext_snapshot; ///< Wrapper-seeded vmctx bytes.
    bool valid = false;
  };

  WrapperInfo parseEntryWrapper(
      uint64_t wrapper_va,
      const std::vector<uint8_t> *initial_vmcontext_snapshot = nullptr);

  std::vector<TraceEntry> traceFromHandlerImpl(
      uint64_t handler_va, uint64_t delta, uint64_t initial_hash,
      const std::vector<uint8_t> *vmcontext_snapshot);

  /// Compute the base_delta value from the vmentry helper sub-function.
  std::optional<uint64_t> computeDelta(uint64_t subfunc_va,
                                       uint64_t return_addr);

  /// Check whether a VA matches the vmexit function (user-specified or
  /// auto-detected from the delta-computer scan).
  bool isVmexitVa(uint64_t va) const;

  const BinaryMemoryMap &mem_;
  uint64_t image_base_;
  uint64_t vmenter_va_;
  uint64_t vmexit_va_;
  uint64_t true_vmexit_va_ = 0;  ///< Auto-detected vmexit (past delta helper).

  uint64_t handler_seg_start_ = 0;
  uint64_t handler_seg_end_ = UINT64_MAX;

  unsigned max_handlers_ = 10000;
  unsigned max_steps_per_handler_ = 5000;

  std::vector<uint64_t> discovered_handlers_;
  llvm::DenseSet<uint64_t> discovered_set_;

  /// Native call targets discovered via vmexit -> call -> vmentry.
  std::vector<uint64_t> native_call_targets_;
  llvm::DenseSet<uint64_t> native_call_set_;

  /// Per-callsite native call info (ordered, not deduplicated).
  std::vector<NativeCallInfo> native_call_infos_;

  /// Stored results from the last trace call (for VMTraceMap).
  std::vector<TraceEntry> last_trace_results_;

  /// Delta value from the last parseEntryWrapper call.
  uint64_t last_delta_ = 0;
};

}  // namespace omill
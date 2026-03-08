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

/// Concrete x86-64 emulator that walks VM handler chains to resolve dispatch
/// targets statically.
///
/// EAC-style VMs use hash-threaded dispatch: each handler computes the next
/// handler's address through complex arithmetic on a hash accumulator
/// ([r12+0x190]), RVA constants, and an image base delta ([r12+0xE0]).  The
/// hash accumulator is initialized by the entry wrapper and updated
/// deterministically by each handler, making the entire chain statically
/// solvable via concrete execution.
///
/// The solver embeds a lightweight x86-64 emulator that handles the ~20
/// instruction forms used in VM handlers (integer arithmetic, comparisons,
/// conditional sets, memory load/store to vmcontext/stack).
class VMHandlerChainSolver {
 public:
  /// A single resolved handler in the chain.
  struct ChainEntry {
    uint64_t handler_va = 0;

    /// Resolved successor handler VAs (1 for linear, 2 for conditional).
    llvm::SmallVector<uint64_t, 2> successors;

    /// True if this handler dispatches to the VM exit function.
    bool is_vmexit = false;

    /// True if the emulator hit an error (unhandled instruction, etc.).
    bool is_error = false;
  };

  /// \param mem        Binary memory map with all loaded sections.
  /// \param image_base PE image base address.
  /// \param vmenter_va VA of the VM entry function (context save).
  /// \param vmexit_va  VA of the VM exit function (context restore).
  VMHandlerChainSolver(const BinaryMemoryMap &mem, uint64_t image_base,
                       uint64_t vmenter_va, uint64_t vmexit_va);

  /// Solve the handler chain starting from a VM entry wrapper function.
  ///
  /// The wrapper is expected to have the structure:
  ///   lea rsp, [rsp-N]
  ///   call <vmentry>
  ///   <jmp to handler preamble>
  ///   mov rax, <hash_constant>
  ///   mov [r12+0x190], rax
  ///   mov eax, <first_rva>
  ///   add rax, [r12+0xE0]
  ///   jmp rax
  ///
  /// Returns the list of all discovered handlers in BFS order.
  std::vector<ChainEntry> solveFromWrapper(uint64_t wrapper_va);

  /// Solve starting from a wrapper with caller-provided vmcontext contents.
  /// The snapshot is copied into synthetic memory at syntheticVMContextBase().
  std::vector<ChainEntry> solveFromWrapperWithSnapshot(
      uint64_t wrapper_va, const std::vector<uint8_t> &vmcontext_snapshot);

  /// Solve from a wrapper with caller-provided vmcontext contents while
  /// overriding the initial hash accumulator value.
  std::vector<ChainEntry> solveFromWrapperWithSnapshotAndHash(
      uint64_t wrapper_va, const std::vector<uint8_t> &vmcontext_snapshot,
      uint64_t initial_hash);

  /// Solve starting from a known handler VA with an explicit initial
  /// vmcontext state (delta and hash already known).
  std::vector<ChainEntry> solveFromHandler(uint64_t handler_va,
                                           uint64_t delta,
                                           uint64_t initial_hash);

  /// Solve from a known handler using caller-provided vmcontext contents
  /// while overriding the initial hash accumulator value.
  std::vector<ChainEntry> solveFromHandlerWithSnapshot(
      uint64_t handler_va, uint64_t delta, uint64_t initial_hash,
      const std::vector<uint8_t> &vmcontext_snapshot);

  /// All unique handler VAs discovered across all solve calls.
  const std::vector<uint64_t> &discoveredHandlers() const {
    return discovered_handlers_;
  }

  /// Chain entries from the last solveFromWrapper/solveFromHandler call.
  /// Includes the wrapper→first_handler entry when called via
  /// solveFromWrapper.
  const std::vector<ChainEntry> &chainEntries() const {
    return last_chain_results_;
  }

  /// Native function VAs called through the vmexit→call→vmentry pattern.
  /// Discovered during chain solving — these are functions the VM handlers
  /// call through temporary VM exit, not VM handlers themselves.
  uint64_t lastDelta() const { return last_delta_; }

  const std::vector<uint64_t> &nativeCallTargets() const {
    return native_call_targets_;
  }

  /// Per-callsite native call info with emulator state snapshots.
  /// Ordered by encounter during BFS (NOT deduplicated by target VA).
  const std::vector<NativeCallInfo> &nativeCallInfos() const {
    return native_call_infos_;
  }

  /// Set maximum number of handlers to solve before giving up.
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
    uint64_t delta = 0;           ///< Image base delta from vmentry sub-func.
    uint64_t initial_hash = 0;    ///< Constant stored to [r12+0x190].
    uint64_t first_handler_va = 0;///< First handler's VA.
    std::vector<uint8_t> vmcontext_snapshot; ///< Wrapper-seeded vmctx bytes.
    bool valid = false;
  };

  WrapperInfo parseEntryWrapper(
      uint64_t wrapper_va,
      const std::vector<uint8_t> *initial_vmcontext_snapshot = nullptr);

  std::vector<ChainEntry> solveFromHandlerImpl(
      uint64_t handler_va, uint64_t delta, uint64_t initial_hash,
      const std::vector<uint8_t> *vmcontext_snapshot);

  /// Compute the delta value from the vmentry sub-function.
  /// The sub-function pattern: push rax; push rbx; mov rax, <const>;
  /// mov rbx, [rsp+10h]; lea rbx, [rbx+rax]; store; pop; pop; ret
  std::optional<uint64_t> computeDelta(uint64_t subfunc_va,
                                       uint64_t return_addr);

  /// Check whether a VA matches the vmexit function (user-specified or
  /// auto-detected from the delta-computer scan).
  bool isVmexitVa(uint64_t va) const;

  const BinaryMemoryMap &mem_;
  uint64_t image_base_;
  uint64_t vmenter_va_;
  uint64_t vmexit_va_;
  uint64_t true_vmexit_va_ = 0;  ///< Auto-detected vmexit (past delta computer).

  uint64_t handler_seg_start_ = 0;
  uint64_t handler_seg_end_ = UINT64_MAX;

  unsigned max_handlers_ = 10000;
  unsigned max_steps_per_handler_ = 5000;

  std::vector<uint64_t> discovered_handlers_;
  llvm::DenseSet<uint64_t> discovered_set_;

  /// Native call targets discovered via vmexit→call→vmentry pattern.
  std::vector<uint64_t> native_call_targets_;
  llvm::DenseSet<uint64_t> native_call_set_;

  /// Per-callsite native call info (ordered, not deduplicated).
  std::vector<NativeCallInfo> native_call_infos_;

  /// Stored results from the last solve call (for mergeChainResults).
  std::vector<ChainEntry> last_chain_results_;

  /// Delta value from the last parseEntryWrapper call.
  uint64_t last_delta_ = 0;
};

}  // namespace omill

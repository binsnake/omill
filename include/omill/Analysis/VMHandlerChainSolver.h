#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>

#include <cstdint>
#include <optional>
#include <vector>

namespace omill {

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

  /// Solve starting from a known handler VA with an explicit initial
  /// vmcontext state (delta and hash already known).
  std::vector<ChainEntry> solveFromHandler(uint64_t handler_va,
                                           uint64_t delta,
                                           uint64_t initial_hash);

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
  const std::vector<uint64_t> &nativeCallTargets() const {
    return native_call_targets_;
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

 private:
  /// Parse a VM entry wrapper to extract initial state.
  struct WrapperInfo {
    uint64_t delta = 0;           ///< Image base delta from vmentry sub-func.
    uint64_t initial_hash = 0;    ///< Constant stored to [r12+0x190].
    uint64_t first_handler_va = 0;///< First handler's VA.
    bool valid = false;
  };

  WrapperInfo parseEntryWrapper(uint64_t wrapper_va);

  /// Compute the delta value from the vmentry sub-function.
  /// The sub-function pattern: push rax; push rbx; mov rax, <const>;
  /// mov rbx, [rsp+10h]; lea rbx, [rbx+rax]; store; pop; pop; ret
  std::optional<uint64_t> computeDelta(uint64_t subfunc_va,
                                       uint64_t return_addr);

  const BinaryMemoryMap &mem_;
  uint64_t image_base_;
  uint64_t vmenter_va_;
  uint64_t vmexit_va_;

  uint64_t handler_seg_start_ = 0;
  uint64_t handler_seg_end_ = UINT64_MAX;

  unsigned max_handlers_ = 10000;
  unsigned max_steps_per_handler_ = 5000;

  std::vector<uint64_t> discovered_handlers_;
  llvm::DenseSet<uint64_t> discovered_set_;

  /// Native call targets discovered via vmexit→call→vmentry pattern.
  std::vector<uint64_t> native_call_targets_;
  llvm::DenseSet<uint64_t> native_call_set_;

  /// Stored results from the last solve call (for mergeChainResults).
  std::vector<ChainEntry> last_chain_results_;

  /// Delta value from the last parseEntryWrapper call.
  uint64_t last_delta_ = 0;
};

}  // namespace omill

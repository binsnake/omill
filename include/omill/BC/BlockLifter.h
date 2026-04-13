/// \file BlockLifter.h
/// \brief Per-basic-block lifter for iterative optimization and target
///        resolution.
///
/// BlockLifter produces one LLVM Function per basic block using remill's
/// standard lifted signature (State*, i64 pc, Memory*) -> Memory*.  Block
/// functions terminate with musttail calls to successor block functions
/// (direct jumps, conditional branches) or the module's canonical unresolved
/// control-flow intrinsics (raw `__remill_*` when requested, otherwise the
/// legacy `__omill_dispatch_*` compatibility names)
/// (unresolved indirect targets).
///
/// This enables an iterative optimize-discover-lift loop: per-block
/// InstCombine + ConstantMemoryFolding can resolve indirect targets to
/// constants, whereupon new blocks are lifted and the cycle repeats until
/// a fixed point.  After discovery completes, a separate merge pass inlines
/// block functions back into multi-block trace functions that the rest of
/// the pipeline processes normally.

#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include <llvm/ADT/SmallVector.h>

#include "omill/BC/LiftTargetPolicy.h"

namespace llvm {
class Function;
class Module;
}  // namespace llvm

namespace remill {
class Arch;
class Instruction;
}  // namespace remill

namespace omill {

/// DevirtualizedTargetKind is reused from TraceLifter.h.
enum class DevirtualizedTargetKind;
class LiftDatabase;
class BinaryMemoryMap;

/// Maps block VA → block LLVM Function.
using BlockMap = std::unordered_map<uint64_t, llvm::Function *>;

/// Abstract interface for block-level lifting callbacks.
///
/// Parallel to TraceManager but at block granularity.  The iterative
/// discovery loop creates a subclass that owns the BlockMap and the
/// binary memory backing.
class BlockManager {
 public:
  virtual ~BlockManager();

  /// Name for a block-function.  Default: "sub_<hex>" for PCs that have
  /// been marked as function entries via MarkFunctionEntry (e.g. direct
  /// call targets and top-level LiftReachable entries), otherwise
  /// "blk_<hex>".  This allows BlockLifter to produce canonical
  /// `sub_*` names for function entry points up front so that downstream
  /// passes which gate on the `sub_` prefix (inliner, ABI recovery,
  /// calling-convention analysis, etc.) can recognize them without
  /// waiting for MergeBlockFunctionsPass to rename.
  virtual std::string BlockName(uint64_t addr);

  /// Mark \p addr as a function entry point so BlockName emits a
  /// canonical `sub_<hex>` name for it.  Idempotent.
  virtual void MarkFunctionEntry(uint64_t addr);

  /// True when \p addr was previously marked as a function entry.
  virtual bool IsFunctionEntry(uint64_t addr) const;

  /// Called when a block has been lifted (defined).
  virtual void SetLiftedBlockDefinition(uint64_t addr,
                                        llvm::Function *fn) = 0;

  /// Get existing block-function declaration (may be empty stub).
  virtual llvm::Function *GetLiftedBlockDeclaration(uint64_t addr);

  /// Get existing block-function definition (non-empty body).
  virtual llvm::Function *GetLiftedBlockDefinition(uint64_t addr);

  /// Try to read an executable byte at \p addr.
  virtual bool TryReadExecutableByte(uint64_t addr, uint8_t *byte) = 0;

  /// Resolve a discovered executable control-flow target into a typed
  /// lift-target decision.
  virtual LiftTargetDecision ResolveLiftTarget(uint64_t source_pc,
                                               uint64_t raw_target_pc,
                                               LiftTargetEdgeKind edge_kind);

  /// Resolve a decode failure while lifting the block that began at
  /// \p source_addr into a typed recovery decision.
  virtual DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_addr, uint64_t failed_pc,
      const DecodeFailureContext &ctx);

  /// Optional destination module for lifted block functions.
  /// If null, BlockLifter falls back to the Remill intrinsic module.
  virtual llvm::Module *GetLiftedBlockModule();

  /// Optional binary memory map used by BlockLifter to run call-target
  /// bridge analysis when no lift database descriptor is available.
  /// Default: nullptr (no fallback analysis).
  virtual const BinaryMemoryMap *GetBinaryMemoryMap() const { return nullptr; }

  /// Provide devirtualized targets for an indirect jump/call.
  /// Default: no-op (no targets).
  virtual void ForEachDevirtualizedTarget(
      const remill::Instruction &inst,
      std::function<void(uint64_t, DevirtualizedTargetKind)> func);

 protected:
  std::unordered_set<uint64_t> function_entry_pcs_;
};

/// Lifts individual basic blocks as separate LLVM functions.
///
/// Each block-function has remill's standard lifted signature:
///   (State*, i64 pc, Memory*) -> Memory*
///
/// Direct jumps and conditional branches produce musttail calls to
/// the successor block-function.  Indirect jumps produce calls to
/// the module's canonical unresolved jump intrinsic. Function calls produce
/// calls to the module's canonical unresolved call intrinsic followed by a
/// musttail call to the fall-through block-function.
class BlockLifter {
 public:
  BlockLifter(const remill::Arch *arch, BlockManager &manager);
  ~BlockLifter();

  void SetLiftDatabase(const LiftDatabase *db);

  /// Lift a single basic block at \p addr.  The block-function is
  /// created in the module that holds the remill intrinsics.
  ///
  /// \p discovered_targets receives the PCs of all successor blocks
  /// (direct jumps, conditional branch targets, fall-through after calls,
  /// devirtualized indirect targets).  The caller decides which to lift.
  ///
  /// Returns the block-function, or nullptr on failure.
  llvm::Function *LiftBlock(
      uint64_t addr,
      llvm::SmallVectorImpl<uint64_t> &discovered_targets);

  /// Lift the block at \p addr and all statically-reachable successors
  /// via BFS (direct jumps, conditional branches, fall-throughs).
  /// Indirect jumps are NOT followed — they are left as dispatch stubs
  /// for the iterative discovery loop to resolve.
  ///
  /// Returns the number of blocks lifted.
  unsigned LiftReachable(uint64_t addr);

  /// Get the module that block-functions are created in.
  llvm::Module *GetModule() const;

 private:
  BlockLifter() = delete;

  class Impl;
  std::unique_ptr<Impl> impl;
};

}  // namespace omill

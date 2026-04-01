/// \file TraceLifter.h
/// \brief Recursive trace lifter, ported from remill for local customization.
///
/// This is omill's own copy of the remill TraceLifter.  It uses the same
/// algorithm (dual worklists: trace_work_list for cross-function targets,
/// inst_work_list for intra-function blocks) and delegates instruction
/// decoding/lifting to remill's Arch and InstructionLifter.
///
/// Having our own copy lets us:
///   - customize block naming (only name devirtualized targets)
///   - add pre/post-instruction hooks
///   - diverge from upstream without maintaining patches

#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>

#include "omill/BC/LiftTargetPolicy.h"

namespace llvm {
class Function;
}  // namespace llvm

namespace remill {
class Arch;
class Instruction;
}  // namespace remill

namespace omill {

using TraceMap = std::unordered_map<uint64_t, llvm::Function *>;

/// Target kinds returned by devirtualization callbacks.
enum class DevirtualizedTargetKind {
  kTraceLocal,  ///< Target is within the current trace.
  kTraceHead    ///< Target is a new trace entry point.
};

/// Manages information about traces.  Permits a user of the trace lifter to
/// provide more global information to the decoder as it goes, e.g. by
/// pre-declaring the existence of many traces, and by supporting
/// devirtualization.
///
/// Callers subclass this and override the pure virtual methods.
class TraceManager {
 public:
  virtual ~TraceManager();

  /// Figure out the name for the trace starting at address \p addr.
  /// Default: "sub_<hex>".
  virtual std::string TraceName(uint64_t addr);

  /// Called when a new trace has been lifted (defined).
  virtual void SetLiftedTraceDefinition(uint64_t addr,
                                        llvm::Function *lifted_func) = 0;

  /// Get a declaration for a lifted trace.  A derived class might have
  /// additional global info that lets it declare traces ahead of time.
  ///
  /// \note May return a function from an arbitrary module.
  /// \note Must return a function with remill's 3-argument lifted form.
  virtual llvm::Function *GetLiftedTraceDeclaration(uint64_t addr);

  /// Get a definition for a lifted trace.
  ///
  /// \note May return a function from an arbitrary module.
  /// \note May return a function of an arbitrary type.
  virtual llvm::Function *GetLiftedTraceDefinition(uint64_t addr);

  /// Apply a callback that gives the decoder access to multiple targets of
  /// this instruction (indirect call or jump).  Enables devirtualization,
  /// e.g. jump-table → switch, indirect call → direct call through PLT.
  virtual void ForEachDevirtualizedTarget(
      const remill::Instruction &inst,
      std::function<void(uint64_t, DevirtualizedTargetKind)> func);

  /// Try to read an executable byte at \p addr.  Returns true on success
  /// and writes the byte to \p *byte.
  virtual bool TryReadExecutableByte(uint64_t addr, uint8_t *byte) = 0;

  /// Resolve a discovered executable control-flow target into a typed
  /// lift-target decision.
  virtual LiftTargetDecision ResolveLiftTarget(uint64_t source_pc,
                                               uint64_t raw_target_pc,
                                               LiftTargetEdgeKind edge_kind);

  /// Resolve a decode failure while lifting from \p source_addr into a typed
  /// recovery decision.
  virtual DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_addr, uint64_t failed_pc,
      const DecodeFailureContext &ctx);
};

/// Recursive trace lifter.  Decodes and lifts traces of instructions into
/// LLVM IR, following control flow within a trace and discovering new trace
/// heads for cross-function calls.
class TraceLifter {
 public:
  ~TraceLifter();

  TraceLifter(const remill::Arch *arch, TraceManager &manager);
  TraceLifter(const remill::Arch *arch, TraceManager *manager);

  static void NullCallback(uint64_t, llvm::Function *);

  /// Lift one or more traces starting from \p addr.
  /// Calls \p callback with each lifted (address, function) pair.
  bool Lift(uint64_t addr,
            std::function<void(uint64_t, llvm::Function *)> callback =
                NullCallback);

 private:
  TraceLifter() = delete;

  class Impl;
  std::unique_ptr<Impl> impl;
};

}  // namespace omill

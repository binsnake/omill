#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

namespace llvm {
class Function;
class Instruction;
class BasicBlock;
}  // namespace llvm

namespace omill {

/// Information about how a single State field is accessed within a function.
struct FieldAccessInfo {
  unsigned offset;     // Byte offset in State struct
  unsigned size;       // Size in bytes
  std::string name;    // Register name if known

  /// Instructions that load from this field.
  llvm::SmallVector<llvm::Instruction *, 4> loads;

  /// Instructions that store to this field.
  llvm::SmallVector<llvm::Instruction *, 4> stores;

  /// True if this field is read before it is written (live-in to the function).
  bool is_live_in = false;

  /// True if this field is written and may be read after the function returns
  /// (live-out). Conservatively true for any field that is written.
  bool is_live_out = false;

  /// True if every store to this field is overwritten before the next read
  /// (i.e., all stores are dead within this function).
  bool all_stores_dead = false;
};

/// Result of analyzing all State field accesses in a function.
struct StateFieldAccessInfo {
  /// Per-field access information, keyed by byte offset.
  llvm::DenseMap<unsigned, FieldAccessInfo> fields;

  /// Set of field offsets that are live-in (read before written).
  llvm::DenseSet<unsigned> live_in_offsets;

  /// Set of field offsets that are live-out (written, potentially read by caller).
  llvm::DenseSet<unsigned> live_out_offsets;

  /// All load instructions from the State struct.
  llvm::SmallVector<llvm::Instruction *, 32> all_state_loads;

  /// All store instructions to the State struct.
  llvm::SmallVector<llvm::Instruction *, 32> all_state_stores;

  bool hasAccesses() const {
    return !all_state_loads.empty() || !all_state_stores.empty();
  }
};

/// Analysis pass that identifies all accesses to the State struct in a function.
/// Resolves GEP chains to field identities and computes liveness.
class StateFieldAccessAnalysis
    : public llvm::AnalysisInfoMixin<StateFieldAccessAnalysis> {
  friend llvm::AnalysisInfoMixin<StateFieldAccessAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = StateFieldAccessInfo;

  Result run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};

}  // namespace omill

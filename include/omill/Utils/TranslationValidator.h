#pragma once

#if OMILL_ENABLE_Z3

#include <llvm/IR/Module.h>

#include <z3++.h>

#include <memory>
#include <string>
#include <vector>

namespace omill {

/// Alive2-style bounded translation validator using Z3.
///
/// Takes a snapshot of a function before a pass runs, then verifies that the
/// post-pass function is semantically equivalent for all possible symbolic
/// inputs.
///
/// Approach:
///   1. Clone the function pre-pass into a separate module.
///   2. Run the pass on the original.
///   3. Encode both functions as Z3 formulas:
///      - State arg0 is modeled as a symbolic bitvector array (Addr → Byte).
///      - Loads from State become array reads.
///      - Stores to State become array writes.
///      - Return value is also compared.
///   4. Assert output_before != output_after (negation of equivalence).
///   5. Check SAT: UNSAT = equivalent, SAT = counterexample.
///
/// Supports:
///   - Integer arithmetic, shifts, bitwise ops.
///   - Vector instructions: extractelement, insertelement, shufflevector.
///   - Bitcast between integer and vector types.
///   - sext/zext/trunc including vector variants.
///   - PHI nodes and conditional branches (loop-free CFG only).
///   - Configurable State comparison range.
class TranslationValidator {
 public:
  explicit TranslationValidator(z3::context &ctx);

  /// Clone function before pass runs.
  /// Must be called before the pass modifies F.
  void snapshotBefore(llvm::Function &F);

  /// Result of semantic equivalence check.
  struct Result {
    bool equivalent = false;
    std::string counterexample;  // Empty if equivalent.
  };

  /// Compare post-pass function against the pre-pass snapshot.
  /// Returns whether the two are semantically equivalent.
  Result verify(llvm::Function &F);

  /// Set the State byte offsets to compare. If empty, uses written offsets.
  void setCompareOffsets(std::vector<unsigned> offsets);

  /// Set max State offset to compare (default 3504).
  void setMaxStateOffset(unsigned max_offset);

 private:
  z3::context &ctx_;

  /// The cloned pre-pass module containing the snapshot.
  std::unique_ptr<llvm::Module> snapshot_module_;

  /// Name of the cloned function in snapshot_module_.
  std::string snapshot_fn_name_;

  /// User-specified offsets to compare. If empty, auto-detect.
  std::vector<unsigned> compare_offsets_;

  /// Max State offset for auto-detection.
  unsigned max_state_offset_ = 3504;

  /// Offsets written by the current function being encoded.
  std::vector<unsigned> written_offsets_;

  /// Encode a function's State-to-State transformation as Z3 constraints.
  /// Returns the final State array expression after executing the function.
  z3::expr encodeFunction(llvm::Function &F, z3::expr state_array,
                          z3::expr &ret_val);

  /// Encode a single basic block's effect on the State array.
  z3::expr encodeBlock(llvm::BasicBlock &BB, z3::expr state_array,
                       z3::expr &ret_val,
                       llvm::DenseMap<llvm::Value *, z3::expr *> &value_map);

  /// Translate an LLVM value to Z3, using cached values from value_map.
  z3::expr translateValue(llvm::Value *V,
                          llvm::DenseMap<llvm::Value *, z3::expr *> &value_map,
                          z3::expr state_array);

  /// Get the Z3 bitvector width for an LLVM type.
  /// For integer types: the bit width.
  /// For vector types: N * element_bits (flattened).
  /// For pointer types: 64.
  unsigned getBitWidth(llvm::Type *T);

  /// Owning storage for Z3 expressions.
  std::vector<std::unique_ptr<z3::expr>> owned_;
  unsigned var_counter_ = 0;

  z3::expr *own(z3::expr e);
};

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

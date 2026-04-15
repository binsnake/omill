#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Merge SROA-decomposed PHI groups back into full-width i64 PHIs.
///
/// SROA splits 64-bit State fields into sub-byte PHIs at the dispatch
/// loop header.  This pass recognizes groups of PHIs with the same
/// `state_XXXX.sroa` prefix, verifies their bit-widths sum to 64,
/// and merges them into a single i64 PHI.  Uses are rewritten:
/// - Existing uses of sub-field PHIs → trunc/lshr+trunc of the merged PHI
/// - Existing zext+shl+or reassembly chains → the merged PHI directly
class MergeDecomposedStatePHIsPass
    : public llvm::PassInfoMixin<MergeDecomposedStatePHIsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static bool isRequired() { return true; }
};

}  // namespace omill

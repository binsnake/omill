#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Merges byte-level PHI chains produced by SROA back into wider integer
/// values when all predecessors write all bytes together.
///
/// Pattern:
///   %b0 = phi i8 [a0, %bb1], [c0, %bb2], ...
///   %b1 = phi i8 [a1, %bb1], [c1, %bb2], ...
///   %b2 = phi i16/i32/i64 [a2, %bb1], [c2, %bb2], ...
///   %b3 = phi i32/i64 [a3, %bb1], [c3, %bb2], ...
///   ... reassembled with shl/zext/or into a single i32/i64
///
/// Replacement:
///   Compute the wide value in each predecessor, phi the wide value once.
class MergeBytePhisPass
    : public llvm::PassInfoMixin<MergeBytePhisPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);
};

}  // namespace omill

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates narrow constant stores that are subsumed by a preceding wider
/// store to an overlapping State offset.
///
/// When a wide store (e.g., <2 x i64> covering 16 bytes) is followed by a
/// narrow store (e.g., i8 to a byte within that range) of the same constant
/// value, the narrow store is redundant.
///
/// Before:
///   store <2 x i64> <i64 X, i64 Y>, ptr getelementptr(i8, ptr %state, i64 464)
///   store i8 0, ptr getelementptr(i8, ptr %state, i64 465)  ; dead if byte matches
///
/// After:
///   store <2 x i64> <i64 X, i64 Y>, ptr getelementptr(i8, ptr %state, i64 464)
class EliminateRedundantByteStoresPass
    : public llvm::PassInfoMixin<EliminateRedundantByteStoresPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "EliminateRedundantByteStoresPass"; }
};

}  // namespace omill

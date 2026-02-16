#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates dead store-load roundtrips on State fields between calls.
///
/// PromoteStateToSSA flushes promoted fields to State before calls that
/// take State as an argument, and reloads them after.  When the reloaded
/// value's only use is to flush it back to the same State offset before
/// the next call, both the load and store are redundant — the value is
/// already at that State offset.
///
/// Before:
///   store i64 %val, ptr getelementptr(i8, ptr %state, i64 2216)
///   call @sub_...(ptr %state, ...)
///   %reloaded = load i64, ptr getelementptr(i8, ptr %state, i64 2216)
///   store i64 %reloaded, ptr getelementptr(i8, ptr %state, i64 2216)
///   call @sub_...(ptr %state, ...)
///
/// After:
///   store i64 %val, ptr getelementptr(i8, ptr %state, i64 2216)
///   call @sub_...(ptr %state, ...)
///   call @sub_...(ptr %state, ...)
class DeadStateRoundtripEliminationPass
    : public llvm::PassInfoMixin<DeadStateRoundtripEliminationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "DeadStateRoundtripEliminationPass"; }
};

}  // namespace omill

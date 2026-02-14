#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recovers stack frame structure from RSP-relative memory accesses.
///
/// After memory intrinsic lowering, stack accesses appear as:
///   %rsp = load i64, ptr <State+RSP_offset>
///   %addr = add i64 %rsp, <frame_offset>
///   %ptr = inttoptr i64 %addr to ptr
///   %val = load i32, ptr %ptr
///
/// This pass detects these patterns, creates a stack frame alloca,
/// and replaces RSP-relative inttoptr accesses with GEPs into the alloca.
class RecoverStackFramePass
    : public llvm::PassInfoMixin<RecoverStackFramePass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "RecoverStackFramePass"; }
};

}  // namespace omill

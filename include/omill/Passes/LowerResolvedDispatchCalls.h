#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers resolved __omill_dispatch_call invocations (where the target is a
/// constant ptrtoint of a dllimport function) into explicit Win64 ABI calls.
///
/// This prevents the State pointer from escaping through the opaque
/// dispatch_call, enabling SROA to decompose the State alloca and ADCE to
/// eliminate dead PEB-walking loop bodies.
class LowerResolvedDispatchCallsPass
    : public llvm::PassInfoMixin<LowerResolvedDispatchCallsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerResolvedDispatchCallsPass"; }
};

}  // namespace omill

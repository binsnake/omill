#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Rewrites calls from one lifted function to another so they go through the
/// `_native` wrapper instead of passing the State pointer directly.
///
/// After RecoverFunctionSignatures creates `sub_X_native` wrappers and
/// EliminateStateStruct marks originals as alwaysinline, AlwaysInlinerPass
/// inlines each lifted function into its OWN wrapper.  But calls to OTHER
/// lifted functions inside the inlined code still use the lifted signature
/// `sub_Y(State*, pc, Memory*)`, causing State to escape and blocking SROA.
///
/// This pass rewrites two patterns:
///   Pattern A: direct call to lifted function sub_Y
///   Pattern B: __omill_dispatch_call targeting a lifted function
///
/// Both are rewritten to: load params from State → call sub_Y_native → store
/// return value back to State.
class RewriteLiftedCallsToNativePass
    : public llvm::PassInfoMixin<RewriteLiftedCallsToNativePass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "RewriteLiftedCallsToNativePass"; }
};

}  // namespace omill

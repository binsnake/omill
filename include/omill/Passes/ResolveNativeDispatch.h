#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves calls to __omill_native_dispatch where the PC argument is a
/// constant.  Parses the dispatch function's switch table to find the matching
/// case and replaces the call with a direct call to the target _native function.
///
/// This pass runs after ABI recovery's deobfuscation passes, which may fold
/// dynamic PC computations to constants that weren't visible when
/// RewriteLiftedCallsToNative originally created the dispatch.
class ResolveNativeDispatchPass
    : public llvm::PassInfoMixin<ResolveNativeDispatchPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveNativeDispatchPass"; }
};

}  // namespace omill

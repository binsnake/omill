#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves VM handler dispatch targets using emulator-derived flat traces.
///
/// richardvm dispatch cannot be reconstructed reliably from lifted IR alone:
/// the target base is `base_delta`, not the PE image base, and merged handlers
/// select exits from the incoming hash stored in the VM context. This pass
/// therefore trusts only the concrete trace map produced by VMTraceEmulator.
///
/// For each function tagged with `omill.vm_handler`, the pass looks up the
/// traced successor VA for that handler and replaces opaque
/// `__omill_dispatch_jump` targets with a constant VA. `__omill_dispatch_call`
/// sites are intentionally ignored here because they represent native calls
/// through the vmexit trampoline, not handler-to-handler dispatch.
class VMDispatchResolutionPass
    : public llvm::PassInfoMixin<VMDispatchResolutionPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "VMDispatchResolutionPass"; }
};

}  // namespace omill
#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates merged VM handler bodies that have been fully demerged.
///
/// After VMDispatchResolution routes dispatch jumps to per-hash demerged
/// clones and VMHandlerInliner inlines those clones into their callers,
/// the original merged handler body may become unreachable.  This pass
/// identifies merged handlers (omill.vm_handler without omill.vm_demerged_clone)
/// that have full demerge coverage and no remaining uses, and deletes them.
///
/// A merged handler is considered "fully covered" when every incoming hash
/// recorded in the VMTraceMap has a corresponding demerged clone (either a
/// vm_demerged_clone function or an outlined virtual callee) present in
/// the module.
///
/// Handlers that are only partially covered or still have uses are kept
/// as fallbacks; their names are logged when OMILL_VM_VERBOSE is set.
class VMDeadMergedHandlerEliminationPass
    : public llvm::PassInfoMixin<VMDeadMergedHandlerEliminationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() {
    return "VMDeadMergedHandlerEliminationPass";
  }
};

}  // namespace omill

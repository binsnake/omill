#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Continuation-passing transform for recursive scc_dispatch calls.
///
/// Eliminates recursive calls to scc_dispatch by converting them into
/// direct dispatch loop iterations using a cont_id alloca mechanism:
///   - Step 1: Demote dispatch PHIs to allocas.
///   - Step 2: Create a cont_id alloca; insert cont_id check before switch.
///   - Step 3: For each recursive call with a constant PC, split the handler
///     block — the "before" half stores the cont_id and target PC then
///     branches to dispatch; the "after" (continuation) half is routed from
///     dispatch via the cont_id switch.
///   - Step 4: Fix dominance violations introduced by block splitting.
///   - Step 5: Inline scc_dispatch into callers and run a cleanup pipeline.
///
/// The pass is a no-op when no scc_dispatch function is present, or when
/// scc_dispatch has no recursive calls with constant PC arguments.
class SCCDispatchCPTPass
    : public llvm::PassInfoMixin<SCCDispatchCPTPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM);
  static bool isRequired() { return true; }
};

}  // namespace omill

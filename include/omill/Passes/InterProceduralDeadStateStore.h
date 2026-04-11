#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Inter-procedural dead State-store elimination (IPDSE).
///
/// Computes, for each lifted function, the transitive set of State byte
/// offsets that may be read along any path reachable from the function's
/// entry (including through musttail chains and ordinary direct calls),
/// then uses that set to kill caller-side stores to offsets the
/// downstream never reads.
///
/// Targets the post-Phase-3.97 residual pattern where a caller stores a
/// flag/register and then musttails into a block that never reads that
/// offset. LLVM's built-in DSE cannot eliminate these because it
/// assumes any call whose arg0 aliases State clobbers all of State.
///
/// Requires CallGraphAnalysis + LiftedFunctionAnalysis. Module-level
/// because the core datum — the transitive live-in set per function —
/// must be shared between callers.
class InterProceduralDeadStateStorePass
    : public llvm::PassInfoMixin<InterProceduralDeadStateStorePass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() {
    return "InterProceduralDeadStateStorePass";
  }
};

}  // namespace omill

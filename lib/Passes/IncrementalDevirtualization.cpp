#include "omill/Passes/IncrementalDevirtualization.h"

#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/RegisterRoleMap.h"
#include "omill/Passes/IterativeBlockDiscovery.h"
#include "omill/Passes/VirtualCFGMaterialization.h"
#include "omill/Utils/LiftedNames.h"

#include <cstdlib>

namespace omill {

namespace {

bool debugEnabled() {
  static const bool enabled = [] {
    const char *v = std::getenv("OMILL_DEBUG_INCREMENTAL_DEVIRT");
    return v && v[0] == '1';
  }();
  return enabled;
}

/// Count unresolved dispatch intrinsic call sites in the module.
unsigned countUnresolvedDispatches(const llvm::Module &M) {
  unsigned count = 0;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (isDispatchCallName(callee->getName()) ||
            isDispatchJumpName(callee->getName()))
          ++count;
      }
    }
  }
  return count;
}

}  // namespace

llvm::PreservedAnalyses IncrementalDevirtualizationPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &AM) {
  bool changed = false;

  for (unsigned round = 0; round < max_outer_rounds_; ++round) {
    unsigned dispatches_before = countUnresolvedDispatches(M);

    if (debugEnabled())
      llvm::errs() << "[incr-devirt] round " << round
                   << " dispatches_before=" << dispatches_before << "\n";

    // Phase A: Block discovery — lift → optimize → resolve → lift more.
    // Uses the existing IterativeBlockDiscoveryPass which internally runs
    // CombinedFixedPointDevirt, IPCP (with affine pass-through),
    // JumpTableConcretizer, and constant dispatch resolution.
    {
      auto result = IterativeBlockDiscoveryPass(/*max_iterations=*/6).run(M, AM);
      if (!result.areAllPreserved())
        changed = true;
    }

    // Phase B: VM-model-guided materialization — rebuild VirtualMachineModel,
    // refine RegisterRoleMap, materialize proven dispatch edges, lift frontier.
    // The pass internally rebuilds the model and calls
    // RegisterRoleMap::refineFromVirtualModel (wired in Step 4).
    {
      auto result =
          VirtualCFGMaterializationPass(session_graph_).run(M, AM);
      if (!result.areAllPreserved())
        changed = true;
    }

    unsigned dispatches_after = countUnresolvedDispatches(M);

    if (debugEnabled())
      llvm::errs() << "[incr-devirt] round " << round
                   << " dispatches_after=" << dispatches_after << "\n";

    // Fixpoint: no progress if dispatch count didn't decrease.
    if (dispatches_after >= dispatches_before)
      break;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/PassManager.h>

#include <functional>

namespace omill {

/// Inter-procedural constant propagation for lifted functions.
///
/// When all resolved callers of a function store the same constant to
/// a Win64 parameter register (RCX, RDX, R8, R9) before the call,
/// this pass replaces the corresponding load in the callee's entry
/// block with that constant.
///
/// Requires CallGraphAnalysis and LiftedFunctionAnalysis.
/// Processes functions bottom-up via the call graph's SCC order,
/// skipping non-trivial SCCs (mutual recursion) and functions with
/// unresolved callers.
class InterProceduralConstPropPass
    : public llvm::PassInfoMixin<InterProceduralConstPropPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "InterProceduralConstPropPass"; }
};

/// Callback that lifts a block at the given PC, returning true if newly lifted.
using IPCPLiftCallback = std::function<bool(uint64_t pc)>;

/// Worklist-based State constant propagation through dispatch edges.
///
/// Builds a State flow graph from all dispatch_call, dispatch_jump, and
/// musttail edges in the module, then propagates constant State field
/// values forward through the graph using a worklist algorithm:
///
/// 1. Seed: collect pre-call constants at each dispatch site.
/// 2. For each (function, input_constants) on the worklist:
///    - Clone the function with input constants folded into entry loads.
///    - Optimize the clone (CombinedFixedPointDevirt + InstCombine + GVN).
///    - Extract output constants from exit stores.
///    - Pass-through: offsets the function doesn't access flow unchanged.
///    - Scan the clone for new dispatch edges and enqueue their targets.
///    - Propagate output along musttail edges to successors.
/// 3. Rewrite call sites to use specialized clones.
///
/// Returns true if any IR changes were made.
bool propagateStateConstantsWorklist(
    llvm::Module &M, const llvm::DataLayout &DL,
    llvm::ModuleAnalysisManager *MAM = nullptr,
    IPCPLiftCallback lift_callback = nullptr);

}  // namespace omill

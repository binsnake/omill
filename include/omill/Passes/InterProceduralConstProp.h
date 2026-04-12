#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Constants.h>
#include <map>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/PassManager.h>

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

/// Propagate constant State field values from callers into dispatch_call
/// targets by cloning shared callees.  For each dispatch_call site with
/// a constant PC target, collects constant stores to State fields in the
/// same BB before the call, clones the resolved callee with those constants
/// folded into entry-block loads, and rewrites the dispatch_call to a
/// direct call to the clone.  Returns true if any changes were made.
/// Persistent map of derived constants that survives across rounds.
using DerivedStateConstants = std::map<unsigned, llvm::ConstantInt *>;

bool propagateStateConstantsThroughDispatches(
    llvm::Module &M, const llvm::DataLayout &DL,
    llvm::ModuleAnalysisManager *MAM = nullptr,
    DerivedStateConstants *persistent_derived = nullptr);

}  // namespace omill

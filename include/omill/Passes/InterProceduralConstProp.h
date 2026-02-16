#pragma once

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

}  // namespace omill

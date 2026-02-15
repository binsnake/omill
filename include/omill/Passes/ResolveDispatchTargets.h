#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves __omill_dispatch_call and __omill_dispatch_jump invocations
/// whose target_pc (arg1) has been folded to a ConstantInt by prior
/// optimization passes (InstCombine, GVN, ConstantMemoryFolding).
///
/// For dispatch_call:
///   - Constant target matching IAT import → ptrtoint(@import)
///   - Constant target matching sub_<hex> → direct call
///
/// For dispatch_jump + ret:
///   - Constant target matching block_<hex> in current function → br
///   - Constant target matching sub_<hex> → musttail call + ret
///
/// Unlike ResolveIATCalls (which pattern-matches load(inttoptr(pc+offset))
/// before optimization), this catches targets that became constant *after*
/// InstCombine/GVN/ConstantMemoryFolding.
class ResolveDispatchTargetsPass
    : public llvm::PassInfoMixin<ResolveDispatchTargetsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveDispatchTargetsPass"; }
};

}  // namespace omill

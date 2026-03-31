#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves unresolved dispatch call/jump targets that are not yet constant
/// by recursively evaluating the target expression using binary memory as a
/// constant oracle.
///
/// Unlike ResolveAndLowerControlFlow (which only handles already-constant PCs)
/// and ResolveIATCalls (which matches a specific IAT load pattern), this pass
/// evaluates arbitrary expression trees feeding dispatch targets:
///
///   load(inttoptr(const))           → read from BinaryMemoryMap
///   load(inttoptr(load(...) + off)) → chained vtable dispatch
///   add/sub/xor/shl(resolved, const) → arithmetic on resolved values
///   zext/sext(resolved)             → extension of resolved values
///
/// Resolved targets are:
///   - Replaced with ConstantInt if mapped to a lifted function
///   - Replaced with ptrtoint(@import) if mapped to a known import
///   - dispatch_jump: converted to branch (intra-function) or musttail call
///
/// Best placed after ConstantMemoryFolding and before/within the iterative
/// target resolution loop (Phase 3.6).
class IndirectCallResolverPass
    : public llvm::PassInfoMixin<IndirectCallResolverPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "IndirectCallResolverPass"; }
};

}  // namespace omill

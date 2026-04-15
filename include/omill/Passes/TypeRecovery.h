#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recovers pointer types from integer arithmetic on pointers.
///
/// Remill lifts all memory accesses through integer addresses (i64).  After
/// lowering, abundant inttoptr(add(ptrtoint(p), offset)) patterns survive
/// where GEP is the correct representation.  This pass rewrites:
///
///   inttoptr(add(ptrtoint(p), const))  → GEP i8, p, const
///   inttoptr(sub(ptrtoint(p), const))  → GEP i8, p, -const
///   ptrtoint(inttoptr(x))              → x
///   inttoptr(ptrtoint(x))              → x
///
/// Multi-layer chains are handled iteratively until fixpoint.
class TypeRecoveryPass : public llvm::PassInfoMixin<TypeRecoveryPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "TypeRecoveryPass"; }
};

}  // namespace omill

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Refines `_native` function parameter types from i64 to ptr or double
/// based on usage analysis.
///
/// After RecoverFunctionSignatures creates native wrappers with all-i64
/// parameter types, this pass examines how each parameter is used:
/// - Dereferenced (inttoptr → load/store) → ptr
/// - Used in floating-point operations or originates from XMM → double
/// - Otherwise → i64 (unchanged)
///
/// Creates new functions with refined signatures, updates all call sites,
/// and erases the old functions.
class RefineFunctionSignaturesPass
    : public llvm::PassInfoMixin<RefineFunctionSignaturesPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "RefineFunctionSignaturesPass"; }
};

}  // namespace omill

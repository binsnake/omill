#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves lazy_importer patterns by replacing the runtime PEB/export-table
/// walk with a direct reference to the resolved import.
///
/// Requires HashImportAnnotationPass to have run first (produces
/// !omill.resolved_import metadata on the hash-comparison icmp).
///
/// Transformation:
///   1. Finds icmp with !omill.resolved_import metadata
///   2. Declares the resolved API as `dllimport` external
///   3. Uses LoopInfo to identify the PEB-walking loop containing the icmp
///   4. Creates a shortcut block: stores ptrtoint(@Import) to State+RAX,
///      then returns, bypassing the loop entirely
///   5. Poisons all values escaping the loop and redirects the preheader
///      to the loop exit, making loop blocks unreachable
class ResolveLazyImportsPass
    : public llvm::PassInfoMixin<ResolveLazyImportsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveLazyImportsPass"; }
};

}  // namespace omill

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Combined pass that detects lazy_importer FNV-1a hash patterns and resolves
/// them to direct import references in a single function walk.
///
/// Replaces the former HashImportAnnotationPass + ResolveLazyImportsPass
/// two-pass pipeline.  The annotation phase identifies FNV hash comparisons
/// and resolves import names via ImportHashDB; the resolution phase rewrites
/// the PEB-walking loop to a direct import reference.  Intermediate metadata
/// (!omill.resolved_import) is still written for diagnostics and for any
/// external tooling that consumes it, but the resolution phase uses the
/// in-memory candidate list rather than re-scanning the function.
class ResolveHashImportsPass
    : public llvm::PassInfoMixin<ResolveHashImportsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveHashImportsPass"; }
};

}  // namespace omill

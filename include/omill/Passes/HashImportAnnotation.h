#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Detects lazy_importer's FNV-1a hash patterns in lifted IR and annotates
/// resolved import names as LLVM metadata (!omill.resolved_import).
///
/// Detection heuristic:
///   1. Find `mul i32 %x, 16777619` (FNV-1a prime 0x01000193)
///   2. Trace forward to `icmp eq i32 %result, <constant>` (target hash)
///   3. Resolve via ImportHashDB
///   4. Annotate the icmp with metadata
class HashImportAnnotationPass
    : public llvm::PassInfoMixin<HashImportAnnotationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "HashImportAnnotationPass"; }
};

}  // namespace omill

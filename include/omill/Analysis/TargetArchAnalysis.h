#pragma once

#include <llvm/IR/PassManager.h>

#include "omill/Arch/ArchABI.h"

namespace llvm {
class Module;
}  // namespace llvm

namespace omill {

/// Module-level analysis that provides the target architecture ABI.
///
/// Reads `omill.target_arch` and `omill.target_os` module metadata.
/// Falls back to x86_64 / Win64 when metadata is absent (backward compat).
class TargetArchAnalysis
    : public llvm::AnalysisInfoMixin<TargetArchAnalysis> {
  friend llvm::AnalysisInfoMixin<TargetArchAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = ArchABI;

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

/// Helper: attach omill.target_arch / omill.target_os metadata to a module.
void setTargetArchMetadata(llvm::Module &M, TargetArch arch,
                           llvm::StringRef os);

}  // namespace omill

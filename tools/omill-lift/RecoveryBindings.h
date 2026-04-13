#pragma once

#include <functional>
#include <vector>

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>

#include "RuntimeAdapters.h"

namespace omill::tooling {

struct OmillLiftTargetQueryOps {
  std::function<llvm::SmallVector<uint64_t, 16>()>
      collect_executable_placeholder_declaration_targets;
  std::function<llvm::SmallVector<uint64_t, 16>()>
      collect_declared_structural_targets_with_defined_implementations;
  std::function<llvm::SmallVector<uint64_t, 16>()>
      collect_output_root_constant_code_call_targets;
  std::function<llvm::SmallVector<uint64_t, 16>()>
      collect_output_root_constant_calli_targets;
  std::function<llvm::SmallVector<uint64_t, 16>()>
      collect_output_root_constant_dispatch_targets;
};

struct OmillLiftPatchOps {
  std::function<void(llvm::ArrayRef<uint64_t>, llvm::StringRef, llvm::StringRef)>
      patch_constant_inttoptr_calls_to_native;
  std::function<unsigned(llvm::ArrayRef<uint64_t>, llvm::StringRef,
                         llvm::StringRef)>
      patch_declared_lifted_or_block_calls_to_defined_targets;
  std::function<unsigned(llvm::ArrayRef<uint64_t>, llvm::StringRef,
                         llvm::StringRef)>
      patch_constant_calli_targets_to_direct_calls;
  std::function<unsigned(llvm::ArrayRef<uint64_t>, llvm::StringRef,
                         llvm::StringRef)>
      patch_constant_dispatch_targets_to_direct_calls;
};

struct OmillLiftOutputRecoveryBindings {
  OutputRecoveryTelemetry telemetry;
  OutputRecoveryCleanupOps cleanup;
  OutputRecoveryImportOps import;
  OmillLiftTargetQueryOps target_queries;
  OmillLiftPatchOps patches;
};

OutputRecoveryCallbacks buildOmillLiftOutputRecoveryCallbacks(
    llvm::Module &module, llvm::ModuleAnalysisManager &module_analysis_manager,
    OmillLiftOutputRecoveryBindings &bindings);

}  // namespace omill::tooling

#pragma once

#include <functional>
#include <optional>
#include <string>
#include <vector>

#include <llvm/ADT/StringRef.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>

#include "omill/Devirtualization/Runtime.h"

namespace llvm {
class Function;
}

namespace omill::tooling {

struct ChildLiftTextArtifact {
  std::string ir_text;
  std::string model_text;
};

struct OutputRecoveryOptionInputs {
  bool raw_binary = false;
  bool no_abi = false;
  bool use_block_lifting = false;
  bool enable_devirtualization = false;
  bool allow_noabi_postmain_rounds = false;
  bool allow_abi_postmain_rounds = false;
  bool enable_nested_vm_enter_child_import = false;
  bool enable_precise_logs = false;
  unsigned max_vm_enter_child_imports = 1;
  unsigned late_noabi_closure_rounds = 4;
  unsigned max_noabi_executable_child_import_rounds = 4;
  unsigned late_abi_closure_rounds = 4;
};

struct OutputRecoveryTelemetry {
  std::function<void(llvm::StringRef)> append_debug_marker;
  std::function<void(llvm::StringRef, llvm::StringRef, std::optional<int64_t>)>
      emit_warn_event;
  std::function<void(const RuntimePreciseLogEvent &)> precise_log;
  std::function<void(llvm::StringRef, bool)> note_abi_post_cleanup_step;
};

struct OutputRecoveryCleanupOps {
  std::function<void(llvm::StringRef)> run_late_closure_canonicalization;
  std::function<void(llvm::StringRef)> run_post_patch_cleanup;
  std::function<void()> run_final_output_cleanup;
  std::function<void()> annotate_vm_unresolved_continuations;
  std::function<void()> prune_to_defined_output_root_closure;
  std::function<void()> rerun_late_output_root_target_pipeline;
  std::function<void()> sanitize_remaining_poison_native_helper_args;
  std::function<void()> erase_noop_self_recursive_native_calls;
  std::function<bool(FrontierDiscoveryPhase, llvm::StringRef)>
      advance_session_owned_frontier_work;
};

struct OutputRecoveryImportOps {
  std::function<std::optional<ChildLiftTextArtifact>(uint64_t, bool, bool, bool,
                                                     bool)>
      lift_child_text;
  std::function<llvm::Function *(uint64_t, const omill::ChildLiftArtifact &,
                                 const omill::ChildImportPlan &,
                                 llvm::StringRef)>
      import_executable_child_root;
  std::function<llvm::Function *(uint64_t, const omill::BinaryRegionSnapshot &,
                                 const omill::ChildImportPlan &)>
      import_executable_snapshot_slice;
  std::function<llvm::Function *(llvm::StringRef, uint64_t, std::string *)>
      import_recovered_terminal_boundary_function;
  std::function<void(uint64_t)> note_imported_target;
};

struct OutputRecoveryTargetOps {
  std::function<std::vector<uint64_t>()>
      collect_executable_placeholder_declaration_targets;
  std::function<std::vector<uint64_t>()>
      collect_declared_structural_targets_with_defined_implementations;
  std::function<std::vector<uint64_t>()>
      collect_output_root_constant_code_call_targets;
  std::function<std::vector<uint64_t>()>
      collect_output_root_constant_calli_targets;
  std::function<std::vector<uint64_t>()>
      collect_output_root_constant_dispatch_targets;
  std::function<void(const std::vector<uint64_t> &, llvm::StringRef,
                     llvm::StringRef)>
      patch_constant_inttoptr_calls_to_native;
  std::function<unsigned(const std::vector<uint64_t> &, llvm::StringRef,
                         llvm::StringRef)>
      patch_declared_lifted_or_block_calls_to_defined_targets;
  std::function<unsigned(const std::vector<uint64_t> &, llvm::StringRef,
                         llvm::StringRef)>
      patch_constant_calli_targets_to_direct_calls;
  std::function<unsigned(const std::vector<uint64_t> &, llvm::StringRef,
                         llvm::StringRef)>
      patch_constant_dispatch_targets_to_direct_calls;
};

struct OutputRecoveryServices {
  llvm::Module &module;
  llvm::ModuleAnalysisManager &module_analysis_manager;
  OutputRecoveryTelemetry telemetry;
  OutputRecoveryCleanupOps cleanup;
  OutputRecoveryImportOps import;
  OutputRecoveryTargetOps targets;
};

OutputRecoveryOptions buildOutputRecoveryOptions(
    const OutputRecoveryOptionInputs &inputs);

OutputRecoveryCallbacks buildOutputRecoveryCallbacks(
    OutputRecoveryServices &services);

}  // namespace omill::tooling

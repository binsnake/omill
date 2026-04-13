#include "RuntimeAdapters.h"

#include <memory>

#include <llvm/IR/Function.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>

namespace omill::tooling {

OutputRecoveryOptions buildOutputRecoveryOptions(
    const OutputRecoveryOptionInputs &inputs) {
  OutputRecoveryOptions options;
  options.raw_binary = inputs.raw_binary;
  options.no_abi = inputs.no_abi;
  options.use_block_lifting = inputs.use_block_lifting;
  options.enable_devirtualization = inputs.enable_devirtualization;
  options.enable_precise_logs = inputs.enable_precise_logs;
  options.allow_noabi_postmain_rounds = inputs.allow_noabi_postmain_rounds;
  options.allow_abi_postmain_rounds = inputs.allow_abi_postmain_rounds;
  options.enable_nested_vm_enter_child_import =
      inputs.enable_nested_vm_enter_child_import;
  options.max_vm_enter_child_imports = inputs.max_vm_enter_child_imports;
  options.late_noabi_closure_rounds = inputs.late_noabi_closure_rounds;
  options.max_noabi_executable_child_import_rounds =
      inputs.max_noabi_executable_child_import_rounds;
  options.late_abi_closure_rounds = inputs.late_abi_closure_rounds;
  return options;
}

OutputRecoveryCallbacks buildOutputRecoveryCallbacks(
    OutputRecoveryServices &services) {
  struct CallbackState {
    llvm::Module *module;
    llvm::ModuleAnalysisManager *module_analysis_manager;
    OutputRecoveryTelemetry telemetry;
    OutputRecoveryCleanupOps cleanup;
    OutputRecoveryImportOps import;
    OutputRecoveryTargetOps targets;
  };
  auto state = std::make_shared<CallbackState>(CallbackState{
      &services.module,
      &services.module_analysis_manager,
      services.telemetry,
      services.cleanup,
      services.import,
      services.targets,
  });

  OutputRecoveryCallbacks callbacks;
  callbacks.precise_log = state->telemetry.precise_log;
  callbacks.run_late_closure_canonicalization =
      [state](llvm::StringRef reason) {
        state->cleanup.run_late_closure_canonicalization(reason);
      };
  callbacks.run_post_patch_cleanup = [state](llvm::StringRef reason) {
    state->cleanup.run_post_patch_cleanup(reason);
  };
  callbacks.run_final_output_cleanup = [state]() {
    state->cleanup.run_final_output_cleanup();
  };
  callbacks.annotate_vm_unresolved_continuations = [state]() {
    state->cleanup.annotate_vm_unresolved_continuations();
  };
  callbacks.before_noabi_frontier_round = [state](unsigned round) {
    if (state->telemetry.append_debug_marker) {
      state->telemetry.append_debug_marker(
          (llvm::Twine("noabi:round_") + llvm::Twine(round) +
           ":before_canonicalization")
              .str());
    }
    state->cleanup.run_late_closure_canonicalization(
        "noabi_late_output_root_closure");
    if (state->telemetry.append_debug_marker) {
      state->telemetry.append_debug_marker(
          (llvm::Twine("noabi:round_") + llvm::Twine(round) +
           ":after_canonicalization")
              .str());
    }
    return true;
  };
  callbacks.after_noabi_frontier_round =
      [state](unsigned round, const FrontierRoundSummary &round_summary) {
        if (state->telemetry.append_debug_marker) {
          state->telemetry.append_debug_marker(
              (llvm::Twine("noabi:round_") + llvm::Twine(round) +
               ":after_frontier")
                  .str());
        }
        llvm::ModulePassManager MPM;
        buildLateClosurePatchPipeline(MPM, 80);
        MPM.run(*state->module, *state->module_analysis_manager);
        if (state->telemetry.append_debug_marker) {
          state->telemetry.append_debug_marker(
              (llvm::Twine("noabi:round_") + llvm::Twine(round) +
               ":after_patch")
                  .str());
        }
        state->cleanup.annotate_vm_unresolved_continuations();
        return round_summary.changed;
      };
  callbacks.prune_to_defined_output_root_closure = [state]() {
    state->cleanup.prune_to_defined_output_root_closure();
  };
  callbacks.rerun_late_output_root_target_pipeline = [state]() {
    state->cleanup.rerun_late_output_root_target_pipeline();
  };
  callbacks.sanitize_remaining_poison_native_helper_args = [state]() {
    state->cleanup.sanitize_remaining_poison_native_helper_args();
  };
  callbacks.erase_noop_self_recursive_native_calls = [state]() {
    state->cleanup.erase_noop_self_recursive_native_calls();
  };
  callbacks.advance_session_owned_frontier_work =
      [state](FrontierDiscoveryPhase phase, llvm::StringRef label) {
        return state->cleanup.advance_session_owned_frontier_work(phase, label);
      };
  callbacks.lift_child_target =
      [state](uint64_t target_pc, bool no_abi, bool enable_gsd,
              bool enable_recovery_mode,
              bool dump_virtual_model) -> std::optional<ChildLiftArtifact> {
        auto child = state->import.lift_child_text(
            target_pc, no_abi, enable_gsd, enable_recovery_mode,
            dump_virtual_model);
        if (!child)
          return std::nullopt;
        ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = std::move(child->ir_text);
        artifact.model_text = std::move(child->model_text);
        return artifact;
      };
  callbacks.import_executable_child =
      [state](uint64_t target_pc, const ChildLiftArtifact &artifact,
              const ChildImportPlan &preimport_plan,
              llvm::StringRef name_prefix) {
        ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        auto *imported = state->import.import_executable_child_root(
            target_pc, artifact, preimport_plan, name_prefix);
        if (!imported) {
          plan.eligibility = ImportEligibility::kRejected;
          plan.rejection_reason = RecoveryRejectionReason::kImportFailed;
          return plan;
        }
        plan.eligibility = ImportEligibility::kImportable;
        plan.rejection_reason = RecoveryRejectionReason::kNone;
        plan.imported_root = imported;
        plan.allowed_declaration_callees =
            preimport_plan.allowed_declaration_callees;
        plan.lowering_helper_callees =
            preimport_plan.lowering_helper_callees;
        plan.import_class = preimport_plan.import_class;
        plan.proof = preimport_plan.proof;
        if (!plan.selected_root_pc)
          plan.selected_root_pc = preimport_plan.selected_root_pc;
        return plan;
      };
  callbacks.import_executable_snapshot_slice =
      [state](uint64_t target_pc, const BinaryRegionSnapshot &snapshot,
              const ChildImportPlan &preimport_plan) {
        ChildImportPlan plan = preimport_plan;
        plan.target_pc = target_pc;
        auto *imported = state->import.import_executable_snapshot_slice(
            target_pc, snapshot, preimport_plan);
        if (!imported) {
          plan.eligibility = ImportEligibility::kRejected;
          if (plan.rejection_reason == RecoveryRejectionReason::kNone)
            plan.rejection_reason = RecoveryRejectionReason::kImportFailed;
          if (plan.rejection_detail.empty())
            plan.rejection_detail = "snapshot_slice_import_failed";
          return plan;
        }
        plan.eligibility = ImportEligibility::kImportable;
        plan.rejection_reason = RecoveryRejectionReason::kNone;
        plan.imported_root = imported;
        return plan;
      };
  callbacks.import_vm_enter_child =
      [state](uint64_t target_pc, const ChildLiftArtifact &artifact,
              const ChildImportPlan &preimport_plan,
              llvm::Function &placeholder) {
        ChildImportPlan plan = preimport_plan;
        plan.target_pc = target_pc;
        if (!plan.selected_root_pc)
          plan.selected_root_pc = artifact.selected_root_pc;
        if (plan.eligibility != ImportEligibility::kImportable)
          return plan;
        auto *imported = state->import.import_executable_child_root(
            target_pc, artifact, preimport_plan, "");
        if (!imported) {
          plan.eligibility = ImportEligibility::kRejected;
          if (plan.rejection_reason == RecoveryRejectionReason::kNone)
            plan.rejection_reason = RecoveryRejectionReason::kImportFailed;
          if (plan.rejection_detail.empty())
            plan.rejection_detail = "vm_enter_child_import_failed";
          return plan;
        }
        if (imported->getFunctionType() != placeholder.getFunctionType()) {
          plan.eligibility = ImportEligibility::kRejected;
          plan.rejection_reason = RecoveryRejectionReason::kTypeMismatch;
          plan.rejection_detail = "type_mismatch";
          return plan;
        }
        plan.eligibility = ImportEligibility::kImportable;
        plan.rejection_reason = RecoveryRejectionReason::kNone;
        plan.imported_root = imported;
        return plan;
      };
  callbacks.note_imported_target = [state](uint64_t target_pc) {
    state->import.note_imported_target(target_pc);
  };
  callbacks.collect_executable_placeholder_declaration_targets = [state]() {
    return state->targets.collect_executable_placeholder_declaration_targets();
  };
  callbacks.collect_declared_structural_targets_with_defined_implementations =
      [state]() {
        return state->targets
            .collect_declared_structural_targets_with_defined_implementations();
      };
  callbacks.collect_output_root_constant_code_call_targets = [state]() {
    return state->targets.collect_output_root_constant_code_call_targets();
  };
  callbacks.collect_output_root_constant_calli_targets = [state]() {
    return state->targets.collect_output_root_constant_calli_targets();
  };
  callbacks.collect_output_root_constant_dispatch_targets = [state]() {
    return state->targets.collect_output_root_constant_dispatch_targets();
  };
  callbacks.patch_constant_inttoptr_calls_to_native =
      [state](const std::vector<uint64_t> &targets, llvm::StringRef marker,
              llvm::StringRef message) {
        state->targets.patch_constant_inttoptr_calls_to_native(
            targets, marker, message);
      };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [state](const std::vector<uint64_t> &targets, llvm::StringRef marker,
              llvm::StringRef message) -> unsigned {
        return state->targets
            .patch_declared_lifted_or_block_calls_to_defined_targets(
                targets, marker, message);
      };
  callbacks.patch_constant_calli_targets_to_direct_calls =
      [state](const std::vector<uint64_t> &targets, llvm::StringRef marker,
              llvm::StringRef message) -> unsigned {
        return state->targets.patch_constant_calli_targets_to_direct_calls(
            targets, marker, message);
      };
  callbacks.patch_constant_dispatch_targets_to_direct_calls =
      [state](const std::vector<uint64_t> &targets, llvm::StringRef marker,
              llvm::StringRef message) -> unsigned {
        return state->targets.patch_constant_dispatch_targets_to_direct_calls(
            targets, marker, message);
      };
  callbacks.note_abi_post_cleanup_step =
      [state](llvm::StringRef label, bool starting) {
        state->telemetry.note_abi_post_cleanup_step(label, starting);
      };
  return callbacks;
}

}  // namespace omill::tooling

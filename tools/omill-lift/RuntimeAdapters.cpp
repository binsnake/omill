#include "RuntimeAdapters.h"

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
    OutputRecoveryAdapterContext &context) {
  OutputRecoveryCallbacks callbacks;
  callbacks.precise_log = context.precise_log;
  callbacks.run_late_closure_canonicalization =
      [&](llvm::StringRef reason) { context.run_late_closure_canonicalization(reason); };
  callbacks.run_post_patch_cleanup =
      [&](llvm::StringRef reason) { context.run_post_patch_cleanup(reason); };
  callbacks.run_final_output_cleanup = [&]() { context.run_final_output_cleanup(); };
  callbacks.annotate_vm_unresolved_continuations = [&]() {
    context.annotate_vm_unresolved_continuations();
  };
  callbacks.before_noabi_frontier_round = [&](unsigned round) {
    if (context.append_debug_marker) {
      context.append_debug_marker(
          (llvm::Twine("noabi:round_") + llvm::Twine(round) +
           ":before_canonicalization")
              .str());
    }
    context.run_late_closure_canonicalization("noabi_late_output_root_closure");
    if (context.append_debug_marker) {
      context.append_debug_marker(
          (llvm::Twine("noabi:round_") + llvm::Twine(round) +
           ":after_canonicalization")
              .str());
    }
    if (!verifyModule(context.module, nullptr))
      return true;
    if (context.emit_warn_event) {
      context.emit_warn_event(
          "noabi_late_closure_invalid_after_canonicalization",
          "module verification failed after no-ABI late closure "
          "canonicalization; skipping frontier advancement",
          static_cast<int64_t>(round));
    }
    return false;
  };
  callbacks.after_noabi_frontier_round =
      [&](unsigned round, const FrontierRoundSummary &round_summary) {
        if (context.append_debug_marker) {
          context.append_debug_marker(
              (llvm::Twine("noabi:round_") + llvm::Twine(round) +
               ":after_frontier")
                  .str());
        }
        llvm::ModulePassManager MPM;
        buildLateClosurePatchPipeline(MPM, 80);
        MPM.run(context.module, context.module_analysis_manager);
        if (context.append_debug_marker) {
          context.append_debug_marker(
              (llvm::Twine("noabi:round_") + llvm::Twine(round) +
               ":after_patch")
                  .str());
        }
        context.annotate_vm_unresolved_continuations();
        return round_summary.changed;
      };
  callbacks.prune_to_defined_output_root_closure = [&]() {
    context.prune_to_defined_output_root_closure();
  };
  callbacks.rerun_late_output_root_target_pipeline = [&]() {
    context.rerun_late_output_root_target_pipeline();
  };
  callbacks.sanitize_remaining_poison_native_helper_args = [&]() {
    context.sanitize_remaining_poison_native_helper_args();
  };
  callbacks.erase_noop_self_recursive_native_calls = [&]() {
    context.erase_noop_self_recursive_native_calls();
  };
  callbacks.advance_session_owned_frontier_work =
      [&](FrontierDiscoveryPhase phase, llvm::StringRef label) {
        return context.advance_session_owned_frontier_work(phase, label);
      };
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode,
          bool dump_virtual_model) -> std::optional<ChildLiftArtifact> {
        auto child = context.lift_child_text(target_pc, no_abi, enable_gsd,
                                             enable_recovery_mode,
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
      [&](uint64_t target_pc, const ChildLiftArtifact &artifact,
          const ChildImportPlan &preimport_plan, llvm::StringRef name_prefix) {
        ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        auto *imported = context.import_executable_child_root(
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
        return plan;
      };
  callbacks.import_vm_enter_child =
      [&](uint64_t target_pc, const ChildLiftArtifact &artifact,
          llvm::Function &placeholder) {
        ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        std::string import_rejection_reason;
        auto *imported = context.import_recovered_terminal_boundary_function(
            artifact.ir_text, target_pc, &import_rejection_reason);
        if (!imported) {
          plan.eligibility = ImportEligibility::kRejected;
          plan.rejection_reason = RecoveryRejectionReason::kImportFailed;
          plan.rejection_detail = import_rejection_reason;
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
  callbacks.note_imported_target = [&](uint64_t target_pc) {
    context.note_imported_target(target_pc);
  };
  callbacks.collect_executable_placeholder_declaration_targets = [&]() {
    return context.collect_executable_placeholder_declaration_targets();
  };
  callbacks.collect_declared_structural_targets_with_defined_implementations =
      [&]() {
        return context
            .collect_declared_structural_targets_with_defined_implementations();
      };
  callbacks.collect_output_root_constant_code_call_targets = [&]() {
    return context.collect_output_root_constant_code_call_targets();
  };
  callbacks.collect_output_root_constant_calli_targets = [&]() {
    return context.collect_output_root_constant_calli_targets();
  };
  callbacks.collect_output_root_constant_dispatch_targets = [&]() {
    return context.collect_output_root_constant_dispatch_targets();
  };
  callbacks.patch_constant_inttoptr_calls_to_native =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) {
        context.patch_constant_inttoptr_calls_to_native(targets, marker,
                                                        message);
      };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return context.patch_declared_lifted_or_block_calls_to_defined_targets(
            targets, marker, message);
      };
  callbacks.patch_constant_calli_targets_to_direct_calls =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return context.patch_constant_calli_targets_to_direct_calls(targets,
                                                                    marker,
                                                                    message);
      };
  callbacks.patch_constant_dispatch_targets_to_direct_calls =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return context.patch_constant_dispatch_targets_to_direct_calls(
            targets, marker, message);
      };
  callbacks.note_abi_post_cleanup_step =
      [&](llvm::StringRef label, bool starting) {
        context.note_abi_post_cleanup_step(label, starting);
      };
  return callbacks;
}

}  // namespace omill::tooling

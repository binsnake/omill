#include "RecoveryBindings.h"

namespace omill::tooling {

namespace {

std::vector<uint64_t> vectorizeTargets(
    const std::function<llvm::SmallVector<uint64_t, 16>()> &collector) {
  auto targets = collector();
  return std::vector<uint64_t>(targets.begin(), targets.end());
}

}  // namespace

OutputRecoveryCallbacks buildOmillLiftOutputRecoveryCallbacks(
    llvm::Module &module, llvm::ModuleAnalysisManager &module_analysis_manager,
    OmillLiftOutputRecoveryBindings &bindings) {
  OutputRecoveryTargetOps targets;
  targets.collect_executable_placeholder_declaration_targets = [&]() {
    return vectorizeTargets(
        bindings.target_queries.collect_executable_placeholder_declaration_targets);
  };
  targets.collect_declared_structural_targets_with_defined_implementations = [&]() {
    return vectorizeTargets(bindings.target_queries
                                .collect_declared_structural_targets_with_defined_implementations);
  };
  targets.collect_output_root_constant_code_call_targets = [&]() {
    return vectorizeTargets(
        bindings.target_queries.collect_output_root_constant_code_call_targets);
  };
  targets.collect_output_root_constant_calli_targets = [&]() {
    return vectorizeTargets(
        bindings.target_queries.collect_output_root_constant_calli_targets);
  };
  targets.collect_output_root_constant_dispatch_targets = [&]() {
    return vectorizeTargets(
        bindings.target_queries.collect_output_root_constant_dispatch_targets);
  };
  targets.patch_constant_inttoptr_calls_to_native =
      [&](const std::vector<uint64_t> &ordered_targets, llvm::StringRef marker,
          llvm::StringRef message) {
        bindings.patches.patch_constant_inttoptr_calls_to_native(
            ordered_targets, marker, message);
      };
  targets.patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](const std::vector<uint64_t> &ordered_targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return bindings.patches
            .patch_declared_lifted_or_block_calls_to_defined_targets(
                ordered_targets, marker, message);
      };
  targets.patch_constant_calli_targets_to_direct_calls =
      [&](const std::vector<uint64_t> &ordered_targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return bindings.patches.patch_constant_calli_targets_to_direct_calls(
            ordered_targets, marker, message);
      };
  targets.patch_constant_dispatch_targets_to_direct_calls =
      [&](const std::vector<uint64_t> &ordered_targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return bindings.patches.patch_constant_dispatch_targets_to_direct_calls(
            ordered_targets, marker, message);
      };

  OutputRecoveryServices services{module,
                                  module_analysis_manager,
                                  bindings.telemetry,
                                  bindings.cleanup,
                                  bindings.import,
                                  std::move(targets)};
  return buildOutputRecoveryCallbacks(services);
}

}  // namespace omill::tooling

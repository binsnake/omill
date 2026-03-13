#pragma once

#include <functional>
#include <string>

#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/IR/PassManager.h>

#include "omill/Arch/ArchABI.h"

namespace omill {

enum class CleanupProfile {
  kLightScalar,
  kLightScalarNoInstCombine,
  kStateToSSA,
  kPostInline,
  kBoundary,
  kFinal,
};

/// Configuration for the omill optimization pipeline.
struct PipelineOptions {
  /// Target architecture (default: x86_64).
  TargetArch target_arch = TargetArch::kX86_64;

  /// Target OS name (default: "windows").
  std::string target_os = "windows";

  /// Stage 2: Lower remill intrinsics to native LLVM operations.
  bool lower_intrinsics = true;

  /// Stage 3: Promote State struct fields to SSA, dead store elimination.
  bool optimize_state = true;

  /// Debug/staging knob: stop pipeline immediately after state optimization.
  /// Used by tests that run the pipeline in multiple explicit phases.
  bool stop_after_state_optimization = false;

  /// Stage 4: Lower control flow intrinsics (call/ret/jump).
  bool lower_control_flow = true;

  /// Stage 5: Recover calling conventions and eliminate State struct.
  /// (Not yet implemented — future stage)
  bool recover_abi = false;

  /// Stage 6: Deobfuscation passes (MBA, opaque predicates, CFF).
  /// (Not yet implemented — future stage)
  bool deobfuscate = false;

  /// Iteratively resolve indirect dispatch targets after optimization.
  /// Runs between Phase 3.5 and Phase 4.
  bool resolve_indirect_targets = false;

  /// Inter-procedural constant propagation across call boundaries.
  /// Auto-enabled when resolve_indirect_targets is on.
  bool interprocedural_const_prop = false;

  /// Maximum iterations for iterative target resolution.
  /// Each VM handler in a chain requires ~2 iterations (lift + inline+resolve),
  /// so this needs to be high enough to handle long handler chains.
  unsigned max_resolution_iterations = 32;

  /// Refine _native function parameter types (ptr vs i64 vs double).
  /// Opt-in; runs late in Phase 4 after ABI recovery.
  bool refine_signatures = false;

  /// Legacy VM devirtualization path: resolve dispatch targets from
  /// emulator-derived flat traces for a specific trace-driven VM pipeline.
  /// Generic static devirtualization should use separate VM-agnostic analyses.
  bool vm_devirtualize = false;

  /// Generic static devirtualization path: use the VM-agnostic symbolic
  /// virtual-state model to materialize proven virtual CFG edges.
  bool generic_static_devirtualize = false;

  /// When generic_static_devirtualize is enabled, validate rewritten
  /// functions with the TranslationValidator when Z3 is available.
  bool verify_generic_static_devirtualization = false;

  /// When set, per-function pass adaptors in Phases 1–3.5 run only on
  /// functions matching this predicate.  Module-wide passes are unaffected.
  /// Used by the VM discovery loop to avoid re-processing already-optimized
  /// functions.
  std::function<bool(llvm::Function &)> scope_predicate;

  /// Use the blocks-as-functions lifting architecture instead of TraceLifter.
  /// When enabled, the pipeline inserts IterativeBlockDiscoveryPass and
  /// MergeBlockFunctionsPass instead of IterativeTargetResolutionPass.
  /// Requires block-functions to already exist in the module (created by
  /// BlockLifter before calling buildPipeline).
  bool use_block_lifting = false;

  /// Run standard LLVM cleanup passes between stages.
  bool run_cleanup_passes = true;

  /// Keep Remill semantic bodies and lifting support alive across pipeline
  /// boundaries so the driver can lift additional targets into the same
  /// module later. The driver is responsible for final cleanup once
  /// iterative discovery is closed.
  bool preserve_lifted_semantics = false;

  /// Merge block functions only after the discovery epoch converges.
  bool merge_block_functions_after_fixpoint = true;

  /// Run interprocedural constant propagation inside the iterative
  /// resolution epoch so newly propagated constants can participate in
  /// the same discovery round.
  bool run_ipcp_inside_resolution = true;
};

/// Builds the omill optimization pipeline.
///
/// Usage:
///   llvm::ModulePassManager MPM;
///   omill::PipelineOptions opts;
///   omill::buildPipeline(MPM, opts);
///
///   llvm::ModuleAnalysisManager MAM;
///   // ... register standard analyses ...
///   MPM.run(*M, MAM);
///
void buildPipeline(llvm::ModulePassManager &MPM, const PipelineOptions &opts);

/// Build only the intrinsic lowering stage (Stage 2).
void buildIntrinsicLoweringPipeline(llvm::FunctionPassManager &FPM);

/// Build only the state optimization stage (Stage 3).
void buildStateOptimizationPipeline(llvm::FunctionPassManager &FPM,
                                    bool deobfuscate = false);

/// Build only the control flow recovery stage (Stage 4).
void buildControlFlowPipeline(llvm::FunctionPassManager &FPM);

/// Build only the ABI recovery stage (Stage 5).
void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM,
                              const PipelineOptions &opts);

/// Build only the deobfuscation stage (Stage 6).
void buildDeobfuscationPipeline(llvm::FunctionPassManager &FPM,
                                const PipelineOptions &opts);

/// Build the late cleanup pipeline (sentinel data elimination + DCE).
/// Run after ABI recovery and post-ABI deobfuscation, before output.
void buildLateCleanupPipeline(llvm::ModulePassManager &MPM);

/// Build a shared cleanup bundle using one of the canonical cleanup profiles.
void buildCleanupPipeline(llvm::FunctionPassManager &FPM,
                          CleanupProfile profile);
void buildCleanupPipeline(llvm::ModulePassManager &MPM,
                          CleanupProfile profile);

/// Internalize and remove now-dead Remill lifting infrastructure once no
/// further iterative lifting rounds will run.
void buildLiftInfrastructureCleanupPipeline(llvm::ModulePassManager &MPM);

/// Resolve constant inttoptr call targets to direct _native calls and run
/// bounded post-rewrite inline/cleanup rounds until convergence.
///
/// Emits per-round progress metadata in:
///   !omill.inttoptr_closure_rounds = {round, resolved_calls, remaining_calls}
void buildIntToPtrClosurePipeline(llvm::ModulePassManager &MPM);

/// Build the post-patch cleanup pipeline used after call-target rewrites.
/// Includes module inlining and core scalar cleanup passes.
void buildPostPatchCleanupPipeline(llvm::ModulePassManager &MPM,
                                   unsigned inline_threshold = 80);

/// Register all omill function-level analyses.
void registerAnalyses(llvm::FunctionAnalysisManager &FAM);

/// Register all omill module-level analyses.
void registerModuleAnalyses(llvm::ModuleAnalysisManager &MAM);

/// Register omill's custom alias analysis with an AAManager.
/// Call before PB.registerFunctionAnalyses() so the custom AA is included.
void registerAAWithManager(llvm::AAManager &AAM);

}  // namespace omill

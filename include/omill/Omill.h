#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Configuration for the omill optimization pipeline.
struct PipelineOptions {
  /// Stage 2: Lower remill intrinsics to native LLVM operations.
  bool lower_intrinsics = true;

  /// Stage 3: Promote State struct fields to SSA, dead store elimination.
  bool optimize_state = true;

  /// Stage 4: Lower control flow intrinsics (call/ret/jump).
  bool lower_control_flow = true;

  /// Stage 5: Recover calling conventions and eliminate State struct.
  /// (Not yet implemented — future stage)
  bool recover_abi = false;

  /// Stage 6: Deobfuscation passes (MBA, opaque predicates, CFF).
  /// (Not yet implemented — future stage)
  bool deobfuscate = false;

  /// Run standard LLVM cleanup passes between stages.
  bool run_cleanup_passes = true;
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
void buildStateOptimizationPipeline(llvm::FunctionPassManager &FPM);

/// Build only the control flow recovery stage (Stage 4).
void buildControlFlowPipeline(llvm::FunctionPassManager &FPM);

/// Build only the ABI recovery stage (Stage 5).
void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM);

/// Build only the deobfuscation stage (Stage 6).
void buildDeobfuscationPipeline(llvm::FunctionPassManager &FPM);

/// Register all omill function-level analyses.
void registerAnalyses(llvm::FunctionAnalysisManager &FAM);

/// Register all omill module-level analyses.
void registerModuleAnalyses(llvm::ModuleAnalysisManager &MAM);

}  // namespace omill

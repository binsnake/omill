#include "omill/Omill.h"

#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/JumpThreading.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Scalar/LoopDeletion.h>
#include <llvm/Transforms/Scalar/LoopPassManager.h>

#include "omill/Analysis/RemillIntrinsicAnalysis.h"
#include "omill/Passes/CFGRecovery.h"
#include "omill/Passes/DeadStateFlagElimination.h"
#include "omill/Passes/DeadStateStoreElimination.h"
#include "omill/Passes/LowerAtomicIntrinsics.h"
#include "omill/Passes/LowerErrorAndMissing.h"
#include "omill/Passes/LowerFlagIntrinsics.h"
#include "omill/Passes/LowerFunctionCall.h"
#include "omill/Passes/LowerFunctionReturn.h"
#include "omill/Passes/LowerHyperCalls.h"
#include "omill/Passes/LowerJump.h"
#include "omill/Passes/LowerMemoryIntrinsics.h"
#include "omill/Passes/LowerUndefinedIntrinsics.h"
#include "omill/Passes/MemoryPointerElimination.h"
#include "omill/Passes/PromoteStateToSSA.h"
#include "omill/Passes/RecoverFunctionSignatures.h"
#include "omill/Passes/RecoverStackFrame.h"
#include "omill/Passes/EliminateStateStruct.h"
#include "omill/Passes/RemoveBarriers.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/HashImportAnnotation.h"
#include "omill/Passes/ResolveLazyImports.h"
#include "omill/Passes/LowerResolvedDispatchCalls.h"
#include "omill/Passes/FoldProgramCounter.h"
#include "omill/Passes/OutlineConstantStackData.h"
#include "omill/Passes/ResolveIATCalls.h"

namespace omill {

static void addCleanupPasses(llvm::FunctionPassManager &FPM) {
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::DCEPass());
  FPM.addPass(llvm::SimplifyCFGPass());
}

void buildIntrinsicLoweringPipeline(llvm::FunctionPassManager &FPM) {
  // Order matters: flags first (expose SSA values), barriers (unblock opts),
  // then memory (biggest IR change), atomics, hypercalls.
  FPM.addPass(LowerFlagIntrinsicsPass());
  FPM.addPass(RemoveBarriersPass());
  FPM.addPass(LowerMemoryIntrinsicsPass());
  FPM.addPass(LowerAtomicIntrinsicsPass());
  FPM.addPass(LowerHyperCallsPass());

  // Cleanup
  addCleanupPasses(FPM);
}

void buildStateOptimizationPipeline(llvm::FunctionPassManager &FPM) {
  // Dead flag elimination first — biggest bang for the buck (~50% stores gone).
  FPM.addPass(DeadStateFlagEliminationPass());
  FPM.addPass(DeadStateStoreEliminationPass());

  // Promote remaining live State fields to SSA.
  FPM.addPass(PromoteStateToSSAPass());
  FPM.addPass(MemoryPointerEliminationPass());

  // Let LLVM finish the job.
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
  FPM.addPass(llvm::EarlyCSEPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::DCEPass());
  FPM.addPass(llvm::SimplifyCFGPass());
  FPM.addPass(llvm::GVNPass());
}

void buildControlFlowPipeline(llvm::FunctionPassManager &FPM) {
  FPM.addPass(LowerErrorAndMissingPass());
  FPM.addPass(LowerFunctionReturnPass());
  FPM.addPass(LowerFunctionCallPass());
  FPM.addPass(LowerJumpPass());
  FPM.addPass(CFGRecoveryPass());

  FPM.addPass(llvm::SimplifyCFGPass());
  FPM.addPass(llvm::JumpThreadingPass());
}

void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM) {
  // Stack frame recovery runs per-function.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(RecoverStackFramePass());
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Signature recovery creates native wrappers; state elimination
  // internalizes the original lifted functions with alwaysinline.
  MPM.addPass(RecoverFunctionSignaturesPass());
  MPM.addPass(EliminateStateStructPass());

  // Inline the lifted functions into their native wrappers, then
  // SROA decomposes the State alloca into individual fields.
  MPM.addPass(llvm::AlwaysInlinerPass());
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    // Safety net: remove any remaining dead loops (e.g. PEB-walking loops
    // whose results are fully dead after State struct elimination).
    FPM.addPass(llvm::createFunctionToLoopPassAdaptor(llvm::LoopDeletionPass()));
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
}

// Debug: dump function IR at pipeline stage
struct DebugDumpPass : public llvm::PassInfoMixin<DebugDumpPass> {
  std::string tag_;
  DebugDumpPass(std::string tag) : tag_(std::move(tag)) {}
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &) {
    if (F.getName().starts_with("sub_")) {
      std::error_code ec;
      std::string filename = "debug_" + tag_ + "_" + F.getName().str() + ".ll";
      llvm::raw_fd_ostream os(filename, ec, llvm::sys::fs::OF_None);
      if (!ec) F.print(os);
    }
    return llvm::PreservedAnalyses::all();
  }
};

void buildDeobfuscationPipeline(llvm::FunctionPassManager &FPM) {
  FPM.addPass(DebugDumpPass("00_pre_deobf"));
  // Recover stack frame: convert inttoptr(RSP+offset) to alloca GEPs.
  FPM.addPass(RecoverStackFramePass());
  FPM.addPass(DebugDumpPass("01_post_stack"));
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(DebugDumpPass("02_post_sroa"));

  FPM.addPass(ConstantMemoryFoldingPass());
  // LLVM cleanup to fold constants exposed by memory folding.
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::GVNPass());
  FPM.addPass(llvm::DCEPass());
  FPM.addPass(DebugDumpPass("03_post_gvn"));
  // Promote stack allocas with all-constant stores to global constants.
  // After xorstr folding, decrypted strings are constant stores to allocas;
  // outlining them enables further simplification and cleaner output.
  FPM.addPass(OutlineConstantStackDataPass());
  // Hash import annotation (uses the now-folded constants).
  FPM.addPass(HashImportAnnotationPass());
  // Replace lazy_importer resolution with direct import references.
  FPM.addPass(ResolveLazyImportsPass());
  // Lower resolved dispatch_calls to native Win64 ABI calls so State
  // no longer escapes, enabling SROA and dead loop elimination.
  FPM.addPass(LowerResolvedDispatchCallsPass());
  // Clean up dead PEB-walking loop after import resolution.
  FPM.addPass(llvm::ADCEPass());
  FPM.addPass(llvm::SimplifyCFGPass());
}

void buildPipeline(llvm::ModulePassManager &MPM, const PipelineOptions &opts) {
  // Phase 0: Inline remill's alwaysinline semantic functions so that
  // subsequent passes can see through them.
  MPM.addPass(llvm::AlwaysInlinerPass());

  // Phase 1: Intrinsic Lowering
  if (opts.lower_intrinsics) {
    llvm::FunctionPassManager FPM;
    buildIntrinsicLoweringPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 2: State Optimization
  if (opts.optimize_state) {
    llvm::FunctionPassManager FPM;
    buildStateOptimizationPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 3: Control Flow Recovery
  if (opts.lower_control_flow) {
    llvm::FunctionPassManager FPM;
    buildControlFlowPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 3.5: Fold program_counter to a constant and resolve IAT-indirect
  // dispatch_calls before ABI recovery eliminates program_counter.
  {
    MPM.addPass(llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(FoldProgramCounterPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(ResolveIATCallsPass());
    FPM.addPass(LowerResolvedDispatchCallsPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 4: ABI Recovery
  if (opts.recover_abi) {
    buildABIRecoveryPipeline(MPM);
  }

  // Phase 5: Deobfuscation (after ABI recovery for max constant visibility)
  if (opts.deobfuscate) {
    // Ensure BinaryMemoryAnalysis is cached before function passes need it.
    MPM.addPass(llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    buildDeobfuscationPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Late lowering: undefined values (after DCE removed most of them)
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(LowerUndefinedIntrinsicsPass());
    if (opts.run_cleanup_passes) {
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
    }
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Global cleanup
  MPM.addPass(llvm::GlobalDCEPass());
}

void registerAnalyses(llvm::FunctionAnalysisManager &FAM) {
  FAM.registerPass([&] { return RemillIntrinsicAnalysis(); });
}

void registerModuleAnalyses(llvm::ModuleAnalysisManager &MAM) {
  MAM.registerPass([&] { return CallingConventionAnalysis(); });
  MAM.registerPass([&] { return BinaryMemoryAnalysis(); });
}

}  // namespace omill

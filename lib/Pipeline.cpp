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
#include <llvm/Transforms/IPO/Inliner.h>
#include <llvm/Transforms/IPO/SCCP.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/LoopDeletion.h>
#include <llvm/Transforms/Scalar/LoopPassManager.h>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Analysis/RemillIntrinsicAnalysis.h"
#include "omill/Passes/CFGRecovery.h"
#include "omill/Passes/OptimizeState.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Passes/ResolveForcedExceptions.h"
#include "omill/Passes/MemoryPointerElimination.h"
#include "omill/Passes/RecoverFunctionSignatures.h"
#include "omill/Passes/RefineFunctionSignatures.h"
#include "omill/Passes/RecoverStackFrame.h"
#include "omill/Passes/RecoverStackFrameTypes.h"
#include "omill/Passes/EliminateStateStruct.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/HashImportAnnotation.h"
#include "omill/Passes/ResolveLazyImports.h"
#include "omill/Passes/FoldProgramCounter.h"
#include "omill/Passes/SimplifyVectorReassembly.h"
#include "omill/Passes/OutlineConstantStackData.h"
#include "omill/Passes/RecoverGlobalTypes.h"
#include "omill/Passes/ResolveIATCalls.h"
#include "omill/Passes/ResolveAndLowerControlFlow.h"
#include "omill/Passes/InterProceduralConstProp.h"
#include "omill/Passes/IterativeTargetResolution.h"
#include "omill/Passes/EliminateDeadPaths.h"
#include "omill/Passes/RewriteLiftedCallsToNative.h"
#if OMILL_ENABLE_Z3
#include "omill/Passes/Z3DispatchSolver.h"
#endif
#if OMILL_ENABLE_SIMPLIFIER
#include "omill/Passes/SimplifyMBA.h"
#endif

namespace omill {

static void addCleanupPasses(llvm::FunctionPassManager &FPM) {
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::DCEPass());
  FPM.addPass(llvm::SimplifyCFGPass());
}

void buildIntrinsicLoweringPipeline(llvm::FunctionPassManager &FPM) {
  // Order matters: flags first (expose SSA values), barriers (unblock opts),
  // then memory (biggest IR change), atomics, hypercalls.
  FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase1));

  // Cleanup
  addCleanupPasses(FPM);
}

void buildStateOptimizationPipeline(llvm::FunctionPassManager &FPM,
                                    bool deobfuscate) {
  // Recover stack frames before SROA/PromoteStateToSSA eliminates the
  // State-based load chains.  This must run early for both deobfuscation
  // and basic ABI recovery.
  FPM.addPass(RecoverStackFramePass());
  FPM.addPass(RecoverStackFrameTypesPass());
  FPM.addPass(llvm::InstCombinePass());

  // Dead flag/store elimination + promote to SSA.
  FPM.addPass(OptimizeStatePass(OptimizePhases::Early));
  FPM.addPass(MemoryPointerEliminationPass());

  // Let LLVM finish the job.
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));

  if (deobfuscate) {
    // When deobfuscation is enabled, skip GVN here — it would destroy the
    // inttoptr patterns and forward-eliminate xorstr stores.  Phase 5 runs
    // GVN after ConstantMemoryFolding has folded the XOR operations and
    // OutlineConstantStackData has promoted the alloca to a global constant.
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::EarlyCSEPass());
    FPM.addPass(llvm::DCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
  } else {
    FPM.addPass(llvm::EarlyCSEPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::DCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::GVNPass());
  }
}

void buildControlFlowPipeline(llvm::FunctionPassManager &FPM) {
  FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase3));
  FPM.addPass(CFGRecoveryPass());

  FPM.addPass(llvm::SimplifyCFGPass());
  FPM.addPass(llvm::JumpThreadingPass());
  FPM.addPass(EliminateDeadPathsPass());
  FPM.addPass(llvm::SimplifyCFGPass());
}

void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM) {
  // Stack frame recovery runs per-function.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(RecoverStackFramePass());
    FPM.addPass(RecoverStackFrameTypesPass());
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Ensure LiftedFunctionAnalysis is cached — RewriteLiftedCallsToNative needs
  // it to resolve forward-declaration calls (sub_X → sub_X.N definition).
  MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis, llvm::Module>());

  // Signature recovery creates native wrappers; state elimination
  // internalizes the original lifted functions with alwaysinline.
  MPM.addPass(RecoverFunctionSignaturesPass());
  MPM.addPass(RewriteLiftedCallsToNativePass());
  MPM.addPass(EliminateStateStructPass());

  // Inline the lifted functions into their native wrappers.
  // IMPORTANT: defer ALL per-function optimization until after
  // interprocedural inlining.  SEH handlers and CFF resolvers read
  // from parameter-based pointers (DISPATCHER_CONTEXT*, etc.) that
  // can only fold once inlined into the caller where the allocas live.
  // Any optimization here (even InstCombine+SimplifyCFG) would kill
  // the handler/resolver bodies prematurely.
  MPM.addPass(llvm::AlwaysInlinerPass());

  // SROA only: decompose State alloca to expose SSA values for dispatch
  // resolution.  No InstCombine, GVN, or SimplifyCFG yet.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  MPM.addPass(llvm::GlobalDCEPass());

  // Full optimization after inlining native wrappers.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(SimplifyVectorReassemblyPass());
#if OMILL_ENABLE_SIMPLIFIER
    FPM.addPass(SimplifyMBAPass());
#endif
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::createFunctionToLoopPassAdaptor(llvm::LoopDeletionPass()));
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
}

void buildDeobfuscationPipeline(llvm::FunctionPassManager &FPM) {
  // Recover stack frame: convert inttoptr(RSP+offset) to alloca GEPs.
  FPM.addPass(RecoverStackFramePass());
  FPM.addPass(RecoverStackFrameTypesPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(SimplifyVectorReassemblyPass());
  FPM.addPass(OptimizeStatePass(OptimizePhases::RedundantBytes));
#if OMILL_ENABLE_SIMPLIFIER
  FPM.addPass(SimplifyMBAPass());
  FPM.addPass(llvm::InstCombinePass());
#endif

  FPM.addPass(ConstantMemoryFoldingPass());
  // Recover string constants from inttoptr(address) patterns.
  FPM.addPass(RecoverGlobalTypesPass());
  // LLVM cleanup to fold constants exposed by memory folding.
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::GVNPass());
  FPM.addPass(SimplifyVectorReassemblyPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(OptimizeStatePass(OptimizePhases::Roundtrip));
  FPM.addPass(llvm::DCEPass());
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
  FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
  // Clean up dead PEB-walking loop after import resolution.
  FPM.addPass(llvm::ADCEPass());
  FPM.addPass(llvm::SimplifyCFGPass());
}

namespace {

/// Strip bodies of remill intrinsic functions before AlwaysInlinerPass.
///
/// Remill's bitcode library defines intrinsic functions like
/// __remill_sync_hyper_call with bodies containing switch statements whose
/// default cases are unreachable.  Remill's semantic functions call these
/// intrinsics with call-site `alwaysinline` attributes.  When LLVM's
/// AlwaysInlinerPass inlines a semantic function, it also force-inlines the
/// intrinsic body (honoring the call-site attribute), embedding the switch
/// with its unreachable default.  If the hyper-call ID doesn't match any
/// switch case, the entire function degenerates to unreachable, eliminating
/// all continuation code.
///
/// Fix: delete intrinsic bodies before inlining so they become opaque
/// declarations.  Our lowering passes (LowerHyperCalls, LowerMemoryIntrinsics,
/// etc.) will replace the calls with proper implementations later.
struct StripRemillIntrinsicBodiesPass
    : llvm::PassInfoMixin<StripRemillIntrinsicBodiesPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &) {
    // Remill intrinsic prefixes to strip.
    static constexpr llvm::StringLiteral prefixes[] = {
        "__remill_sync_hyper_call",
        "__remill_async_hyper_call",
    };

    bool changed = false;
    for (auto &prefix : prefixes) {
      if (auto *F = M.getFunction(prefix)) {
        if (!F->isDeclaration()) {
          F->deleteBody();
          changed = true;
        }
      }
    }
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

}  // namespace

void buildPipeline(llvm::ModulePassManager &MPM, const PipelineOptions &opts) {
  // Phase 0: Strip remill intrinsic bodies to prevent AlwaysInlinerPass from
  // inlining them via call-site alwaysinline attributes.  Their bodies contain
  // switch/unreachable patterns that poison the entire function's control flow.
  MPM.addPass(StripRemillIntrinsicBodiesPass());

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
    // Inline functions before state optimization to ensure stack frames
    // can be recovered interprocedurally (e.g. OLLVM stack passing).
    if (opts.deobfuscate) {
       llvm::InlineParams Params = llvm::getInlineParams(2000); // Aggressive threshold
       MPM.addPass(llvm::ModuleInlinerWrapperPass(Params));
    }

    llvm::FunctionPassManager FPM;
    buildStateOptimizationPipeline(FPM, opts.deobfuscate);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  // Build the lifted function index before control flow passes need it.
  MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis, llvm::Module>());

  // Cache exception info before control flow passes need it.
  MPM.addPass(llvm::RequireAnalysisPass<ExceptionInfoAnalysis, llvm::Module>());

  // Phase 3a: Resolve forced exceptions (UD2/INT3 → handler call).
  // Must run before the remaining control flow passes so the handler's body
  // can be inlined and then processed by LowerFunctionCall/LowerJump.
  if (opts.lower_control_flow) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(ResolveForcedExceptionsPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));

    // Inline exception handlers into their callers.  This is critical:
    // CFF handlers are trampolines that call resolvers.  Without inlining,
    // ABI recovery creates a native wrapper for the handler that drops XMM
    // values (the handler doesn't use XMMs directly), so the resolver's SSE
    // computation gets all-zero XMM inputs and folds to ret 0.
    // Inlining merges the handler body into the caller (which HAS XMM values),
    // preserving the full State across the call chain.
    MPM.addPass(llvm::AlwaysInlinerPass());
    // Remove inlined handler functions so they don't appear as callers in
    // the call graph, which would prevent InterProceduralConstProp from
    // propagating R9 (synthetic DC address) to the resolver.
    MPM.addPass(llvm::GlobalDCEPass());
  }
  // Phase 3b: Remaining control flow recovery.
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
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 3.6: Iterative indirect target resolution.
  if (opts.resolve_indirect_targets) {
    MPM.addPass(
        IterativeTargetResolutionPass(opts.max_resolution_iterations));
  }

  // Phase 3.7: Inter-procedural constant propagation.
  // After InterProceduralConstProp propagates R9 (DISPATCHER_CONTEXT* from
  // SEH resolution) to handler/resolver functions, ConstantMemoryFolding
  // resolves [R9+0x38] → HandlerData from the synthetic binary region.
  if (opts.interprocedural_const_prop || opts.resolve_indirect_targets) {
    MPM.addPass(llvm::RequireAnalysisPass<CallGraphAnalysis, llvm::Module>());
    MPM.addPass(InterProceduralConstPropPass());
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(ConstantMemoryFoldingPass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(ResolveAndLowerControlFlowPass(ResolvePhases::ResolveTargets));
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 4: ABI Recovery
  if (opts.recover_abi) {
    buildABIRecoveryPipeline(MPM);

    // Phase 4 (late): Refine _native function parameter types.
    if (opts.refine_signatures) {
      MPM.addPass(RefineFunctionSignaturesPass());
    }
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
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Undefined));
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

void registerModuleAnalyses(llvm::ModuleAnalysisManager &MAM) {
  MAM.registerPass([&] { return CallGraphAnalysis(); });
  MAM.registerPass([&] { return CallingConventionAnalysis(); });
  MAM.registerPass([&] { return BinaryMemoryAnalysis(); });
  MAM.registerPass([&] { return LiftedFunctionAnalysis(); });
  MAM.registerPass([&] { return ExceptionInfoAnalysis(); });
}

}  // namespace omill

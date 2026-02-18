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

#include <cstdlib>
#include <optional>

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
#include "omill/Passes/InlineJumpTargets.h"
#include "omill/Passes/RewriteLiftedCallsToNative.h"
#if OMILL_ENABLE_Z3
#include "omill/Passes/Z3DispatchSolver.h"
#endif
#if OMILL_ENABLE_SIMPLIFIER
#include "omill/Passes/SimplifyMBA.h"
#endif

namespace omill {

namespace {

bool envDisabled(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0') return false;
  return (v[0] == '1' && v[1] == '\0') ||
         (v[0] == 't' && v[1] == '\0') ||
         (v[0] == 'T' && v[1] == '\0');
}

std::optional<uint32_t> envUint32(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0') return std::nullopt;
  char *end = nullptr;
  unsigned long n = std::strtoul(v, &end, 0);
  if (end == v || (end && *end != '\0')) return std::nullopt;
  return static_cast<uint32_t>(n);
}

bool hasControlTransferLikeCalls(const llvm::Function &F) {
  for (const auto &BB : F) {
    for (const auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) {
        continue;
      }
      auto *callee = CI->getCalledFunction();
      if (!callee) {
        continue;
      }

      auto name = callee->getName();
      if (name == "__remill_jump" || name == "__remill_function_call" ||
          name == "__remill_function_return" ||
          name == "__omill_dispatch_jump" || name == "__omill_dispatch_call") {
        return true;
      }
      if (name.contains_insensitive("jmpi") ||
          name.contains_insensitive("jump") ||
          name.contains_insensitive("function_call") ||
          name.contains_insensitive("function_return")) {
        return true;
      }
    }
  }
  return false;
}

template <typename InnerPass>
struct SkipOnLiftedControlTransferPass
    : llvm::PassInfoMixin<SkipOnLiftedControlTransferPass<InnerPass>> {
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM) {
    // Stack-frame recovery over lifted traces with unresolved transfer helpers
    // can over-rewrite stack-pointer arithmetic and collapse CFGs.
    if (F.getName().starts_with("sub_") && hasControlTransferLikeCalls(F)) {
      return llvm::PreservedAnalyses::all();
    }

    InnerPass P;
    return P.run(F, AM);
  }
};

}  // namespace

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
  if (!envDisabled("OMILL_SKIP_RECOVER_STACK_FRAME")) {
    FPM.addPass(SkipOnLiftedControlTransferPass<RecoverStackFramePass>());
  }
  if (!envDisabled("OMILL_SKIP_RECOVER_STACK_FRAME_TYPES")) {
    FPM.addPass(SkipOnLiftedControlTransferPass<RecoverStackFrameTypesPass>());
  }
  if (!envDisabled("OMILL_SKIP_STATE_PRE_INSTCOMBINE")) {
    FPM.addPass(llvm::InstCombinePass());
  }

  // Dead flag/store elimination + promote to SSA.
  if (!envDisabled("OMILL_SKIP_OPTIMIZE_STATE_EARLY")) {
    uint32_t early_mask = OptimizePhases::Early;
    if (auto mask = envUint32("OMILL_STATE_EARLY_MASK"); mask.has_value()) {
      early_mask = *mask;
    }
    FPM.addPass(OptimizeStatePass(early_mask));
  }
  if (!envDisabled("OMILL_SKIP_MEMORY_POINTER_ELIM")) {
    FPM.addPass(MemoryPointerEliminationPass());
  }

  // Let LLVM finish the job.
  if (!envDisabled("OMILL_SKIP_STATE_SROA")) {
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
  }

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
  if (!envDisabled("OMILL_SKIP_CF_PHASE3_LOWER")) {
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase3));
  }
  // GVN + InstCombine after LowerJump: GVN forwards stores to State GEP
  // loads (e.g. R10D base register in jump table patterns), enabling
  // RecoverTables to match dispatch_jump targets that reference State
  // registers.  InstCombine propagates the forwarded constants.
  if (!envDisabled("OMILL_SKIP_CF_PRE_RESOLVE_GVN")) {
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::InstCombinePass());
  }
  // Recover table-based dispatch_jump targets while fallback blocks still
  // have the canonical "call __omill_dispatch_jump; ret" shape produced by
  // Phase 3 lowering. Later CFG cleanup can obscure this pattern.
  if (!envDisabled("OMILL_SKIP_CF_EARLY_RESOLVE_TABLES")) {
    FPM.addPass(ResolveAndLowerControlFlowPass(
        ResolvePhases::ResolveTargets |
        ResolvePhases::RecoverTables |
        ResolvePhases::SymbolicSolve));
  }
  if (!envDisabled("OMILL_SKIP_CF_CFG_RECOVERY")) {
    FPM.addPass(CFGRecoveryPass());
  }

  if (!envDisabled("OMILL_SKIP_CF_SIMPLIFYCFG_1")) {
    FPM.addPass(llvm::SimplifyCFGPass());
  }
  if (!envDisabled("OMILL_SKIP_CF_JUMP_THREADING")) {
    FPM.addPass(llvm::JumpThreadingPass());
  }
  if (!envDisabled("OMILL_SKIP_ELIMINATE_DEAD_PATHS")) {
    FPM.addPass(EliminateDeadPathsPass());
  }
  if (!envDisabled("OMILL_SKIP_CF_SIMPLIFYCFG_2")) {
    FPM.addPass(llvm::SimplifyCFGPass());
  }
}

void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM) {
  // Stack frame recovery runs per-function.
  {
    llvm::FunctionPassManager FPM;
    // Stack frame recovery already runs in state optimization.
    // Re-running it here can over-rewrite recovered stack-pointer arithmetic
    // in complex lifted functions and collapse control flow.
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Ensure LiftedFunctionAnalysis is cached — RewriteLiftedCallsToNative needs
  // it to resolve forward-declaration calls (sub_X → sub_X.N definition).
  MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis, llvm::Module>());

  // Signature recovery creates native wrappers; state elimination
  // internalizes the original lifted functions with alwaysinline.
  if (!envDisabled("OMILL_SKIP_ABI_RECOVER_SIGNATURES")) {
    MPM.addPass(RecoverFunctionSignaturesPass());
    MPM.addPass(RewriteLiftedCallsToNativePass());
    MPM.addPass(EliminateStateStructPass());
  }

  // Inline the lifted functions into their native wrappers.
  // IMPORTANT: defer ALL per-function optimization until after
  // interprocedural inlining.  SEH handlers and CFF resolvers read
  // from parameter-based pointers (DISPATCHER_CONTEXT*, etc.) that
  // can only fold once inlined into the caller where the allocas live.
  // Any optimization here (even InstCombine+SimplifyCFG) would kill
  // the handler/resolver bodies prematurely.
  if (!envDisabled("OMILL_SKIP_ABI_ALWAYS_INLINE")) {
    MPM.addPass(llvm::AlwaysInlinerPass());
  }

  // SROA only: decompose State alloca to expose SSA values for dispatch
  // resolution.  No InstCombine, GVN, or SimplifyCFG yet.
  if (!envDisabled("OMILL_SKIP_ABI_SROA")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  if (!envDisabled("OMILL_SKIP_ABI_GLOBAL_DCE")) {
    MPM.addPass(llvm::GlobalDCEPass());
  }

  // Full optimization after inlining native wrappers.
  if (!envDisabled("OMILL_SKIP_ABI_FINAL_OPT")) {
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
  if (!envDisabled("OMILL_SKIP_DEOBF_RECOVER_STACK")) {
    FPM.addPass(SkipOnLiftedControlTransferPass<RecoverStackFramePass>());
    FPM.addPass(SkipOnLiftedControlTransferPass<RecoverStackFrameTypesPass>());
  }
  if (!envDisabled("OMILL_SKIP_DEOBF_PRE_SROA")) {
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(SimplifyVectorReassemblyPass());
  }
  if (!envDisabled("OMILL_SKIP_DEOBF_OPT_STATE_REDUNDANT")) {
    FPM.addPass(OptimizeStatePass(OptimizePhases::RedundantBytes));
  }
#if OMILL_ENABLE_SIMPLIFIER
  if (!envDisabled("OMILL_SKIP_DEOBF_SIMPLIFY_MBA")) {
    FPM.addPass(SimplifyMBAPass());
    FPM.addPass(llvm::InstCombinePass());
  }
#endif

  if (!envDisabled("OMILL_SKIP_DEOBF_CONST_FOLD")) {
    FPM.addPass(ConstantMemoryFoldingPass());
    // Recover string constants from inttoptr(address) patterns.
    FPM.addPass(RecoverGlobalTypesPass());
  }
  if (!envDisabled("OMILL_SKIP_DEOBF_POST_CONST_CLEANUP")) {
    // LLVM cleanup to fold constants exposed by memory folding.
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(SimplifyVectorReassemblyPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(OptimizeStatePass(OptimizePhases::Roundtrip));
    FPM.addPass(llvm::DCEPass());
  }
  // Promote stack allocas with all-constant stores to global constants.
  // After xorstr folding, decrypted strings are constant stores to allocas;
  // outlining them enables further simplification and cleaner output.
  if (!envDisabled("OMILL_SKIP_DEOBF_OUTLINE_CONST_STACK")) {
    FPM.addPass(OutlineConstantStackDataPass());
  }
  // Hash import annotation (uses the now-folded constants).
  if (!envDisabled("OMILL_SKIP_DEOBF_HASH_IMPORTS")) {
    FPM.addPass(HashImportAnnotationPass());
  }
  // Replace lazy_importer resolution with direct import references.
  if (!envDisabled("OMILL_SKIP_DEOBF_RESOLVE_LAZY")) {
    FPM.addPass(ResolveLazyImportsPass());
  }
  // Lower resolved dispatch_calls to native Win64 ABI calls so State
  // no longer escapes, enabling SROA and dead loop elimination.
  if (!envDisabled("OMILL_SKIP_DEOBF_RESOLVED_DISPATCH")) {
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
  }
  // Clean up dead PEB-walking loop after import resolution.
  if (!envDisabled("OMILL_SKIP_DEOBF_FINAL_CLEANUP")) {
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
  }
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

/// Internalize all functions/globals that are not lifted code or remill
/// intrinsics.  After AlwaysInlinerPass inlines the ~2000 semantic functions
/// from the semantics module, their bodies are dead but retain external
/// linkage — so GlobalDCE won't touch them.  This pass marks them internal,
/// allowing the subsequent GlobalDCE to strip them and all transitively-dead
/// global constants (CRC tables, SHA-256 round constants, etc.).
struct InternalizeRemillSemanticsPass
    : llvm::PassInfoMixin<InternalizeRemillSemanticsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &) {
    bool changed = false;

    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      if (F.hasLocalLinkage()) continue;

      auto name = F.getName();
      // Keep lifted functions and remill intrinsics.
      if (name.starts_with("sub_") || name.starts_with("block_") ||
          name.starts_with("__remill_"))
        continue;

      F.setLinkage(llvm::GlobalValue::InternalLinkage);
      changed = true;
    }

    for (auto &GV : M.globals()) {
      if (GV.isDeclaration()) continue;
      if (GV.hasLocalLinkage()) continue;

      auto name = GV.getName();
      // Keep State type metadata and remill markers.
      if (name.starts_with("__remill_") || name.starts_with("llvm."))
        continue;

      GV.setLinkage(llvm::GlobalValue::InternalLinkage);
      changed = true;
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

  // Phase 0 cleanup: Internalize dead semantic functions/globals so GlobalDCE
  // can remove them.  The semantics module has ~2000 instruction definitions
  // with external linkage that GlobalDCE alone won't touch.
  MPM.addPass(InternalizeRemillSemanticsPass());
  MPM.addPass(llvm::GlobalDCEPass());

  // Phase 0.5: Resolve trace stubs and inline jump-exiting callees.
  // Must run BEFORE Phase 1 so that block_<hex> names (from jump table
  // target discovery during lifting) survive — SimplifyCFG in Phase 1
  // cleanup merges blocks and destroys those names.  __remill_jump is
  // still present at this point (not lowered until Phase 3).
  if (opts.deobfuscate) {
    MPM.addPass(InlineJumpTargetsPass());
  }

  // Phase 1: Intrinsic Lowering
  if (opts.lower_intrinsics) {
    llvm::FunctionPassManager FPM;
    buildIntrinsicLoweringPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 2: State Optimization
  if (opts.optimize_state) {
    if (opts.deobfuscate && !envDisabled("OMILL_SKIP_STATE_MODULE_INLINER")) {
       llvm::InlineParams Params = llvm::getInlineParams(2000); // Aggressive threshold
       MPM.addPass(llvm::ModuleInlinerWrapperPass(Params));
    }

    llvm::FunctionPassManager FPM;
    buildStateOptimizationPipeline(FPM, opts.deobfuscate);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // In staged test flows, stop here to avoid running later phases on
  // partially-lowered IR.
  if (opts.stop_after_state_optimization) {
    return;
  }
  // Build the lifted function index before control flow passes need it.
  MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis, llvm::Module>());

  // Cache exception info before control flow passes need it.
  MPM.addPass(llvm::RequireAnalysisPass<ExceptionInfoAnalysis, llvm::Module>());

  // ResolveAndLowerControlFlowPass (run in Phase 3) can use the binary map
  // to recover jump tables from dispatch_jump targets.
  if (opts.lower_control_flow) {
    MPM.addPass(
        llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
  }

  // Phase 3a: Resolve forced exceptions (UD2/INT3 → handler call).
  // Must run before the remaining control flow passes so the handler's body
  // can be inlined and then processed by LowerFunctionCall/LowerJump.
  if (opts.lower_control_flow) {
    llvm::FunctionPassManager FPM;
    if (!envDisabled("OMILL_SKIP_RESOLVE_FORCED_EXCEPTIONS")) {
      FPM.addPass(ResolveForcedExceptionsPass());
    }
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));

    // Inline exception handlers into their callers.  This is critical:
    // CFF handlers are trampolines that call resolvers.  Without inlining,
    // ABI recovery creates a native wrapper for the handler that drops XMM
    // values (the handler doesn't use XMMs directly), so the resolver's SSE
    // computation gets all-zero XMM inputs and folds to ret 0.
    // Inlining merges the handler body into the caller (which HAS XMM values),
    // preserving the full State across the call chain.
    if (!envDisabled("OMILL_SKIP_CF_HANDLER_INLINE")) {
      MPM.addPass(llvm::AlwaysInlinerPass());
    }
    // Remove inlined handler functions so they don't appear as callers in
    // the call graph, which would prevent InterProceduralConstProp from
    // propagating R9 (synthetic DC address) to the resolver.
    if (!envDisabled("OMILL_SKIP_CF_HANDLER_GDCE")) {
      MPM.addPass(llvm::GlobalDCEPass());
    }
  }
  // Phase 3b: Remaining control flow recovery.
  if (opts.lower_control_flow) {
    llvm::FunctionPassManager FPM;
    buildControlFlowPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Phase 3.5: Fold program_counter to a constant and resolve IAT-indirect
  // dispatch_calls before ABI recovery eliminates program_counter.
  if (!envDisabled("OMILL_SKIP_PHASE35")) {
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
    if (!envDisabled("OMILL_SKIP_UNDEFINED_LOWER")) {
      FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Undefined));
    }
    if (opts.run_cleanup_passes && !envDisabled("OMILL_SKIP_LATE_CLEANUP")) {
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

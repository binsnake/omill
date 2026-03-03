#include "omill/Omill.h"

#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/IntrinsicInst.h>
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
#include <llvm/Transforms/Scalar/LoopRotation.h>
#include <llvm/Transforms/Scalar/LoopUnrollPass.h>
#include <llvm/Transforms/Scalar/LoopPassManager.h>

#include <chrono>
#include <cstdlib>
#include <optional>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Analysis/RemillIntrinsicAnalysis.h"
#include "omill/Analysis/SegmentsAA.h"
#include "omill/Passes/CFGRecovery.h"
#include "omill/Passes/ControlFlowUnflattener.h"
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
#include "omill/Passes/DeadStateStoreDSE.h"
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
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/Passes/IterativeBlockDiscovery.h"
#include "omill/Passes/MergeBlockFunctions.h"
#include "omill/Passes/JumpTableConcretizer.h"
#include "omill/Passes/IndirectCallResolver.h"
#include "omill/Passes/JunkInstructionRemover.h"
#include "omill/Passes/KnownIndexSelect.h"
#include "omill/Passes/MemoryCoalesce.h"
#include "omill/Passes/PartialOverlapDSE.h"
#include "omill/Passes/PointersHoisting.h"
#include "omill/Passes/SynthesizeFlags.h"
#include "omill/Passes/StackConcretization.h"
#include "omill/Passes/TypeRecovery.h"
#include "omill/Passes/VMHandlerInliner.h"
#include "omill/Analysis/VMHandlerGraph.h"
#include "omill/Passes/VMDispatchResolution.h"
#include "omill/Passes/VMHashElimination.h"
#include "omill/Passes/RewriteLiftedCallsToNative.h"
#if OMILL_ENABLE_Z3
#include "omill/Passes/Z3DispatchSolver.h"
#endif
#if OMILL_ENABLE_SIMPLIFIER
#include "omill/Passes/SimplifyMBA.h"
#endif
#include "omill/Passes/CollapseRemillSHRSwitch.h"
#include "omill/Passes/ExpandI128DivRem.h"
#include "omill/Passes/StripCompilerUsed.h"
#include "omill/Passes/EliminateDeadTraceCounters.h"
#include "omill/Passes/MergeBytePhis.h"
#include "omill/Passes/RecoverAllocaPointers.h"

namespace omill {

namespace {

/// Lightweight pass that prints a phase label + elapsed time + function count.
/// Gated by OMILL_PHASE_TIMING env var to avoid noise in normal operation.
struct PhaseMarkerPass : llvm::PassInfoMixin<PhaseMarkerPass> {
  std::string label_;
  using Clock = std::chrono::steady_clock;
  static Clock::time_point &origin() {
    static auto t0 = Clock::now();
    return t0;
  }
  explicit PhaseMarkerPass(llvm::StringRef label) : label_(label) {}
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                  Clock::now() - origin())
                  .count();
    llvm::errs() << "[omill] " << label_ << "  +" << ms << "ms  ("
                 << M.size() << " functions)\n";
    return llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

/// Add a phase marker only if OMILL_PHASE_TIMING is set.
void addPhaseMarker(llvm::ModulePassManager &MPM, llvm::StringRef label) {
  static bool enabled = (std::getenv("OMILL_PHASE_TIMING") != nullptr);
  if (enabled)
    MPM.addPass(PhaseMarkerPass(label));
}

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

/// Module pass that runs an FPM only on functions matching a predicate.
/// Avoids iterating the entire module when only a few functions need work.
template <typename Pred>
struct ScopedFunctionPassAdaptor
    : llvm::PassInfoMixin<ScopedFunctionPassAdaptor<Pred>> {
  llvm::FunctionPassManager FPM;
  Pred predicate;
  ScopedFunctionPassAdaptor(llvm::FunctionPassManager FPM, Pred pred)
      : FPM(std::move(FPM)), predicate(std::move(pred)) {}
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &MAM) {
    auto &FAM =
        MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration() || !predicate(F))
        continue;
      auto PA = FPM.run(F, FAM);
      if (!PA.areAllPreserved()) {
        changed = true;
        FAM.invalidate(F, PA);
      }
    }
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

template <typename Pred>
ScopedFunctionPassAdaptor<Pred> createScopedFPM(llvm::FunctionPassManager FPM,
                                                 Pred pred) {
  return ScopedFunctionPassAdaptor<Pred>(std::move(FPM), std::move(pred));
}

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
  if (!envDisabled("OMILL_SKIP_STACK_CONCRETIZATION")) {
    FPM.addPass(SkipOnLiftedControlTransferPass<StackConcretizationPass>());
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
    FPM.addPass(llvm::SimplifyCFGPass());
  } else {
    FPM.addPass(llvm::EarlyCSEPass());
    FPM.addPass(llvm::InstCombinePass());
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

namespace {

// ABI helper: fold direct calls to functions that are exactly
// `ret <constant>`, exposing concrete jump targets in callers.
struct FoldCallsToConstantReturnPass
    : llvm::PassInfoMixin<FoldCallsToConstantReturnPass> {
  static bool pointsToOnlyLocalAllocas(const llvm::Value *Ptr) {
    if (!Ptr) {
      return false;
    }

    llvm::SmallVector<llvm::Value *, 4> objs;
    if (!llvm::getUnderlyingObjectsForCodeGen(Ptr, objs)) {
      auto *obj = llvm::getUnderlyingObject(Ptr);
      return llvm::isa<llvm::AllocaInst>(obj);
    }

    if (objs.empty()) {
      return false;
    }
    for (auto *obj : objs) {
      obj = obj->stripPointerCasts();
      if (!llvm::isa<llvm::AllocaInst>(obj)) {
        return false;
      }
    }
    return true;
  }

  static llvm::Constant *getFoldableConstantReturn(llvm::Function *F) {
    if (!F || F->isDeclaration() || F->getReturnType()->isVoidTy())
      return nullptr;

    llvm::Constant *ret_const = nullptr;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        if (auto *Ret = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
          auto *C = llvm::dyn_cast<llvm::Constant>(Ret->getReturnValue());
          if (!C)
            return nullptr;
          if (!ret_const) {
            ret_const = C;
          } else if (ret_const != C) {
            return nullptr;
          }
          continue;
        }

        if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (SI->isVolatile())
            return nullptr;
          if (!pointsToOnlyLocalAllocas(SI->getPointerOperand())) {
            return nullptr;
          }
          continue;
        }

        if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          if (LI->isVolatile())
            return nullptr;
          if (!pointsToOnlyLocalAllocas(LI->getPointerOperand())) {
            return nullptr;
          }
          continue;
        }

        if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(&I)) {
          switch (II->getIntrinsicID()) {
            case llvm::Intrinsic::assume:
            case llvm::Intrinsic::lifetime_start:
            case llvm::Intrinsic::lifetime_end:
            case llvm::Intrinsic::experimental_noalias_scope_decl:
            case llvm::Intrinsic::stacksave:
            case llvm::Intrinsic::stackrestore:
              continue;
            case llvm::Intrinsic::memset:
            case llvm::Intrinsic::memset_inline: {
              auto *MI = llvm::cast<llvm::MemSetInst>(II);
              if (!pointsToOnlyLocalAllocas(MI->getDest())) {
                return nullptr;
              }
              continue;
            }
            case llvm::Intrinsic::memcpy:
            case llvm::Intrinsic::memcpy_inline:
            case llvm::Intrinsic::memmove: {
              auto *MTI = llvm::cast<llvm::MemTransferInst>(II);
              if (!pointsToOnlyLocalAllocas(MTI->getDest()) ||
                  !pointsToOnlyLocalAllocas(MTI->getSource())) {
                return nullptr;
              }
              continue;
            }
            default:
              return nullptr;
          }
        }

        if (llvm::isa<llvm::AtomicRMWInst>(&I) ||
            llvm::isa<llvm::AtomicCmpXchgInst>(&I) ||
            llvm::isa<llvm::FenceInst>(&I) ||
            llvm::isa<llvm::CallBase>(&I)) {
          return nullptr;
        }
      }
    }

    return ret_const;
  }

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    llvm::SmallVector<std::pair<llvm::Function *, llvm::Constant *>, 32>
        foldable_fns;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (auto *C = getFoldableConstantReturn(&F)) {
        foldable_fns.push_back({&F, C});
      }
    }

    struct Replacement {
      llvm::CallInst *call;
      llvm::Constant *value;
    };
    llvm::SmallVector<Replacement, 32> replacements;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->getType()->isVoidTy())
            continue;
          auto *Callee = CI->getCalledFunction();
          if (!Callee)
            continue;
          auto *C = getFoldableConstantReturn(Callee);
          if (!C || C->getType() != CI->getType())
            continue;
          replacements.push_back({CI, C});
        }
      }
    }

    bool changed = false;

    for (auto &R : replacements) {
      R.call->replaceAllUsesWith(R.value);
      R.call->eraseFromParent();
      changed = true;
    }

    for (auto &[F, C] : foldable_fns) {
      if (F->empty())
        continue;

      bool already_canonical = false;
      if (F->size() == 1) {
        auto &BB = F->front();
        if (BB.size() == 1) {
          if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator())) {
            already_canonical = (RI->getReturnValue() == C);
          }
        }
      }
      if (already_canonical)
        continue;

      F->deleteBody();
      auto *entry = llvm::BasicBlock::Create(F->getContext(), "entry", F);
      llvm::ReturnInst::Create(F->getContext(), C, entry);
      changed = true;
    }

    if (!changed)
      return llvm::PreservedAnalyses::all();
    return llvm::PreservedAnalyses::none();
  }

  static bool isRequired() { return true; }
};

}  // namespace

void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM) {
  addPhaseMarker(MPM, "ABI: start");
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

  addPhaseMarker(MPM, "ABI: inline lifted → native");
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

  // Inlining lifted functions into _native wrappers can re-introduce
  // dispatch_call/dispatch_jump artifacts. Rewrite again so wrappers don't
  // keep State alive due late-emitted dispatch shims.
  if (!envDisabled("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE")) {
    MPM.addPass(RewriteLiftedCallsToNativePass());
  }

  // Eliminate dead stores to volatile State fields, decompose the State
  // alloca via SROA, and expand i128 div/rem — all in a single traversal.
  {
    llvm::FunctionPassManager FPM;
    if (!envDisabled("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE"))
      FPM.addPass(DeadStateStoreDSEPass());
    if (!envDisabled("OMILL_SKIP_ABI_SROA"))
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    if (!envDisabled("OMILL_SKIP_EXPAND_I128_DIVREM"))
      FPM.addPass(ExpandI128DivRemPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "ABI: GlobalDCE dead originals");
  if (!envDisabled("OMILL_SKIP_ABI_GLOBAL_DCE")) {
    MPM.addPass(llvm::GlobalDCEPass());
  }
  addPhaseMarker(MPM, "ABI: final optimization");
  // Full optimization after inlining native wrappers.
  // SROA already ran above; start with InstCombine on the decomposed SSA.
  if (!envDisabled("OMILL_SKIP_ABI_FINAL_OPT")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(SimplifyVectorReassemblyPass());
    FPM.addPass(CollapseRemillSHRSwitchPass());
#if OMILL_ENABLE_SIMPLIFIER
    FPM.addPass(SimplifyMBAPass());
#endif
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(PointersHoistingPass());
    FPM.addPass(TypeRecoveryPass());
    // NOTE: LoopDeletionPass removed — SCEV's computeShiftCompareExitLimit
    // crashes (SEH 0xC0000005) on lifted modular-exponentiation loops with
    // 128-bit multiply-modulo operations.  ADCE + SimplifyCFG below handle
    // dead code removal adequately without it.
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // After per-function cleanup, some native helpers collapse to a constant
  // return. Fold direct calls to those helpers in their callers.
  if (!envDisabled("OMILL_SKIP_ABI_FOLD_CONST_RET_CALLS")) {
    MPM.addPass(FoldCallsToConstantReturnPass());
  }

  // Merged cleanup: post-FoldCallsToConstantReturn + dead trace counter
  // elimination in a single module traversal.
  {
    llvm::FunctionPassManager FPM;
    if (!envDisabled("OMILL_SKIP_ABI_FOLD_CONST_RET_CALLS")) {
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::DCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
    }
    if (!envDisabled("OMILL_SKIP_ABI_DEAD_TRACE_COUNTERS")) {
      FPM.addPass(EliminateDeadTraceCountersPass());
      FPM.addPass(MergeBytePhisPass());
    }
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "ABI: inline VM handlers");
  // Interprocedural inlining: inline VM handler _native functions into their
  // callers.  This enables store-to-load forwarding across the call boundary
  // (the caller stores constants to its native_stack, the VM handler reads
  // them via inttoptr(R12 + offset)).  LLVM cannot fold inttoptr(ptrtoint
  // (alloca)+C) to a GEP, so RecoverAllocaPointersPass does it first,
  // unblocking BasicAA / GVN store forwarding.
  if (!envDisabled("OMILL_SKIP_ABI_INLINE_VM_HANDLERS")) {
    // Inline VM handler _native functions into their callers and run
    // cleanup passes.  This entire block is skipped when no VM handler
    // functions exist (e.g. non-VM block-lift mode) to avoid running
    // expensive cleanup passes on the entire module for no benefit.
    struct InlineVMHandlersAndCleanupPass
        : llvm::PassInfoMixin<InlineVMHandlersAndCleanupPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &MAM) {
        // Mark VM handler _native functions for inlining and collect their
        // callers so we only run expensive cleanup on affected functions.
        bool has_vm_handlers = false;
        llvm::DenseSet<llvm::Function *> callers;
        for (auto &F : M) {
          if (!F.hasFnAttribute("omill.vm_handler") ||
              !F.getName().ends_with("_native"))
            continue;
          F.removeFnAttr(llvm::Attribute::NoInline);
          F.addFnAttr(llvm::Attribute::AlwaysInline);
          has_vm_handlers = true;
          for (auto *U : F.users()) {
            if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
              callers.insert(CB->getFunction());
          }
        }
        if (!has_vm_handlers)
          return llvm::PreservedAnalyses::all();

        // Inline the marked functions.
        {
          llvm::ModulePassManager InlineMPM;
          InlineMPM.addPass(llvm::AlwaysInlinerPass());
          InlineMPM.run(M, MAM);
        }

        // Cleanup only on functions that called VM handlers.
        {
          auto &FAM =
              MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                  .getManager();
          llvm::FunctionPassManager FPM;
          FPM.addPass(RecoverAllocaPointersPass());
          FPM.addPass(llvm::GVNPass());
          FPM.addPass(llvm::InstCombinePass());
          FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
          FPM.addPass(llvm::InstCombinePass());
          FPM.addPass(llvm::SimplifyCFGPass());
          FPM.addPass(llvm::GVNPass());
          FPM.addPass(llvm::ADCEPass());
          FPM.addPass(llvm::InstCombinePass());
          FPM.addPass(llvm::SimplifyCFGPass());
          for (auto *F : callers) {
            if (F->isDeclaration())
              continue;
            auto PA = FPM.run(*F, FAM);
            FAM.invalidate(*F, PA);
          }
        }

        {
          llvm::ModulePassManager CleanMPM;
          CleanMPM.addPass(llvm::GlobalDCEPass());
          CleanMPM.run(M, MAM);
        }

        return llvm::PreservedAnalyses::none();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(InlineVMHandlersAndCleanupPass{});
  }
  addPhaseMarker(MPM, "ABI: final cleanup");
  // Strip @llvm.compiler.used and run GlobalDCE to remove dead ISEL stubs.
  if (!envDisabled("OMILL_SKIP_STRIP_COMPILER_USED")) {
    MPM.addPass(StripCompilerUsedPass());
    MPM.addPass(llvm::GlobalDCEPass());
  }
}

void buildDeobfuscationPipeline(llvm::FunctionPassManager &FPM) {
  // Recover stack frame: convert inttoptr(RSP+offset) to alloca GEPs.
  if (!envDisabled("OMILL_SKIP_DEOBF_RECOVER_STACK")) {
    FPM.addPass(SkipOnLiftedControlTransferPass<RecoverStackFramePass>());
    FPM.addPass(SkipOnLiftedControlTransferPass<RecoverStackFrameTypesPass>());
  }
  if (!envDisabled("OMILL_SKIP_DEOBF_STACK_CONCRETIZATION")) {
    FPM.addPass(SkipOnLiftedControlTransferPass<StackConcretizationPass>());
  }
  if (!envDisabled("OMILL_SKIP_DEOBF_PRE_SROA")) {
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(SimplifyVectorReassemblyPass());
  }
  if (!envDisabled("OMILL_SKIP_DEOBF_JUNK_REMOVAL")) {
    FPM.addPass(JunkInstructionRemoverPass());
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
  if (!envDisabled("OMILL_SKIP_DEOBF_MEMORY_COALESCE")) {
    FPM.addPass(MemoryCoalescePass());
    FPM.addPass(PartialOverlapDSEPass());
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
  // Control-flow unflattening: after MBA simplification, constant folding,
  // and dead-path elimination have resolved state variable computations.
  if (!envDisabled("OMILL_SKIP_DEOBF_CFF_UNFLATTEN")) {
    FPM.addPass(ControlFlowUnflattenerPass());
    FPM.addPass(llvm::SimplifyCFGPass());
  }
  // Unroll small constant-trip-count decrypt loops (e.g. CW_STR XOR cipher)
  // so their body stores become straight-line code.  GVN then forwards
  // entry-block stores to the unrolled loads, enabling InstCombine to fold
  // XOR operations to constants — making all stores constant and eliminating
  // loads so OutlineConstantStackData can promote the alloca to a global.
  if (!envDisabled("OMILL_SKIP_DEOBF_LOOP_UNROLL")) {
    FPM.addPass(llvm::createFunctionToLoopPassAdaptor(llvm::LoopRotatePass()));
    FPM.addPass(llvm::LoopUnrollPass(
        llvm::LoopUnrollOptions().setFullUnrollMaxCount(256)));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::InstCombinePass());
  }
  // Promote stack allocas with all-constant stores to global constants.
  // After xorstr folding (and now loop unrolling), decrypted strings are
  // constant stores to allocas; outlining enables further simplification.
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
    FPM.addPass(KnownIndexSelectPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(TypeRecoveryPass());
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

/// Promote semantic function linkage from internal to external.
/// Anonymous-namespace semantic functions have internal linkage by
/// construction.  After Phase 0's AlwaysInlinerPass inlines them into
/// lifted traces, they have no callers.  Without this promotion,
/// SCCP/IPSCCP in later passes (Phase 2 ModuleInlinerWrapperPass)
/// sees "internal, no callers" and replaces their bodies with
/// unreachable.  External linkage makes them opaque to SCCP.
struct ExternalizeRemillSemanticsPass
    : llvm::PassInfoMixin<ExternalizeRemillSemanticsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      if (!F.hasLocalLinkage()) continue;
      auto name = F.getName();
      // Skip lifted code and remill intrinsics.
      if (name.starts_with("sub_") || name.starts_with("block_") ||
          name.starts_with("__remill_") || name.starts_with("__omill_"))
        continue;
      F.setLinkage(llvm::GlobalValue::ExternalLinkage);
      changed = true;
    }
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

/// After Phase 0's AlwaysInlinerPass has inlined all semantic functions into
/// existing lifted traces, protect the semantic function bodies from Phase 2's
/// destructive optimizations (SROA, InstCombine, SimplifyCFG, GVN).  These
/// passes run via createModuleToFunctionPassAdaptor on ALL functions and will
/// collapse semantic function bodies to unreachable.  The `optnone` attribute
/// makes LLVM skip optimization passes for these functions.
///
/// Phase 3.6's IterativeTargetResolution removes the protection before inlining
/// semantics into newly-discovered VM handler functions.
struct ProtectRemillSemanticsPass
    : llvm::PassInfoMixin<ProtectRemillSemanticsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      auto name = F.getName();
      if (name.starts_with("sub_") || name.starts_with("block_") ||
          name.starts_with("__remill_") || name.starts_with("__omill_"))
        continue;
      // Skip if already protected.
      if (F.hasFnAttribute(llvm::Attribute::OptimizeNone)) continue;
      // optnone requires noinline and conflicts with alwaysinline.
      F.removeFnAttr(llvm::Attribute::AlwaysInline);
      F.addFnAttr(llvm::Attribute::NoInline);
      F.addFnAttr(llvm::Attribute::OptimizeNone);
      changed = true;
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
  // Reset the phase timer origin on each pipeline build.
  PhaseMarkerPass::origin() = PhaseMarkerPass::Clock::now();
  addPhaseMarker(MPM, "Phase 0: start");

  // Phase 0: Strip remill intrinsic bodies to prevent AlwaysInlinerPass from
  // inlining them via call-site alwaysinline attributes.  Their bodies contain
  // switch/unreachable patterns that poison the entire function's control flow.
  MPM.addPass(StripRemillIntrinsicBodiesPass());

  // Phase 0: Externalize semantic functions BEFORE AlwaysInliner.
  // The ~2000 semantic functions live in anonymous C++ namespaces and have
  // internal linkage by construction.  AlwaysInlinerPass inlines them into
  // lifted traces, then replaces the original bodies with unreachable
  // (internal + no callers = dead).  Promoting to external prevents this
  // body destruction, keeping the bodies available for VM handler functions
  // discovered later in Phase 3.6.
  MPM.addPass(ExternalizeRemillSemanticsPass());

  // Phase 0: Inline remill's alwaysinline semantic functions so that
  // subsequent passes can see through them.
  MPM.addPass(llvm::AlwaysInlinerPass());

  // Protect semantic function bodies from Phase 2 function-pass optimizations.
  // Phase 3.6 Step 2b restores alwaysinline before inlining into VM handlers.
  MPM.addPass(ProtectRemillSemanticsPass());

  // Phase 0.5: Resolve trace stubs and inline jump-exiting callees.
  // Must run BEFORE Phase 1 so that block_<hex> names (from jump table
  // target discovery during lifting) survive — SimplifyCFG in Phase 1
  // cleanup merges blocks and destroys those names.  __remill_jump is
  // still present at this point (not lowered until Phase 3).
  if (opts.deobfuscate && !opts.use_block_lifting &&
      !envDisabled("OMILL_SKIP_INLINE_JUMP_TARGETS")) {
    MPM.addPass(InlineJumpTargetsPass());
  }

  addPhaseMarker(MPM, "Phase 1: intrinsic lowering");
  // Phase 1: Intrinsic Lowering
  if (opts.lower_intrinsics) {
    llvm::FunctionPassManager FPM;
    buildIntrinsicLoweringPipeline(FPM);
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "Phase 2: state optimization");
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

  // Synthesize flag patterns: after SROA/mem2reg promotes flag values to
  // SSA, recognize xor(SF, OF) patterns and fold to icmp slt.  Follow
  // with InstCombine to fold compound patterns (JGE, JLE, JG).
  if (!envDisabled("OMILL_SKIP_SYNTHESIZE_FLAGS")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(SynthesizeFlagsPass());
    FPM.addPass(llvm::InstCombinePass());
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

  addPhaseMarker(MPM, "Phase 3: control flow");
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

  addPhaseMarker(MPM, "Phase 3.5: fold PC + IAT");
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

  // Phase 3.55: Proactive jump table concretization.
  // Runs after Phase 3.5 has folded program_counter and resolved IAT calls,
  // but before iterative target resolution.  Converts dispatch_jump sites
  // with jump table patterns (base + idx * stride loads from binary memory)
  // into switch instructions.
  if (opts.resolve_indirect_targets || opts.use_block_lifting) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(JumpTableConcretizerPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "Phase 3.56: VM devirtualization");
  // Phase 3.56: VM Devirtualization.
  // Resolve handler dispatch targets via binary graph lookup and eliminate
  // hash integrity checks.  Must run after Phase 3 has lowered __remill_jump
  // to __omill_dispatch_jump and before Phase 3.6 resolves them.
  if (opts.vm_devirtualize) {
    // Resolve opaque dispatch targets using the handler graph.
    MPM.addPass(VMDispatchResolutionPass());

    // Lower resolved dispatch targets to direct calls.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(
          LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }

    // Eliminate hash integrity checks in handler functions.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(VMHashEliminationPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }

    addPhaseMarker(MPM, "Phase 3.56: VM handler inlining");
    // Inline small handler calls.  VMHandlerInlinerPass performs its own
    // inlining via llvm::InlineFunction and erases dead handlers, so no
    // separate AlwaysInlinerPass is needed.
    MPM.addPass(VMHandlerInlinerPass(/*max_handler_instrs=*/500,
                                     /*min_callsites=*/1));

    addPhaseMarker(MPM, "Phase 3.56: post-handler cleanup");
    // Clean up after handler inlining — scoped to functions that
    // VMHandlerInlinerPass tagged with "omill.needs_cleanup".
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(RecoverAllocaPointersPass());
      // Second hash elimination: inlined handlers may expose new murmur rounds.
      FPM.addPass(VMHashEliminationPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
        if (!F.hasFnAttribute("omill.needs_cleanup"))
          return false;
        F.removeFnAttr("omill.needs_cleanup");
        return true;
      }));
    }
  }

  addPhaseMarker(MPM, "Phase 3.6: iterative target resolution");
  // Phase 3.6: Iterative indirect target resolution.
  if (opts.use_block_lifting) {
    // Block-lifting mode: optimize block-functions, resolve constant
    // dispatch targets, and convert them to direct musttail calls.
    MPM.addPass(
        IterativeBlockDiscoveryPass(opts.max_resolution_iterations));
    // Merge block-functions back into multi-block trace functions.
    MPM.addPass(MergeBlockFunctionsPass());
    MPM.addPass(llvm::GlobalDCEPass());
  } else if (opts.resolve_indirect_targets) {
    MPM.addPass(
        IterativeTargetResolutionPass(opts.max_resolution_iterations));
  }

  // Phase 0 deferred: now that IterativeTargetResolution has discovered all
  // late functions and inlined semantic bodies into them, internalize and
  // remove dead semantic functions that have no remaining callers.
  MPM.addPass(InternalizeRemillSemanticsPass());
  MPM.addPass(llvm::GlobalDCEPass());

  addPhaseMarker(MPM, "Phase 3.7: IPCP");
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
    FPM.addPass(IndirectCallResolverPass());
#if OMILL_ENABLE_Z3
    FPM.addPass(Z3DispatchSolverPass());
#endif
    FPM.addPass(ResolveAndLowerControlFlowPass(ResolvePhases::ResolveTargets));
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "Phase 4: ABI recovery");
  // Phase 4: ABI Recovery
  if (opts.recover_abi) {
    buildABIRecoveryPipeline(MPM);

    // Phase 4 (late): Refine _native function parameter types.
    if (opts.refine_signatures) {
      MPM.addPass(RefineFunctionSignaturesPass());
    }
  }

  addPhaseMarker(MPM, "Phase 5: deobfuscation");
  // Phase 5: Deobfuscation (after ABI recovery for max constant visibility)
  if (opts.deobfuscate) {
    // Ensure BinaryMemoryAnalysis is cached before function passes need it.
    MPM.addPass(llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    buildDeobfuscationPipeline(FPM);
    // Deobfuscation only applies to _native wrappers post-ABI.
    MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
      return F.getName().ends_with("_native");
    }));
  }

  // Inline VM handler functions identified by callsite frequency analysis.
  // After deobfuscation has simplified individual functions, small functions
  // called from multiple dispatch sites are likely VM handlers.  Inlining
  // exposes their bodies to further optimization.
  if (opts.deobfuscate && !envDisabled("OMILL_SKIP_VM_HANDLER_INLINE")) {
    MPM.addPass(VMHandlerInlinerPass());
    // Re-run cleanup only on functions that had handlers inlined.
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
      if (!F.hasFnAttribute("omill.needs_cleanup"))
        return false;
      F.removeFnAttr("omill.needs_cleanup");
      return true;
    }));
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

  addPhaseMarker(MPM, "Final: cleanup");
  // Global cleanup
  MPM.addPass(llvm::GlobalDCEPass());
}

void registerModuleAnalyses(llvm::ModuleAnalysisManager &MAM) {
  MAM.registerPass([&] { return CallGraphAnalysis(); });
  MAM.registerPass([&] { return CallingConventionAnalysis(); });
  MAM.registerPass([&] { return BinaryMemoryAnalysis(); });
  MAM.registerPass([&] { return LiftedFunctionAnalysis(); });
  MAM.registerPass([&] { return ExceptionInfoAnalysis(); });
  MAM.registerPass([&] { return BlockLiftAnalysis(); });
  MAM.registerPass([&] { return VMHandlerGraphAnalysis(); });
}

void registerAAWithManager(llvm::AAManager &AAM) {
  AAM.registerFunctionAnalysis<SegmentsAA>();
}

}  // namespace omill

#include "omill/Passes/IterativeTargetResolution.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/FixIrreducible.h>
#include <llvm/Transforms/Utils/LCSSA.h>
#include <llvm/Transforms/Utils/LoopSimplify.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/BC/TraceLiftAnalysis.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/EliminateDeadPaths.h"
#include "omill/Passes/IndirectCallResolver.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Passes/RecoverAllocaPointers.h"
#include "omill/Passes/CollapseRemillSHRSwitch.h"
#include "omill/Passes/ResolveAndLowerControlFlow.h"
#include "omill/Passes/OptimizeState.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Omill.h"
#if OMILL_ENABLE_Z3
#include "omill/Passes/Z3DispatchSolver.h"
#endif

namespace omill {

namespace {

/// Check if a function contains any unresolved dispatch calls.
bool hasUnresolvedDispatches(llvm::Function &F) {
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I))
        if (auto *callee = call->getCalledFunction()) {
          auto name = callee->getName();
          if (name == "__omill_dispatch_call" ||
              name == "__omill_dispatch_jump")
            return true;
        }
  return false;
}

/// Count unresolved __omill_dispatch_call and __omill_dispatch_jump calls.
unsigned countUnresolvedDispatches(llvm::Module &M) {
  unsigned count = 0;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name == "__omill_dispatch_call" || name == "__omill_dispatch_jump")
          ++count;
      }
    }
  }
  return count;
}

/// Collect the set of functions containing unresolved dispatch calls.
llvm::SmallVector<llvm::Function *, 16>
collectAffectedFunctions(llvm::Module &M) {
  llvm::SmallVector<llvm::Function *, 16> result;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (hasUnresolvedDispatches(F))
      result.push_back(&F);
  }
  return result;
}

/// Run a FunctionPassManager on a specific set of functions.
void runFPMOnFunctions(llvm::FunctionPassManager &FPM,
                       llvm::ArrayRef<llvm::Function *> Funcs,
                       llvm::ModuleAnalysisManager &MAM,
                       llvm::Module &M) {
  llvm::FunctionAnalysisManager &FAM =
      MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();
  for (auto *F : Funcs) {
    if (F->isDeclaration())
      continue;
    FPM.run(*F, FAM);
  }
}

/// Collect constant dispatch targets that don't have a corresponding lifted
/// function.  Returns the set of new PCs to lift.
llvm::DenseSet<uint64_t> collectNewTargetPCs(
    llvm::Module &M, const LiftedFunctionMap *lifted) {
  llvm::DenseSet<uint64_t> new_pcs;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name != "__omill_dispatch_call" && name != "__omill_dispatch_jump")
          continue;
        if (call->arg_size() < 2)
          continue;
        auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!pc_arg)
          continue;
        uint64_t target_pc = pc_arg->getZExtValue();
        if (target_pc == 0)
          continue;
        // Check if a lifted function already exists.
        if (lifted && lifted->lookup(target_pc))
          continue;
        new_pcs.insert(target_pc);
      }
    }
  }
  return new_pcs;
}

/// Resolve a forward-declaration callee to its actual definition.
llvm::Function *resolveToDefinition(llvm::Function *decl, llvm::Module &M) {
  if (!decl->isDeclaration())
    return decl;

  auto name = decl->getName();
  if (!name.starts_with("sub_"))
    return nullptr;

  uint64_t va = extractEntryVA(name);
  if (va == 0)
    return nullptr;

  for (auto &F : M) {
    if (&F == decl || F.isDeclaration())
      continue;
    if (!F.getName().starts_with("sub_"))
      continue;
    if (extractEntryVA(F.getName()) == va)
      return &F;
  }
  return nullptr;
}

/// Inline lifted-function calls within functions that contain unresolved
/// dispatch_jump or dispatch_call targets.
/// If modified_out is provided, appends functions that were modified by
/// inlining (i.e., the containing functions that had callees inlined into
/// them).
bool inlineCalleesForDispatchResolution(
    llvm::Module &M,
    llvm::SmallVectorImpl<llvm::Function *> *modified_out = nullptr) {
  llvm::SmallVector<llvm::Function *, 4> targets;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_call" ||
            callee->getName() == "__omill_dispatch_jump") {
          targets.push_back(&F);
          goto next_func;
        }
      }
    }
    next_func:;
  }

  if (targets.empty())
    return false;

  bool inlined_any = false;

  for (auto *F : targets) {
    bool progress = true;
    while (progress) {
      progress = false;
      llvm::SmallVector<llvm::CallInst *, 8> to_inline;

      for (auto &BB : *F) {
        for (auto &I : BB) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI)
            continue;
          auto *callee = CI->getCalledFunction();
          if (!callee)
            continue;

          if (callee->getName().starts_with("__omill_") ||
              callee->getName().starts_with("__remill_") ||
              callee->getName().starts_with("llvm.") ||
              callee->isIntrinsic())
            continue;
          if (!callee->getName().starts_with("sub_"))
            continue;

          llvm::Function *def = resolveToDefinition(callee, *F->getParent());
          if (!def || def->isDeclaration())
            continue;
          if (def == F)
            continue;

          if (callee != def)
            CI->setCalledFunction(def->getFunctionType(), def);

          to_inline.push_back(CI);
        }
      }

      for (auto *CI : to_inline) {
        llvm::InlineFunctionInfo IFI;
        auto result = llvm::InlineFunction(*CI, IFI);
        if (result.isSuccess()) {
          progress = true;
          inlined_any = true;
          if (modified_out)
            modified_out->push_back(F);
        }
      }
    }
  }

  return inlined_any;
}

/// Reverse inlining: inline functions that CONTAIN unresolved dispatches
/// INTO their callers, enabling the caller's constant State stores to
/// propagate into the handler's dynamic dispatch targets.
///
/// This handles VM dispatch table handlers where the handler computes its
/// target from State fields (e.g., CX + DL) that the caller wrote as
/// constants before tail-calling the handler.  By inlining the handler
/// into the thunk, GVN forwards the constant values to the handler's
/// dispatch computation, making it resolvable.
bool inlineDispatchFunctionsIntoCallers(
    llvm::Module &M,
    llvm::SmallVectorImpl<llvm::Function *> *modified_out = nullptr) {
  // Find functions with unresolved dispatches.
  llvm::SmallPtrSet<llvm::Function *, 4> dispatch_funcs;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    bool has_dispatch = false;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_call" ||
            callee->getName() == "__omill_dispatch_jump") {
          has_dispatch = true;
          break;
        }
      }
      if (has_dispatch)
        break;
    }
    if (has_dispatch)
      dispatch_funcs.insert(&F);
  }

  if (dispatch_funcs.empty())
    return false;

  bool inlined_any = false;
  for (auto *DF : dispatch_funcs) {
    // Skip very large functions to prevent code blowup.
    unsigned inst_count = 0;
    for (auto &BB : *DF)
      inst_count += BB.size();
    if (inst_count > 50000)
      continue;

    // Collect call sites of this function in other functions.
    llvm::SmallVector<llvm::CallInst *, 4> call_sites;
    for (auto *U : DF->users()) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(U);
      if (!CI)
        continue;
      if (CI->getCalledFunction() != DF)
        continue;
      if (CI->getFunction() == DF)
        continue;
      call_sites.push_back(CI);
    }

    for (auto *CI : call_sites) {
      // Strip musttail — InlineFunction can't handle it.
      if (CI->isMustTailCall())
        CI->setTailCallKind(llvm::CallInst::TCK_None);

      auto *caller = CI->getFunction();
      llvm::InlineFunctionInfo IFI;
      auto result = llvm::InlineFunction(*CI, IFI);
      if (result.isSuccess()) {
        inlined_any = true;
        if (modified_out)
          modified_out->push_back(caller);
      }
    }
  }

  return inlined_any;
}

/// Build the set of semantic functions that transitively produce dispatch
/// intrinsics (__remill_function_call, __remill_jump, __remill_async_hyper_call).
/// A newly-lifted function has "dispatch potential" only if it calls one of
/// these semantics — otherwise it won't produce __omill_dispatch_* after
/// lowering, and its Step A/B/B2 work can be deferred.
llvm::DenseSet<llvm::Function *>
buildDispatchSemanticSet(llvm::Module &M) {
  llvm::DenseSet<llvm::Function *> result;

  // Seed: functions that directly call dispatch-producing intrinsics.
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *C = CI->getCalledFunction();
        if (!C)
          continue;
        auto name = C->getName();
        if (name == "__remill_function_call" || name == "__remill_jump" ||
            name == "__remill_async_hyper_call") {
          result.insert(&F);
          goto next_seed;
        }
      }
    }
    next_seed:;
  }

  // Transitively: if function A calls B (alwaysinline) and B is in result,
  // then A is also dispatch-producing.  Iterate to fixpoint.
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &F : M) {
      if (F.isDeclaration() || result.count(&F))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI)
            continue;
          auto *Callee = CI->getCalledFunction();
          if (!Callee || !result.count(Callee))
            continue;
          result.insert(&F);
          changed = true;
          goto next_trans;
        }
      }
      next_trans:;
    }
  }

  return result;
}

/// Inline all alwaysinline callees within a single function until fixpoint.
void inlineAlwaysInlineCalleesInFunc(llvm::Function *F) {
  if (F->isDeclaration())
    return;
  bool progress = true;
  while (progress) {
    progress = false;
    for (auto &BB : *F) {
      for (auto &I : llvm::make_early_inc_range(BB)) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *Callee = CI->getCalledFunction();
        if (!Callee || Callee->isDeclaration())
          continue;
        if (!Callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
          continue;
        llvm::InlineFunctionInfo IFI;
        if (llvm::InlineFunction(*CI, IFI).isSuccess())
          progress = true;
      }
    }
  }
}

/// Inline alwaysinline callees within a specific set of functions, replacing
/// the full-module AlwaysInlinerPass with a targeted version.
///
/// Phase 1 pre-expands the shared semantic functions by inlining their own
/// alwaysinline callees.  This is done once (~200 small functions) so that
/// Phase 2 copies fully-flattened bodies into each of the N target functions,
/// needing only a single inlining round instead of D rounds (D = call depth).
void inlineAlwaysInlineCallees(llvm::ArrayRef<llvm::Function *> Funcs) {
  // Phase 1: Collect alwaysinline functions called (directly or transitively)
  // by the target functions, and pre-expand them.
  llvm::DenseSet<llvm::Function *> semantics;
  llvm::SmallVector<llvm::Function *, 64> worklist;

  // Seed with direct callees of target functions.
  for (auto *F : Funcs) {
    if (F->isDeclaration())
      continue;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *Callee = CI->getCalledFunction())
            if (!Callee->isDeclaration() &&
                Callee->hasFnAttribute(llvm::Attribute::AlwaysInline) &&
                semantics.insert(Callee).second)
              worklist.push_back(Callee);
  }

  // Transitively collect callees of callees.
  while (!worklist.empty()) {
    auto *SF = worklist.pop_back_val();
    for (auto &BB : *SF)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *Callee = CI->getCalledFunction())
            if (!Callee->isDeclaration() &&
                Callee->hasFnAttribute(llvm::Attribute::AlwaysInline) &&
                semantics.insert(Callee).second)
              worklist.push_back(Callee);
  }

  // Pre-expand: inline alwaysinline callees within each semantic function.
  // Semantic functions are small (~30-200 insns) so this converges fast.
  for (auto *SF : semantics)
    inlineAlwaysInlineCalleesInFunc(SF);

  llvm::errs() << "ITR: Step A Phase 1: pre-expanded " << semantics.size()
               << " semantics\n";

  // Phase 2: Inline pre-expanded semantics into target functions.
  // Callees are fully flattened, so this typically needs only 1 round.
  for (size_t I = 0; I < Funcs.size(); ++I) {
    if (Funcs[I]->isDeclaration())
      continue;
    if (I % 50 == 0)
      llvm::errs() << "ITR: Step A Phase 2: " << I << "/" << Funcs.size()
                   << "\n";
    inlineAlwaysInlineCalleesInFunc(Funcs[I]);
  }
  llvm::errs() << "ITR: Step A Phase 2 complete\n";
}

}  // namespace

llvm::PreservedAnalyses IterativeTargetResolutionPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  unsigned iteration = 0;
  unsigned prev_count = countUnresolvedDispatches(M);

  if (prev_count == 0)
    return llvm::PreservedAnalyses::all();

  bool ever_changed = false;
  bool tried_inlining = false;
  bool tried_reverse_inlining = false;
  bool lifted_new_funcs = false;
  llvm::DenseSet<uint64_t> already_lifted_pcs;  // Prevent re-lifting.
  llvm::DenseSet<llvm::Function *> already_optimized;  // Skip redundant Step 1.
  llvm::SmallVector<llvm::Function *, 0> all_deferred;  // Deferred for post-loop.

  // Get optional trace-lift callback for discovering new functions.
  TraceLiftCallback lift_trace;
  {
    auto &lift_result = MAM.getResult<TraceLiftAnalysis>(M);
    lift_trace = lift_result.lift_trace;
  }

  auto *lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);

  do {
    lifted_new_funcs = false;  // Reset each iteration.

    // Collect functions with unresolved dispatches — only these need
    // the expensive optimization passes in Step 1.
    auto affected = collectAffectedFunctions(M);

    // Filter Step 1 to only functions not yet optimized in a prior iteration.
    llvm::SmallVector<llvm::Function *, 16> needs_opt;
    for (auto *F : affected)
      if (!already_optimized.count(F))
        needs_opt.push_back(F);

    llvm::errs() << "ITR iter " << iteration << ": " << affected.size()
                 << " affected, " << needs_opt.size() << " to optimize\n";

    // Step 1: CFG canonicalization + LLVM optimizations.
    // Run only on functions that haven't been optimized yet.
    if (!needs_opt.empty()) {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::FixIrreduciblePass());
      FPM.addPass(llvm::LoopSimplifyPass());
      FPM.addPass(llvm::LCSSAPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(ConstantMemoryFoldingPass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      FPM.addPass(ConstantMemoryFoldingPass());
      FPM.addPass(EliminateDeadPathsPass());
      FPM.addPass(llvm::InstCombinePass());
      runFPMOnFunctions(FPM, needs_opt, MAM, M);
      for (auto *F : needs_opt)
        already_optimized.insert(F);
    }

    // Step 2a: Resolve dispatch targets (but don't lower yet).
    // Only run on affected functions — resolvers early-exit on others anyway.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(ResolveAndLowerControlFlowPass());
      FPM.addPass(IndirectCallResolverPass());
#if OMILL_ENABLE_Z3
      FPM.addPass(Z3DispatchSolverPass());
#endif
      runFPMOnFunctions(FPM, affected, MAM, M);
    }

    // Step 2b: If we have a lift callback, discover constant dispatch targets
    // that don't map to any existing lifted function and lift them.
    // This runs BETWEEN resolution and lowering so we can see newly-resolved
    // constant PCs before they get lowered away.
    if (lift_trace) {
      auto new_pcs = collectNewTargetPCs(M, lifted);
      // Filter out PCs we've already lifted in a previous iteration.
      for (uint64_t pc : already_lifted_pcs)
        new_pcs.erase(pc);
      if (!new_pcs.empty()) {
        // Lift the discovered functions.
        llvm::SmallVector<llvm::Function *, 4> new_funcs;
        for (uint64_t pc : new_pcs) {
          lift_trace(pc);
          already_lifted_pcs.insert(pc);
        }

        // Collect the newly-lifted functions (raw remill IR).
        for (auto &F : M) {
          if (F.isDeclaration()) continue;
          for (uint64_t pc : new_pcs) {
            std::string prefix = "sub_" + llvm::Twine::utohexstr(pc).str();
            if (F.getName().starts_with(prefix)) {
              new_funcs.push_back(&F);
              // Register in the LiftedFunctionMap so downstream
              // resolution passes (Phase 3.7, Phase 4) can find it.
              if (lifted)
                lifted->insert(pc, &F);
              break;
            }
          }
        }

        // Split new functions: only those with dispatch potential (call
        // semantics that produce __remill_function_call / __remill_jump)
        // need expensive Step A/B/B2 during ITR.  The rest are deferred
        // to after the loop — they just need to exist for dispatch lowering.
        llvm::errs() << "ITR: lifted " << new_funcs.size()
                     << " new functions\n";

        llvm::SmallVector<llvm::Function *, 4> dispatch_new, deferred_new;
        {
          auto dispatch_set = buildDispatchSemanticSet(M);
          for (auto *F : new_funcs) {
            if (F->isDeclaration()) {
              continue;
            }
            bool has_potential = false;
            for (auto &BB : *F) {
              for (auto &I : BB) {
                auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
                if (!CI)
                  continue;
                auto *Callee = CI->getCalledFunction();
                if (Callee && dispatch_set.count(Callee)) {
                  has_potential = true;
                  goto classified;
                }
              }
            }
            classified:
            if (has_potential)
              dispatch_new.push_back(F);
            else
              deferred_new.push_back(F);
          }
        }
        llvm::errs() << "ITR: " << dispatch_new.size()
                     << " with dispatch potential, " << deferred_new.size()
                     << " deferred\n";

        // Accumulate deferred functions for post-loop processing.
        all_deferred.append(deferred_new.begin(), deferred_new.end());

        // Step C: Mark ALL new functions (including deferred) so they
        // survive the pipeline as callable functions.
        for (auto *F : new_funcs) {
          if (F->isDeclaration()) continue;
          F->addFnAttr("omill.vm_handler");
          F->addFnAttr(llvm::Attribute::NoInline);
        }

        // Run the equivalent of Phase 0 + Phase 1 + Phase 3 only on
        // dispatch-potential functions.
        if (!dispatch_new.empty()) {
          // Step A: Inline alwaysinline semantic function bodies into the
          // VM handler.  This is the Phase 0 equivalent.  Semantic function
          // bodies are preserved because GlobalDCE was deferred to after
          // Phase 3.6.
          {
            // Unprotect semantic functions: strip optnone+noinline, restore
            // alwaysinline so AlwaysInlinerPass can inline them into VM handlers.
            for (auto &F : M) {
              if (F.isDeclaration()) continue;
              if (!F.hasFnAttribute(llvm::Attribute::OptimizeNone)) continue;
              auto name = F.getName();
              if (name.starts_with("sub_") || name.starts_with("block_") ||
                  name.starts_with("__remill_") || name.starts_with("__omill_"))
                continue;
              F.removeFnAttr(llvm::Attribute::OptimizeNone);
              F.removeFnAttr(llvm::Attribute::NoInline);
              F.addFnAttr(llvm::Attribute::AlwaysInline);
            }

            llvm::errs() << "ITR: Step A: inlining semantics into "
                         << dispatch_new.size() << " functions...\n";
            inlineAlwaysInlineCallees(dispatch_new);
            auto &FAM =
                MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                    .getManager();
            for (auto *F : dispatch_new)
              FAM.invalidate(*F, llvm::PreservedAnalyses::none());
          }

          // Step B: Lower remill intrinsics now exposed by inlining.
          {
            llvm::errs() << "ITR: Step B: lowering remill intrinsics...\n";
            llvm::FunctionPassManager FPM;
            FPM.addPass(LowerRemillIntrinsicsPass(
                LowerCategories::Phase1 | LowerCategories::Phase3));
            FPM.addPass(llvm::InstCombinePass());
            FPM.addPass(llvm::SimplifyCFGPass());
            for (auto *F : dispatch_new) {
              if (F->isDeclaration()) continue;
              llvm::FunctionAnalysisManager &FAM =
                  MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                      .getManager();
              FPM.run(*F, FAM);
            }
          }

          // Step B2: State optimization — eliminate dead flag/PC stores.
          {
            llvm::errs() << "ITR: Step B2: state optimization on "
                         << dispatch_new.size() << " functions...\n";
            llvm::FunctionPassManager StateFPM;
            StateFPM.addPass(CollapseRemillSHRSwitchPass());
            StateFPM.addPass(llvm::SimplifyCFGPass());
            StateFPM.addPass(llvm::InstCombinePass());
            StateFPM.addPass(OptimizeStatePass(OptimizePhases::All));
            StateFPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
            StateFPM.addPass(llvm::InstCombinePass());
            StateFPM.addPass(llvm::DCEPass());
            StateFPM.addPass(llvm::SimplifyCFGPass());
            StateFPM.addPass(llvm::GVNPass());
            StateFPM.addPass(llvm::InstCombinePass());
            StateFPM.addPass(llvm::SimplifyCFGPass());
            for (auto *F : dispatch_new) {
              if (F->isDeclaration()) continue;
              llvm::FunctionAnalysisManager &FAM =
                  MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                      .getManager();
              StateFPM.run(*F, FAM);
            }
            llvm::errs() << "ITR: Step B2 complete\n";
          }
          // Mark dispatch functions as already optimized.
          for (auto *F : dispatch_new)
            already_optimized.insert(F);

          // Strip alwaysinline from callees of processed functions so
          // Phase 4's AlwaysInliner doesn't re-inline them.
          for (auto *F : dispatch_new) {
            if (F->isDeclaration()) continue;
            for (auto &BB : *F)
              for (auto &I : BB)
                if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
                  if (auto *Callee = CI->getCalledFunction())
                    if (Callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
                      Callee->removeFnAttr(llvm::Attribute::AlwaysInline);
          }
        }
        ever_changed = true;
        lifted_new_funcs = true;
        // New functions can introduce new dispatches — reset inlining
        // state so the loop can make another attempt with new callees.
        tried_inlining = false;
        tried_reverse_inlining = false;
        // Refresh the LiftedFunctionMap after lifting new functions.
        MAM.invalidate(M, llvm::PreservedAnalyses::none());
        lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);
        // Update baseline: new functions may increase dispatch count.
        prev_count = countUnresolvedDispatches(M);
      }
    }

    // Step 2c: Lower resolved dispatches.
    // Only run on affected functions — only they can have resolved dispatches.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
      runFPMOnFunctions(FPM, affected, MAM, M);
    }

    unsigned curr_count = countUnresolvedDispatches(M);
    bool made_progress = curr_count < prev_count || lifted_new_funcs;
    if (made_progress)
      ever_changed = true;

    if (!made_progress) {
      // Step 3: Resolution stalled.  Try inlining lifted callees into
      // functions with unresolved dispatches to expose interprocedural
      // data flow (e.g. VMenter → return-address patching).
      if (!tried_inlining && curr_count > 0) {
        llvm::SmallVector<llvm::Function *, 8> inline_modified;
        if (inlineCalleesForDispatchResolution(M, &inline_modified)) {
          tried_inlining = true;
          ever_changed = true;

          // Inlining dirtied these functions — they need re-optimization.
          for (auto *F : inline_modified)
            already_optimized.erase(F);

          llvm::errs() << "ITR: inlined callees into " << inline_modified.size()
                       << " functions\n";

          // Invalidate ALL cached analyses — inlining modified CFGs.
          MAM.invalidate(M, llvm::PreservedAnalyses::none());

          // After inlining VM handler bodies, the handler's context reads
          // become inttoptr(ptrtoint(alloca)+C) patterns.
          // RecoverAllocaPointers resolves these to GEPs, enabling GVN
          // store-to-load forwarding of context values (keys, image base).
          // ConstantMemoryFolding resolves loads from binary memory that
          // the handler uses for dispatch table lookups.
          // GVN then propagates the forwarded constants through the MBA,
          // and IndirectCallResolver's Monte Carlo evaluator picks up
          // the folded dispatch targets in the next iteration.
          {
            // Only run on functions with dispatches — those are the ones
            // that had callees inlined into them.
            auto post_inline = collectAffectedFunctions(M);
            llvm::FunctionPassManager FPM;
            FPM.addPass(RecoverAllocaPointersPass());
            FPM.addPass(llvm::GVNPass());
            FPM.addPass(ConstantMemoryFoldingPass());
            FPM.addPass(llvm::InstCombinePass());
            FPM.addPass(llvm::SimplifyCFGPass());
            FPM.addPass(llvm::ADCEPass());
            FPM.addPass(llvm::InstCombinePass());
            runFPMOnFunctions(FPM, post_inline, MAM, M);
            // Post-inline optimization done — mark them optimized again.
            for (auto *F : post_inline)
              already_optimized.insert(F);
          }

          // Re-fetch the lifted map after invalidation.
          lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);

          prev_count = curr_count;
          ++iteration;
          continue;  // Re-run optimization + resolution with inlined bodies.
        }
      }
      // Step 4: Reverse inlining — inline dispatch-containing functions
      // INTO their callers.  The caller may store constant context values
      // into State (e.g. VM keys) before tail-calling the handler.  After
      // inlining, GVN forwards those stores to the handler's State loads,
      // making dynamic dispatch targets (e.g. CX + DL) constant.
      if (!tried_reverse_inlining && curr_count > 0) {
        llvm::SmallVector<llvm::Function *, 8> reverse_modified;
        if (inlineDispatchFunctionsIntoCallers(M, &reverse_modified)) {
          tried_reverse_inlining = true;
          ever_changed = true;

          // Reverse inlining dirtied callers — they need re-optimization.
          for (auto *F : reverse_modified)
            already_optimized.erase(F);

          llvm::errs() << "ITR: reverse-inlined into "
                       << reverse_modified.size() << " functions\n";

          MAM.invalidate(M, llvm::PreservedAnalyses::none());

          // Mark __remill_undefined_* as memory(none) so GVN can
          // forward State stores past them.  These return undefined
          // values and never touch memory.
          for (auto &F : M) {
            if (F.getName().starts_with("__remill_undefined_"))
              F.setMemoryEffects(llvm::MemoryEffects::none());
          }

          // After reverse inlining, the caller now has dispatch
          // intrinsics from the handler.  OptimizeStatePass skips
          // sub_* functions with dispatches unless they have the
          // vm_handler attribute.  Mark them so promotion proceeds.
          for (auto &F : M) {
            if (F.isDeclaration()) continue;
            if (!F.getName().starts_with("sub_")) continue;
            bool has_dispatch = false;
            for (auto &BB : F)
              for (auto &I : BB)
                if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
                  if (auto *C = CI->getCalledFunction())
                    if (C->getName().starts_with("__omill_dispatch_")) {
                      has_dispatch = true;
                      goto mark_done;
                    }
            mark_done:
            if (has_dispatch && !F.hasFnAttribute("omill.vm_handler"))
              F.addFnAttr("omill.vm_handler");
          }

          // Phase A: Collapse SHR switches from the inlined handler,
          // then promote State fields to allocas so stores are visible
          // to SROA/GVN without inttoptr aliasing barriers.
          // Only run on functions with dispatches (callers that received
          // the reverse-inlined handler bodies).
          {
            auto post_reverse = collectAffectedFunctions(M);
            llvm::FunctionPassManager FPM;
            FPM.addPass(CollapseRemillSHRSwitchPass());
            FPM.addPass(llvm::SimplifyCFGPass());
            FPM.addPass(llvm::InstCombinePass());
            FPM.addPass(OptimizeStatePass(OptimizePhases::All));
            FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
            FPM.addPass(llvm::InstCombinePass());
            runFPMOnFunctions(FPM, post_reverse, MAM, M);
          }

          // Phase B: Standard cleanup with constant folding.
          {
            auto post_reverse = collectAffectedFunctions(M);
            llvm::FunctionPassManager FPM;
            FPM.addPass(RecoverAllocaPointersPass());
            FPM.addPass(llvm::GVNPass());
            FPM.addPass(ConstantMemoryFoldingPass());
            FPM.addPass(llvm::InstCombinePass());
            FPM.addPass(llvm::SimplifyCFGPass());
            FPM.addPass(llvm::ADCEPass());
            FPM.addPass(llvm::InstCombinePass());
            runFPMOnFunctions(FPM, post_reverse, MAM, M);
            // Post-reverse optimization done — mark them optimized again.
            for (auto *F : post_reverse)
              already_optimized.insert(F);
          }

          lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);

          // Recount after cleanup — reverse inlining may have increased
          // the count (handler copy + inlined copy), but cleanup may
          // have resolved some.  Use post-cleanup count as baseline.
          prev_count = countUnresolvedDispatches(M);
          ++iteration;
          continue;
        }
      }
      break;
    }

    tried_inlining = false;  // Reset on progress — allow re-inlining.
    tried_reverse_inlining = false;
    prev_count = curr_count;
    ++iteration;
  } while (iteration < max_iterations_);

  llvm::errs() << "ITR: " << iteration << " iterations, "
               << countUnresolvedDispatches(M) << " dispatches remaining\n";

  // Process deferred functions that were skipped during the ITR loop.
  // These have no dispatch potential so they don't affect resolution,
  // but they need Step A/B/B2 before the downstream ABI recovery pipeline.
  if (!all_deferred.empty()) {
    llvm::errs() << "ITR: processing " << all_deferred.size()
                 << " deferred functions...\n";
    ever_changed = true;

    // Unprotect semantic functions (may already be done, but idempotent).
    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      if (!F.hasFnAttribute(llvm::Attribute::OptimizeNone)) continue;
      auto name = F.getName();
      if (name.starts_with("sub_") || name.starts_with("block_") ||
          name.starts_with("__remill_") || name.starts_with("__omill_"))
        continue;
      F.removeFnAttr(llvm::Attribute::OptimizeNone);
      F.removeFnAttr(llvm::Attribute::NoInline);
      F.addFnAttr(llvm::Attribute::AlwaysInline);
    }

    // Step A: Inline semantics.
    llvm::errs() << "ITR: deferred Step A: inlining semantics...\n";
    inlineAlwaysInlineCallees(all_deferred);
    {
      auto &FAM =
          MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
              .getManager();
      for (auto *F : all_deferred)
        FAM.invalidate(*F, llvm::PreservedAnalyses::none());
    }

    // Step B: Lower remill intrinsics.
    {
      llvm::errs() << "ITR: deferred Step B...\n";
      llvm::FunctionPassManager FPM;
      FPM.addPass(LowerRemillIntrinsicsPass(
          LowerCategories::Phase1 | LowerCategories::Phase3));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::SimplifyCFGPass());
      for (auto *F : all_deferred) {
        if (F->isDeclaration()) continue;
        llvm::FunctionAnalysisManager &FAM =
            MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                .getManager();
        FPM.run(*F, FAM);
      }
    }

    // Step B2: State optimization.
    {
      llvm::errs() << "ITR: deferred Step B2...\n";
      llvm::FunctionPassManager StateFPM;
      StateFPM.addPass(CollapseRemillSHRSwitchPass());
      StateFPM.addPass(llvm::SimplifyCFGPass());
      StateFPM.addPass(llvm::InstCombinePass());
      StateFPM.addPass(OptimizeStatePass(OptimizePhases::All));
      StateFPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      StateFPM.addPass(llvm::InstCombinePass());
      StateFPM.addPass(llvm::DCEPass());
      StateFPM.addPass(llvm::SimplifyCFGPass());
      StateFPM.addPass(llvm::GVNPass());
      StateFPM.addPass(llvm::InstCombinePass());
      StateFPM.addPass(llvm::SimplifyCFGPass());
      for (auto *F : all_deferred) {
        if (F->isDeclaration()) continue;
        llvm::FunctionAnalysisManager &FAM =
            MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                .getManager();
        StateFPM.run(*F, FAM);
      }
    }

    // Strip alwaysinline from callees.
    for (auto *F : all_deferred) {
      if (F->isDeclaration()) continue;
      for (auto &BB : *F)
        for (auto &I : BB)
          if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
            if (auto *Callee = CI->getCalledFunction())
              if (Callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
                Callee->removeFnAttr(llvm::Attribute::AlwaysInline);
    }

    llvm::errs() << "ITR: deferred processing complete\n";
  }

  return ever_changed ? llvm::PreservedAnalyses::none()
                      : llvm::PreservedAnalyses::all();
}

}  // namespace omill

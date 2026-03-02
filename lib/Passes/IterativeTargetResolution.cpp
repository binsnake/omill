#include "omill/Passes/IterativeTargetResolution.h"

#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
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
#include "omill/Passes/ResolveAndLowerControlFlow.h"
#include "omill/Passes/OptimizeState.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Omill.h"
#if OMILL_ENABLE_Z3
#include "omill/Passes/Z3DispatchSolver.h"
#endif

namespace omill {

namespace {

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
bool inlineCalleesForDispatchResolution(llvm::Module &M) {
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
        }
      }
    }
  }

  return inlined_any;
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
  bool lifted_new_funcs = false;
  llvm::DenseSet<uint64_t> already_lifted_pcs;  // Prevent re-lifting.

  // Get optional trace-lift callback for discovering new functions.
  TraceLiftCallback lift_trace;
  {
    auto &lift_result = MAM.getResult<TraceLiftAnalysis>(M);
    lift_trace = lift_result.lift_trace;
  }

  auto *lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);

  do {
    lifted_new_funcs = false;  // Reset each iteration.
    // Step 1: CFG canonicalization + LLVM optimizations.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::FixIrreduciblePass());
      FPM.addPass(llvm::LoopSimplifyPass());
      FPM.addPass(llvm::LCSSAPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      FPM.addPass(ConstantMemoryFoldingPass());
      FPM.addPass(EliminateDeadPathsPass());
      FPM.addPass(llvm::InstCombinePass());
      auto adaptor = llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
      adaptor.run(M, MAM);
    }

    // Debug: dump IR after Step 1 when we just inlined.
    if (tried_inlining && iteration == 1) {
      std::error_code ec;
      llvm::raw_fd_ostream os("post_inline_opt.ll", ec, llvm::sys::fs::OF_Text);
      if (!ec) M.print(os, nullptr);
    }

    // Step 2a: Resolve dispatch targets (but don't lower yet).
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(ResolveAndLowerControlFlowPass());
      FPM.addPass(IndirectCallResolverPass());
#if OMILL_ENABLE_Z3
      FPM.addPass(Z3DispatchSolverPass());
#endif
      auto adaptor = llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
      adaptor.run(M, MAM);
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

        // Run the equivalent of Phase 0 + Phase 1 + Phase 3 on newly
        // lifted functions.  These missed earlier pipeline phases that
        // inline semantic functions, lower remill intrinsics, and resolve
        // control flow.
        if (!new_funcs.empty()) {
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

            llvm::ModulePassManager InlineMPM;
            InlineMPM.addPass(llvm::AlwaysInlinerPass());
            InlineMPM.run(M, MAM);
            MAM.invalidate(M, llvm::PreservedAnalyses::none());
          }

          // DEBUG: dump after AlwaysInliner, before lowering
          if (auto *dbg = std::getenv("OMILL_DUMP_STEP2A")) {
            std::string path(dbg);
            std::error_code EC;
            llvm::raw_fd_ostream OS(path, EC);
            if (!EC) M.print(OS, nullptr);
          }
          // Step B: Lower remill intrinsics now exposed by inlining.
          {
            llvm::FunctionPassManager FPM;
            FPM.addPass(LowerRemillIntrinsicsPass(
                LowerCategories::Phase1 | LowerCategories::Phase3));
            FPM.addPass(llvm::InstCombinePass());
            FPM.addPass(llvm::SimplifyCFGPass());
            for (auto *F : new_funcs) {
              if (F->isDeclaration()) continue;
              llvm::FunctionAnalysisManager &FAM =
                  MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                      .getManager();
              FPM.run(*F, FAM);
            }
          }

          // DEBUG: dump post-inline post-lowered handler IR
          if (auto *dbg = std::getenv("OMILL_DUMP_STEP2B")) {
            std::string path(dbg);
            std::error_code EC;
            llvm::raw_fd_ostream OS(path, EC);
            if (!EC) M.print(OS, nullptr);
          }

          // Step B2: State optimization — eliminate dead flag/PC stores.
          // After semantic inlining, the handler has ~3400 dead flag stores
          // and ~900 dead PC stores that LLVM DSE can't eliminate (inttoptr
          // memory ops between them prevent alias analysis from proving
          // non-aliasing with State GEP offsets).
          {
            llvm::FunctionPassManager StateFPM;
            StateFPM.addPass(OptimizeStatePass(OptimizePhases::All));
            StateFPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
            StateFPM.addPass(llvm::InstCombinePass());
            StateFPM.addPass(llvm::DCEPass());
            StateFPM.addPass(llvm::SimplifyCFGPass());
            StateFPM.addPass(llvm::GVNPass());
            StateFPM.addPass(llvm::InstCombinePass());
            StateFPM.addPass(llvm::SimplifyCFGPass());
            for (auto *F : new_funcs) {
              if (F->isDeclaration()) continue;
              llvm::FunctionAnalysisManager &FAM =
                  MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                      .getManager();
              StateFPM.run(*F, FAM);
            }
          }
          // Step C: Mark dynamically-discovered functions so:
          // (1) EliminateStateStruct does NOT add alwaysinline
          // (2) Phase 4 AlwaysInliner does NOT re-inline stubs into them
          // (3) They survive the full ABI recovery pipeline as callable
          //     functions with the remill calling convention.
          for (auto *F : new_funcs) {
            if (F->isDeclaration()) continue;
            F->addFnAttr("omill.vm_handler");
            F->addFnAttr(llvm::Attribute::NoInline);
            // Strip alwaysinline from any remaining callees so Phase 4's
            // AlwaysInliner doesn't re-inline them.
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
        // Refresh the LiftedFunctionMap after lifting new functions.
        MAM.invalidate(M, llvm::PreservedAnalyses::none());
        lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);
        // Update baseline: new functions may increase dispatch count.
        prev_count = countUnresolvedDispatches(M);
      }
    }

    // Step 2c: Lower resolved dispatches.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
      auto adaptor = llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
      adaptor.run(M, MAM);
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
        if (inlineCalleesForDispatchResolution(M)) {
          tried_inlining = true;
          ever_changed = true;

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
            llvm::FunctionPassManager FPM;
            FPM.addPass(RecoverAllocaPointersPass());
            FPM.addPass(llvm::GVNPass());
            FPM.addPass(ConstantMemoryFoldingPass());
            FPM.addPass(llvm::InstCombinePass());
            FPM.addPass(llvm::SimplifyCFGPass());
            FPM.addPass(llvm::ADCEPass());
            FPM.addPass(llvm::SimplifyCFGPass());
            FPM.addPass(llvm::InstCombinePass());
            auto adaptor =
                llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
            adaptor.run(M, MAM);
          }

          // Re-fetch the lifted map after invalidation.
          lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);

          prev_count = curr_count;
          ++iteration;
          continue;  // Re-run optimization + resolution with inlined bodies.
        }
      }
      break;
    }

    tried_inlining = false;  // Reset on progress — allow re-inlining.
    prev_count = curr_count;
    ++iteration;
  } while (iteration < max_iterations_);

  return ever_changed ? llvm::PreservedAnalyses::none()
                      : llvm::PreservedAnalyses::all();
}

}  // namespace omill

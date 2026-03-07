#include "omill/Passes/IterativeTargetResolution.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Instructions.h>
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
#include "omill/BC/BlockLifterAnalysis.h"
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

#include <optional>

namespace omill {

namespace {

/// Combined dispatch info: total unresolved dispatch count + affected functions.
struct DispatchInfo {
  unsigned count = 0;
  llvm::SmallVector<llvm::Function *, 16> affected;
};

/// Scan the module once to collect both the total unresolved dispatch count
/// and the set of non-declaration functions containing dispatches.
DispatchInfo collectDispatchInfo(llvm::Module &M) {
  DispatchInfo info;
  for (auto &F : M) {
    bool func_affected = false;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name == "__omill_dispatch_call" ||
            name == "__omill_dispatch_jump") {
          ++info.count;
          func_affected = true;
        }
      }
    }
    if (func_affected && !F.isDeclaration())
      info.affected.push_back(&F);
  }
  return info;
}

/// Count unresolved dispatches only (lightweight, no affected list).
unsigned countUnresolvedDispatches(llvm::Module &M) {
  unsigned count = 0;
  for (auto &F : M)
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = call->getCalledFunction()) {
            auto name = callee->getName();
            if (name == "__omill_dispatch_call" ||
                name == "__omill_dispatch_jump")
              ++count;
          }
  return count;
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

  auto maybeCollectTarget = [&](uint64_t target_pc) {
    if (target_pc == 0)
      return;
    if (lifted && lifted->lookup(target_pc))
      return;
    new_pcs.insert(target_pc);
  };

  auto extractIntToPtrConstTarget = [&](llvm::Value *callee_op)
      -> std::optional<uint64_t> {
    if (!callee_op)
      return std::nullopt;
    callee_op = callee_op->stripPointerCasts();

    llvm::ConstantInt *ci = nullptr;
    if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
      if (ce->getOpcode() == llvm::Instruction::IntToPtr)
        ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
    }
    if (!ci) {
      if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
        ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
    }
    if (!ci)
      return std::nullopt;
    return ci->getZExtValue();
  };

  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;

        if (!call->getCalledFunction()) {
          if (auto target = extractIntToPtrConstTarget(call->getCalledOperand()))
            maybeCollectTarget(*target);
          continue;
        }

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
        maybeCollectTarget(pc_arg->getZExtValue());
      }
    }
  }
  return new_pcs;
}

/// Map from virtual address to defined function, for O(1) resolution.
using VAFuncMap = llvm::DenseMap<uint64_t, llvm::Function *>;

/// Build a VA-to-Function map for all defined sub_* functions.
VAFuncMap buildVAToFunctionMap(llvm::Module &M) {
  VAFuncMap map;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.getName().starts_with("sub_"))
      continue;
    uint64_t va = extractEntryVA(F.getName());
    if (va == 0)
      continue;
    map.try_emplace(va, &F);
  }
  return map;
}

/// Resolve a forward-declaration callee to its actual definition using the
/// prebuilt VA map for O(1) lookup instead of O(N) linear scan.
llvm::Function *resolveToDefinition(llvm::Function *decl,
                                    const VAFuncMap &va_map) {
  if (!decl->isDeclaration())
    return decl;

  auto name = decl->getName();
  if (!name.starts_with("sub_"))
    return nullptr;

  uint64_t va = extractEntryVA(name);
  if (va == 0)
    return nullptr;

  auto it = va_map.find(va);
  if (it == va_map.end())
    return nullptr;
  if (it->second == decl)
    return nullptr;
  return it->second;
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

  // Build VA-to-function map once for O(1) resolution.
  auto va_map = buildVAToFunctionMap(M);

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

          llvm::Function *def = resolveToDefinition(callee, va_map);
          if (!def || def->isDeclaration())
            continue;
          if (def == F)
            continue;

          // Only inline callees that can contribute to dispatch resolution:
          // they must contain dispatch intrinsics or calls to other sub_*
          // functions.  Leaf functions without dispatch calls (e.g. security
          // cookie init) provide no benefit and their inlined code may be
          // misfolded by ConstantMemoryFolding (reading uninitialized globals
          // as zero from the static binary kills continuation paths).
          {
            bool has_dispatch_or_subcalls = false;
            for (auto &DefBB : *def) {
              for (auto &DefI : DefBB) {
                auto *DefCI = llvm::dyn_cast<llvm::CallInst>(&DefI);
                if (!DefCI)
                  continue;
                auto *DefCallee = DefCI->getCalledFunction();
                if (!DefCallee)
                  continue;
                auto name = DefCallee->getName();
                if (name == "__omill_dispatch_call" ||
                    name == "__omill_dispatch_jump" ||
                    name.starts_with("sub_")) {
                  has_dispatch_or_subcalls = true;
                  break;
                }
              }
              if (has_dispatch_or_subcalls)
                break;
            }
            if (!has_dispatch_or_subcalls)
              continue;
          }

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

/// Build a PreservedAnalyses that preserves immutable module analyses.
/// BinaryMemoryAnalysis, TraceLiftAnalysis, and BlockLiftAnalysis never
/// change during ITR, so we avoid re-running their invalidation callbacks.
llvm::PreservedAnalyses immutablePreserved() {
  auto PA = llvm::PreservedAnalyses::none();
  PA.preserve<BinaryMemoryAnalysis>();
  PA.preserve<TraceLiftAnalysis>();
  PA.preserve<BlockLiftAnalysis>();
  return PA;
}

/// Run Step B: Lower remill intrinsics exposed by semantic inlining.
void runStepB(llvm::ArrayRef<llvm::Function *> Funcs,
              llvm::ModuleAnalysisManager &MAM,
              llvm::Module &M) {
  llvm::FunctionPassManager FPM;
  FPM.addPass(LowerRemillIntrinsicsPass(
      LowerCategories::Phase1 | LowerCategories::Phase3));
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::SimplifyCFGPass());
  runFPMOnFunctions(FPM, Funcs, MAM, M);
}

/// Run Step B2: State optimization after intrinsic lowering.
/// When lightweight=true, uses a reduced 5-pass pipeline sufficient for
/// ABI recovery but skipping heavy passes (GVN, SROA, DCE) that dispatch
/// resolution needs.  Phase 5 (deobfuscation) runs GVN/SROA later anyway.
void runStepB2(llvm::ArrayRef<llvm::Function *> Funcs,
               llvm::ModuleAnalysisManager &MAM,
               llvm::Module &M,
               bool lightweight = false) {
  llvm::FunctionPassManager StateFPM;
  StateFPM.addPass(CollapseRemillSHRSwitchPass());
  StateFPM.addPass(llvm::SimplifyCFGPass());
  StateFPM.addPass(llvm::InstCombinePass());
  StateFPM.addPass(OptimizeStatePass(OptimizePhases::All));
  if (!lightweight) {
    StateFPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    StateFPM.addPass(llvm::InstCombinePass());
    StateFPM.addPass(llvm::DCEPass());
    StateFPM.addPass(llvm::SimplifyCFGPass());
    StateFPM.addPass(llvm::GVNPass());
    StateFPM.addPass(llvm::InstCombinePass());
  }
  StateFPM.addPass(llvm::SimplifyCFGPass());
  runFPMOnFunctions(StateFPM, Funcs, MAM, M);
}

/// Inline all alwaysinline callees within a single function until fixpoint.
void inlineAlwaysInlineCalleesInFunc(llvm::Function *F) {
  if (F->isDeclaration())
    return;

  // Collect alwaysinline call sites into a worklist instead of rescanning
  // the entire function after every inline.  After Phase 1 pre-expansion,
  // inlined bodies rarely contain further alwaysinline calls, so this
  // typically processes the initial set and stops.  Any new alwaysinline
  // calls discovered via InlinedCallSites are appended to the worklist.
  llvm::SmallVector<llvm::CallInst *, 64> Worklist;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (auto *Callee = CI->getCalledFunction())
          if (!Callee->isDeclaration() &&
              Callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
            Worklist.push_back(CI);

  while (!Worklist.empty()) {
    auto *CI = Worklist.pop_back_val();
    llvm::InlineFunctionInfo IFI;
    if (!llvm::InlineFunction(*CI, IFI).isSuccess())
      continue;
    // Check newly inlined call sites for further alwaysinline calls.
    for (auto *NewCS : IFI.InlinedCallSites)
      if (auto *NewCI = llvm::dyn_cast<llvm::CallInst>(NewCS))
        if (auto *Callee = NewCI->getCalledFunction())
          if (!Callee->isDeclaration() &&
              Callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
            Worklist.push_back(NewCI);
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
  // Skip functions that have no alwaysinline calls to avoid scanning them.
  size_t skipped = 0;
  for (size_t I = 0; I < Funcs.size(); ++I) {
    auto *F = Funcs[I];
    if (F->isDeclaration()) {
      ++skipped;
      continue;
    }

    // Quick check: does this function have any alwaysinline calls?
    bool has_inline_calls = false;
    for (auto &BB : *F) {
      for (auto &Inst : BB) {
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&Inst))
          if (auto *Callee = CI->getCalledFunction())
            if (!Callee->isDeclaration() &&
                Callee->hasFnAttribute(llvm::Attribute::AlwaysInline)) {
              has_inline_calls = true;
              break;
            }
      }
      if (has_inline_calls) break;
    }
    if (!has_inline_calls) {
      ++skipped;
      continue;
    }

    if (I % 50 == 0)
      llvm::errs() << "ITR: Step A Phase 2: " << I << "/" << Funcs.size()
                   << "\n";
    inlineAlwaysInlineCalleesInFunc(F);
  }
  llvm::errs() << "ITR: Step A Phase 2 complete (" << skipped
               << " skipped)\n";
}

/// Process deferred functions: unprotect semantics, inline, lower, optimize.
void processDeferredFunctions(llvm::ArrayRef<llvm::Function *> deferred,
                              llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
  // Unprotect semantic functions: ensure alwaysinline is set so
  // inlineAlwaysInlineCallees can inline them into deferred functions.
  // Earlier ITR iterations may have already stripped optnone+alwaysinline
  // from semantics, so we can't gate on optnone — instead, add
  // alwaysinline to all non-lifted, non-intrinsic defined functions.
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
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
  inlineAlwaysInlineCallees(deferred);
  {
    auto &FAM =
        MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();
    for (auto *F : deferred)
      FAM.invalidate(*F, llvm::PreservedAnalyses::none());
  }

  // Step B: Lower remill intrinsics.
  llvm::errs() << "ITR: deferred Step B...\n";
  runStepB(deferred, MAM, M);

  // Step B2: State optimization (full pipeline — deferred functions still need
  // SROA/GVN to properly eliminate State struct usage).
  llvm::errs() << "ITR: deferred Step B2...\n";
  runStepB2(deferred, MAM, M);

  // Step 1: CFG canonicalization + optimizations to prepare for resolution.
  llvm::errs() << "ITR: deferred Step 1: optimizing...\n";
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(ConstantMemoryFoldingPass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::InstCombinePass());
    runFPMOnFunctions(FPM, deferred, MAM, M);
  }

  // Step 2: Resolve and lower dispatch targets.
  llvm::errs() << "ITR: deferred Step 2: resolving dispatches...\n";
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(ResolveAndLowerControlFlowPass());
    FPM.addPass(IndirectCallResolverPass());
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::ADCEPass());
    runFPMOnFunctions(FPM, deferred, MAM, M);
  }

  // Strip alwaysinline from callees.
  for (auto *F : deferred) {
    if (F->isDeclaration())
      continue;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *Callee = CI->getCalledFunction())
            if (Callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
              Callee->removeFnAttr(llvm::Attribute::AlwaysInline);
  }
}

}  // namespace

llvm::PreservedAnalyses IterativeTargetResolutionPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  unsigned iteration = 0;
  unsigned prev_count = 0;

  bool ever_changed = false;
  bool tried_inlining = false;
  bool tried_reverse_inlining = false;
  bool lifted_new_funcs = false;
  llvm::DenseSet<uint64_t> already_lifted_pcs;  // Prevent re-lifting.
  llvm::DenseSet<llvm::Function *> already_optimized;  // Skip redundant Step 1.
  llvm::DenseSet<llvm::Function *> already_resolved;   // Skip redundant Step 2a.
  llvm::SmallVector<llvm::Function *, 0> all_deferred;  // Deferred for post-loop.

  // Get optional trace-lift callback for discovering new functions.
  TraceLiftCallback lift_trace;
  {
    auto &lift_result = MAM.getResult<TraceLiftAnalysis>(M);
    lift_trace = lift_result.lift_trace;
  }

  auto *lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);

  // Cache the dispatch semantic set — stable across the ITR loop since
  // semantic functions don't change structure during resolution.
  auto dispatch_set = buildDispatchSemanticSet(M);

  do {
    lifted_new_funcs = false;  // Reset each iteration.

    // Collect dispatch info: both the count and the affected functions
    // in a single module scan.
    auto info = collectDispatchInfo(M);
    if (info.count == 0) {
      if (!ever_changed)
        return llvm::PreservedAnalyses::all();
      break;
    }
    if (iteration == 0)
      prev_count = info.count;
    auto affected = std::move(info.affected);

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
      for (auto *F : needs_opt) {
        already_optimized.insert(F);
        // Optimization changed IR — needs fresh resolution.
        already_resolved.erase(F);
      }
    }

    // Step 2a: Resolve dispatch targets (but don't lower yet).
    // Only run on functions whose IR changed since last resolution.
    {
      llvm::SmallVector<llvm::Function *, 16> needs_resolve;
      for (auto *F : affected)
        if (!already_resolved.count(F))
          needs_resolve.push_back(F);

      if (!needs_resolve.empty()) {
        llvm::errs() << "ITR: Step 2a: resolving " << needs_resolve.size()
                     << "/" << affected.size() << " functions\n";
        llvm::FunctionPassManager FPM;
        FPM.addPass(ResolveAndLowerControlFlowPass());
        FPM.addPass(IndirectCallResolverPass());
#if OMILL_ENABLE_Z3
        FPM.addPass(Z3DispatchSolverPass());
#endif
        // Per-function resolution with progress logging.
        {
          auto &FAM = MAM.getResult<
              llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();
          for (unsigned i = 0; i < needs_resolve.size(); ++i) {
            auto *RF = needs_resolve[i];
            if (RF->isDeclaration())
              continue;
            unsigned ic = 0;
            for (auto &BB : *RF)
              ic += BB.size();
            llvm::errs() << "  resolving [" << i << "] "
                         << RF->getName() << " (" << ic << " insts)\n";
            FPM.run(*RF, FAM);
          }
        }
        for (auto *F : needs_resolve)
          already_resolved.insert(F);
      }
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
            std::string prefix = omill::liftedFunctionName(pc);
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
        for (auto *F : new_funcs) {
          if (F->isDeclaration())
            continue;
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
          llvm::errs() << "ITR: Step B: lowering remill intrinsics...\n";
          runStepB(dispatch_new, MAM, M);

          // Step B2: State optimization — eliminate dead flag/PC stores.
          llvm::errs() << "ITR: Step B2: state optimization on "
                       << dispatch_new.size() << " functions...\n";
          runStepB2(dispatch_new, MAM, M);
          llvm::errs() << "ITR: Step B2 complete\n";

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
        MAM.invalidate(M, immutablePreserved());
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
    if (made_progress) {
      ever_changed = true;
      // Lowering changed IR in some affected functions — they need
      // re-resolution on the next iteration to discover further targets.
      for (auto *F : affected)
        already_resolved.erase(F);
    }

    if (!made_progress) {
      // Step 3: Resolution stalled.  Try inlining lifted callees into
      // functions with unresolved dispatches to expose interprocedural
      // data flow (e.g. VMenter → return-address patching).
      if (!tried_inlining && curr_count > 0) {
        llvm::SmallVector<llvm::Function *, 8> inline_modified;
        if (inlineCalleesForDispatchResolution(M, &inline_modified)) {
          tried_inlining = true;
          ever_changed = true;

          // Inlining dirtied these functions — they need re-optimization
          // and re-resolution.
          for (auto *F : inline_modified) {
            already_optimized.erase(F);
            already_resolved.erase(F);
          }

          llvm::errs() << "ITR: inlined callees into " << inline_modified.size()
                       << " functions\n";

          // Invalidate cached analyses — inlining modified CFGs.
          MAM.invalidate(M, immutablePreserved());

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
            // Only run on functions actually modified by inlining, not
            // all affected — unmodified functions are already optimized.
            llvm::SmallPtrSet<llvm::Function *, 16> modified_set(
                inline_modified.begin(), inline_modified.end());
            llvm::SmallVector<llvm::Function *, 16> post_inline(
                modified_set.begin(), modified_set.end());
            llvm::errs() << "ITR: post-inline optimizing "
                         << post_inline.size() << " modified functions\n";
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

          // Reverse inlining dirtied callers — they need re-optimization
          // and re-resolution.
          for (auto *F : reverse_modified) {
            already_optimized.erase(F);
            already_resolved.erase(F);
          }

          llvm::errs() << "ITR: reverse-inlined into "
                       << reverse_modified.size() << " functions\n";

          MAM.invalidate(M, immutablePreserved());

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

          // Deduplicate the modified set — only these callers need
          // re-optimization, not all 2500+ affected functions.
          llvm::SmallPtrSet<llvm::Function *, 16> rev_set(
              reverse_modified.begin(), reverse_modified.end());
          llvm::SmallVector<llvm::Function *, 16> post_reverse(
              rev_set.begin(), rev_set.end());
          llvm::errs() << "ITR: post-reverse optimizing "
                       << post_reverse.size() << " modified functions\n";

          // Phase 0: Trim dead code from inlined handler body.
          // After reverse inlining, functions contain full handler bodies
          // with dead error paths and unreachable continuations. Trimming
          // first shrinks functions before the expensive Phase A passes.
          {
            llvm::FunctionPassManager FPM;
            FPM.addPass(llvm::ADCEPass());
            FPM.addPass(llvm::SimplifyCFGPass());
            runFPMOnFunctions(FPM, post_reverse, MAM, M);
          }

          // Phase A: Collapse SHR switches from the inlined handler,
          // then promote State fields to allocas so stores are visible
          // to SROA/GVN without inttoptr aliasing barriers.
          {
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
    processDeferredFunctions(all_deferred, M, MAM);
    llvm::errs() << "ITR: deferred processing complete\n";
  }

  return ever_changed ? llvm::PreservedAnalyses::none()
                      : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#include "omill/Omill.h"

#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/JumpThreading.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/DeadArgumentElimination.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>
#include <llvm/Transforms/IPO/Inliner.h>
#include <llvm/Transforms/IPO/SCCP.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/DeadStoreElimination.h>
#include <llvm/Transforms/Scalar/LoopDeletion.h>
#include <llvm/Transforms/Scalar/LoopRotation.h>
#include <llvm/Transforms/Scalar/LoopUnrollPass.h>
#include <llvm/Transforms/Scalar/LoopPassManager.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

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
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Passes/ResolveForcedExceptions.h"
#include "omill/Passes/MemoryPointerElimination.h"
#include "omill/Passes/RecoverFunctionSignatures.h"
#include "omill/Passes/RefineFunctionSignatures.h"
#include "omill/Passes/RecoverStackFrame.h"
#include "omill/Passes/RecoverStackFrameTypes.h"
#include "omill/Passes/EliminateStateStruct.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/VirtualCalleeRegistry.h"
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
#include "omill/BC/TraceLiftAnalysis.h"
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
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Passes/VMDispatchResolution.h"
#include "omill/Passes/VMDeadMergedHandlerElimination.h"
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
#include "omill/Analysis/TargetArchAnalysis.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

bool isWindowsTargetOS(llvm::StringRef os) {
  return os.contains_insensitive("windows");
}

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

struct VMVerboseStatePass : llvm::PassInfoMixin<VMVerboseStatePass> {
  std::string label_;

  explicit VMVerboseStatePass(llvm::StringRef label) : label_(label) {}

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
    unsigned handlers = 0;
    unsigned wrappers = 0;
    unsigned exact_hash_handlers = 0;
    unsigned demerged_clones = 0;
    unsigned dispatch_jumps = 0;
    unsigned dispatch_calls = 0;

    auto &virtual_callees = MAM.getResult<VirtualCalleeRegistryAnalysis>(M);
    size_t outlined_virtuals = virtual_callees.size();
    size_t outlined_hash_resolved = virtual_callees.countKind("hash_resolved");
    size_t outlined_nested_helper = virtual_callees.countKind("nested_helper");
    size_t outlined_trace_linked = virtual_callees.countTraceLinked();

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;

      if (F.hasFnAttribute("omill.vm_handler"))
        ++handlers;
      if (F.hasFnAttribute("omill.vm_wrapper"))
        ++wrappers;
      if (F.getFnAttribute("omill.vm_trace_in_hash").isValid())
        ++exact_hash_handlers;
      if (F.getFnAttribute("omill.vm_demerged_clone").isValid())
        ++demerged_clones;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;
          auto *callee = CB->getCalledFunction();
          if (!callee)
            continue;
          auto name = callee->getName();
          if (name == "__omill_dispatch_jump")
            ++dispatch_jumps;
          else if (name == "__omill_dispatch_call")
            ++dispatch_calls;
        }
      }
    }

    llvm::errs() << "[omill-vm] " << label_
                 << " handlers=" << handlers
                 << " wrappers=" << wrappers
                 << " exact=" << exact_hash_handlers
                 << " clones=" << demerged_clones
                 << " dispatch_jumps=" << dispatch_jumps
                 << " dispatch_calls=" << dispatch_calls
                 << " outlined_virtuals=" << outlined_virtuals
                 << " outlined_hash=" << outlined_hash_resolved
                 << " outlined_nested=" << outlined_nested_helper
                 << " trace_linked=" << outlined_trace_linked << "\n";
    return llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

void addVMVerboseMarker(llvm::ModulePassManager &MPM, llvm::StringRef label) {
  static bool enabled = (std::getenv("OMILL_VM_VERBOSE") != nullptr);
  if (enabled)
    MPM.addPass(VMVerboseStatePass(label));
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

bool envBoolEnabled(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return false;
  auto sv = llvm::StringRef(v).lower();
  return !(sv == "0" || sv == "false" || sv == "off" || sv == "no");
}

bool emitInlineDiagMarkers() {
  if (envBoolEnabled("OMILL_SKIP_INLINE_DIAG_MARKERS"))
    return false;
  const char *force = std::getenv("OMILL_INLINE_DIAG_MARKERS");
  if (!force || force[0] == '\0')
    return true;
  auto sv = llvm::StringRef(force).lower();
  return !(sv == "0" || sv == "false" || sv == "off" || sv == "no");
}

void emitInlineDiagMarker(llvm::CallBase &call, llvm::Function &callee,
                          llvm::StringRef phase) {
  auto *caller = call.getFunction();
  if (!caller)
    return;

  auto &M = *caller->getParent();
  auto &Ctx = M.getContext();
  auto *i8_ptr_ty = llvm::PointerType::getUnqual(Ctx);

  std::string text;
  llvm::raw_string_ostream os(text);
  os << "omill.inline phase=" << phase << "; caller=" << caller->getName()
     << "; callee=" << callee.getName();
  if (callee.getName().starts_with("sub_"))
    os << "; callee_va=0x" << llvm::utohexstr(extractEntryVA(callee.getName()));
  os.flush();

  auto *str_data = llvm::ConstantDataArray::getString(Ctx, text, true);
  auto *str_gv = new llvm::GlobalVariable(
      M, str_data->getType(), true, llvm::GlobalValue::PrivateLinkage, str_data,
      "__omill_inline_diag");
  str_gv->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
  str_gv->setAlignment(llvm::Align(1));
  str_gv->setSection(".omill.inline.diag");

  auto *sink = M.getGlobalVariable("__omill_inline_diag_sink");
  if (!sink) {
    sink = new llvm::GlobalVariable(
        M, i8_ptr_ty, false, llvm::GlobalValue::InternalLinkage,
        llvm::ConstantPointerNull::get(i8_ptr_ty), "__omill_inline_diag_sink");
    sink->setAlignment(llvm::Align(8));
    sink->setSection(".omill.inline.diag");
  }

  auto *zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(Ctx), 0);
  llvm::SmallVector<llvm::Constant *, 2> idxs{zero, zero};
  llvm::Constant *str_ptr = llvm::ConstantExpr::getInBoundsGetElementPtr(
      str_data->getType(), str_gv, idxs);
  if (str_ptr->getType() != i8_ptr_ty)
    str_ptr = llvm::ConstantExpr::getPointerCast(str_ptr, i8_ptr_ty);

  llvm::IRBuilder<> B(&call);
  auto *store = B.CreateStore(str_ptr, sink, /*isVolatile=*/true);
  store->setAlignment(llvm::Align(8));

  llvm::appendToUsed(M, {str_gv, sink});
}

/// Split large [N x i8] allocas into per-region allocas based on
/// constant-offset GEP clustering.  Enables SROA on oversized allocas
/// (e.g., 69KB native_stack from ABI recovery) that SROA skips.
struct SplitLargeAllocaPass
    : llvm::PassInfoMixin<SplitLargeAllocaPass> {
  static constexpr uint64_t kSizeThreshold = 4096;
  static constexpr int64_t kGapTolerance = 16;
  static constexpr int64_t kRegionPadding = 8;

  llvm::PreservedAnalyses run(llvm::Function &F,
                               llvm::FunctionAnalysisManager &) {
    if (F.isDeclaration())
      return llvm::PreservedAnalyses::all();

    auto &DL = F.getDataLayout();
    auto *i8_ty = llvm::Type::getInt8Ty(F.getContext());
    bool changed = false;

    llvm::SmallVector<llvm::AllocaInst *, 4> candidates;
    for (auto &I : F.getEntryBlock()) {
      auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
      if (!AI || AI->isArrayAllocation()) continue;
      auto *arr_ty = llvm::dyn_cast<llvm::ArrayType>(
          AI->getAllocatedType());
      if (!arr_ty) continue;
      if (arr_ty->getElementType() != i8_ty) continue;
      if (arr_ty->getNumElements() < kSizeThreshold) continue;
      candidates.push_back(AI);
    }

    for (auto *alloca : candidates) {
      struct GEPInfo {
        llvm::GetElementPtrInst *gep;
        int64_t offset;
      };
      llvm::SmallVector<GEPInfo, 32> gep_infos;
      llvm::SmallVector<llvm::MemSetInst *, 2> memsets;
      bool has_opaque_use = false;

      bool has_ptrtoint_escape = false;

      for (auto *user : alloca->users()) {
        if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(user)) {
          llvm::APInt ap_offset(64, 0);
          if (GEP->accumulateConstantOffset(DL, ap_offset)) {
            gep_infos.push_back({GEP, ap_offset.getSExtValue()});
          } else {
            has_opaque_use = true;
          }
          // Check if any user of this GEP is a ptrtoint.  A ptrtoint
          // escapes the alloca address and enables inttoptr-based stores
          // that may target offsets in different split regions.  Splitting
          // would break these cross-region references.
          for (auto *gep_user : GEP->users()) {
            if (llvm::isa<llvm::PtrToIntInst>(gep_user))
              has_ptrtoint_escape = true;
          }
        } else if (auto *MS = llvm::dyn_cast<llvm::MemSetInst>(user)) {
          memsets.push_back(MS);
        } else if (llvm::isa<llvm::PtrToIntInst>(user) ||
                   llvm::isa<llvm::BitCastInst>(user)) {
          has_opaque_use = true;
          has_ptrtoint_escape = true;
        } else {
          has_opaque_use = true;
        }
      }

      // If the alloca has a ptrtoint escape, don't split — inttoptr-based
      // stores derived from the ptrtoint (e.g., via VM hash addressing)
      // may target offsets that span multiple regions.  After splitting,
      // these cross-region inttoptr addresses become unresolvable by
      // ConcretizeAllocaPtrsPass, breaking store→load connections.
      // The late ConcretizeAllocaPtrs + VmContextSlotForwarding passes
      // can resolve the data flow when the alloca stays intact.
      if (has_ptrtoint_escape)
        continue;

      if (gep_infos.empty())
        continue;

      // Group offsets into contiguous regions.
      llvm::SmallVector<int64_t, 32> offsets;
      for (auto &gi : gep_infos)
        offsets.push_back(gi.offset);
      llvm::sort(offsets);
      offsets.erase(std::unique(offsets.begin(), offsets.end()),
                    offsets.end());

      struct Region { int64_t min_off, max_off; };
      llvm::SmallVector<Region, 8> regions;
      {
        int64_t cur_min = offsets[0], cur_max = offsets[0];
        for (size_t i = 1; i < offsets.size(); ++i) {
          if (offsets[i] - cur_max > kGapTolerance) {
            regions.push_back({cur_min, cur_max});
            cur_min = offsets[i];
          }
          cur_max = offsets[i];
        }
        regions.push_back({cur_min, cur_max});
      }

      // Create per-region allocas.
      llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
      struct RegionAlloca { int64_t min_off, max_off; llvm::AllocaInst *ai; };
      llvm::SmallVector<RegionAlloca, 8> region_allocas;
      for (auto &r : regions) {
        int64_t size = r.max_off - r.min_off + kRegionPadding;
        if (size <= 0) size = kRegionPadding;
        auto *ty = llvm::ArrayType::get(i8_ty, size);
        auto *ra = EntryBuilder.CreateAlloca(ty, nullptr, "split_region");
        region_allocas.push_back({r.min_off, r.max_off, ra});
      }

      // Rewrite GEPs.
      for (auto &gi : gep_infos) {
        for (auto &ra : region_allocas) {
          if (gi.offset >= ra.min_off && gi.offset <= ra.max_off) {
            llvm::IRBuilder<> Builder(gi.gep);
            auto *new_idx = llvm::ConstantInt::get(
                Builder.getInt64Ty(), gi.offset - ra.min_off);
            auto *new_gep = Builder.CreateGEP(
                i8_ty, ra.ai, new_idx, "split_ptr");
            gi.gep->replaceAllUsesWith(new_gep);
            gi.gep->eraseFromParent();
            changed = true;
            break;
          }
        }
      }

      // Initialize per-region allocas from original memsets.
      for (auto *MS : memsets) {
        auto *val = MS->getValue();
        bool is_volatile = MS->isVolatile();
        for (auto &ra : region_allocas) {
          int64_t size = ra.max_off - ra.min_off + kRegionPadding;
          llvm::IRBuilder<> Builder(MS);
          Builder.CreateMemSet(ra.ai, val, Builder.getInt64(size),
                                llvm::MaybeAlign(), is_volatile);
        }
        if (!has_opaque_use) {
          MS->eraseFromParent();
          changed = true;
        }
      }

      if (alloca->use_empty())
        alloca->eraseFromParent();
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

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
/// Pre-collects matching functions to guard against iterator invalidation
/// if the FPM creates new function declarations in the module.
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

    // Pre-collect matching functions to avoid iterator invalidation when
    // passes create new function declarations (e.g. __omill_dispatch_call).
    llvm::SmallVector<llvm::Function *, 32> worklist;
    for (auto &F : M) {
      if (F.isDeclaration() || !predicate(F))
        continue;
      worklist.push_back(&F);
    }

    bool changed = false;
    for (auto *F : worklist) {
      // Skip functions that became declarations during processing.
      if (F->isDeclaration())
        continue;
      auto PA = FPM.run(*F, FAM);
      if (!PA.areAllPreserved()) {
        changed = true;
        FAM.invalidate(*F, PA);
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

void buildCleanupPipeline(llvm::FunctionPassManager &FPM,
                          CleanupProfile profile) {
  switch (profile) {
    case CleanupProfile::kLightScalar:
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::DCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      break;
    case CleanupProfile::kStateToSSA:
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      break;
    case CleanupProfile::kPostInline:
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
      break;
    case CleanupProfile::kBoundary:
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      break;
    case CleanupProfile::kFinal:
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(llvm::AggressiveInstCombinePass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::DSEPass());
      break;
  }
}

void buildCleanupPipeline(llvm::ModulePassManager &MPM,
                          CleanupProfile profile) {
  llvm::FunctionPassManager FPM;
  buildCleanupPipeline(FPM, profile);
  MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  if (profile == CleanupProfile::kFinal)
    MPM.addPass(llvm::GlobalDCEPass());
}

void buildIntrinsicLoweringPipeline(llvm::FunctionPassManager &FPM) {
  // Order matters: flags first (expose SSA values), barriers (unblock opts),
  // then memory (biggest IR change), atomics, hypercalls.
  FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase1));

  // Cleanup
  buildCleanupPipeline(FPM, CleanupProfile::kLightScalar);
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

/// Repair malformed PHI nodes and strip alwaysinline from broken functions.
/// Must run before every AlwaysInlinerPass to prevent crashes in
/// CloneAndPruneFunctionInto (SEH 0xC0000005).
struct RepairBeforeInlinePass
    : llvm::PassInfoMixin<RepairBeforeInlinePass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F) {
        llvm::DenseMap<llvm::BasicBlock *, unsigned> pred_edge_count;
        for (auto *P : llvm::predecessors(&BB))
          ++pred_edge_count[P];
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
          if (!phi) break;
          for (unsigned i = phi->getNumIncomingValues(); i-- > 0;) {
            if (!pred_edge_count.count(phi->getIncomingBlock(i))) {
              phi->removeIncomingValue(i, /*DeletePHIIfEmpty=*/false);
              changed = true;
            }
          }
          llvm::DenseMap<llvm::BasicBlock *, unsigned> phi_count;
          for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i)
            ++phi_count[phi->getIncomingBlock(i)];
          for (auto &[pred, needed] : pred_edge_count) {
            unsigned have = phi_count.lookup(pred);
            if (have == 0) continue;
            for (unsigned j = have; j < needed; ++j) {
              phi->addIncoming(phi->getIncomingValueForBlock(pred), pred);
              changed = true;
            }
          }
          if (phi->getNumIncomingValues() == 0) {
            phi->replaceAllUsesWith(
                llvm::PoisonValue::get(phi->getType()));
            phi->eraseFromParent();
          }
        }
      }
      if (F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
        if (llvm::verifyFunction(F, &llvm::errs())) {
          llvm::errs() << "[repair] stripping alwaysinline from broken: "
                       << F.getName() << "\n";
          F.removeFnAttr(llvm::Attribute::AlwaysInline);
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

void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM,
                              const PipelineOptions &opts) {
  addPhaseMarker(MPM, "ABI: start (target-cpu)");

  // Set target-cpu on all functions so LLVM codegen emits inline CMPXCHG16B
  // instead of library calls for i128 cmpxchg.  x86-64-v2 implies +cx16.
  if (opts.target_arch == TargetArch::kX86_64 &&
      !envDisabled("OMILL_SKIP_ABI_TARGET_CPU")) {
    struct SetTargetCPUPass : llvm::PassInfoMixin<SetTargetCPUPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        bool changed = false;
        for (auto &F : M) {
          if (F.isDeclaration())
            continue;
          if (!F.hasFnAttribute("target-cpu")) {
            F.addFnAttr("target-cpu", "x86-64-v2");
            changed = true;
          }
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(SetTargetCPUPass{});
  }

  addPhaseMarker(MPM, "ABI: initial SROA+InstCombine");
  // Stack frame recovery runs per-function.
  if (!envDisabled("OMILL_SKIP_ABI_INITIAL_OPT")) {
    llvm::FunctionPassManager FPM;
    // Stack frame recovery already runs in state optimization.
    // Re-running it here can over-rewrite recovered stack-pointer arithmetic
    // in complex lifted functions and collapse control flow.
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "ABI: recover signatures");
  // Ensure LiftedFunctionAnalysis is cached — RewriteLiftedCallsToNative needs
  // it to resolve forward-declaration calls (sub_X → sub_X.N definition).
  MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis, llvm::Module>());

  // Signature recovery creates native wrappers; state elimination
  // internalizes the original lifted functions with alwaysinline.
  if (!envDisabled("OMILL_SKIP_ABI_RECOVER_SIGNATURES")) {
    MPM.addPass(RecoverFunctionSignaturesPass());
    addPhaseMarker(MPM, "ABI: rewrite lifted calls");
    MPM.addPass(RewriteLiftedCallsToNativePass());
    addPhaseMarker(MPM, "ABI: eliminate state struct");
    MPM.addPass(EliminateStateStructPass());
  }

  addPhaseMarker(MPM, "ABI: repair+inline lifted → native");
  MPM.addPass(RepairBeforeInlinePass{});
  if (!envDisabled("OMILL_SKIP_ABI_ALWAYS_INLINE")) {
    MPM.addPass(llvm::AlwaysInlinerPass());
  }
  addPhaseMarker(MPM, "ABI: rewrite lifted calls (post-inline)");

  // Inlining lifted functions into _native wrappers can re-introduce
  // dispatch_call/dispatch_jump artifacts. Rewrite again so wrappers don't
  // keep State alive due late-emitted dispatch shims.
  if (!envDisabled("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE")) {
    MPM.addPass(RewriteLiftedCallsToNativePass());
  }

  // Lower any remill intrinsics that survived into _native wrappers.
  // This happens when lifted functions still contain __remill_read_memory_*,
  // __remill_flag_computation_*, etc. (e.g., VM discovery callees that weren't
  // processed by the scoped Phase 1).  After AlwaysInlinerPass inlined those
  // lifted functions into _native wrappers, the intrinsic calls appear directly
  // in the wrapper bodies.  Lower them now before SROA decomposes the State.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(LowerRemillIntrinsicsPass(
        LowerCategories::Flags | LowerCategories::Barriers |
        LowerCategories::Memory | LowerCategories::Atomics |
        LowerCategories::HyperCalls | LowerCategories::ErrorMissing |
        LowerCategories::Undefined));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  addPhaseMarker(MPM, "ABI: DSE+SROA+i128");
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
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }
    addPhaseMarker(MPM, "ABI: final-opt SHR+MBA");
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(SimplifyVectorReassemblyPass());
      FPM.addPass(CollapseRemillSHRSwitchPass());
#if OMILL_ENABLE_SIMPLIFIER
      FPM.addPass(SimplifyMBAPass());
#endif
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }
    addPhaseMarker(MPM, "ABI: final-opt GVN+Type+ADCE");
    {
      llvm::FunctionPassManager FPM;
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
  }

  addPhaseMarker(MPM, "ABI: fold const-ret + trace counters");
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
        // Mark VM handler functions for inlining and collect caller names
        // so we can find them after inlining (Function* may be invalidated).
        auto &virtual_callees =
            MAM.getResult<VirtualCalleeRegistryAnalysis>(M);
        bool has_vm_handlers = false;
        llvm::SmallVector<std::string, 16> caller_names;
        llvm::DenseSet<llvm::Function *> inline_targets;
        for (auto &F : M) {
          if (!F.hasFnAttribute("omill.vm_handler"))
            continue;
          // Handle both cases: _native wrappers (if they exist) and
          // original lifted functions (when RecoverFunctionSignatures
          // skipped them).
          if (!F.getName().ends_with("_native") &&
              M.getFunction((F.getName() + "_native").str()))
            continue;  // Has a _native wrapper — skip the original.
          // The VM wrapper is a boundary function — handlers are inlined
          // INTO it, but it must NOT be inlined into its callers (e.g.
          // DriverEntry). Demerged clone wrappers and registry-modeled
          // outlined virtual callees must also remain outlined so recovered
          // virtualized callees survive as separate functions.
          if (F.hasFnAttribute("omill.vm_wrapper") ||
              F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
              F.getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
              virtual_callees.lookup(F.getName()).has_value())
            continue;
          // Only inline VM handlers that have callers.  Uncalled handlers
          // (deferred functions whose addresses weren't resolved to direct
          // calls) must be kept — they're still reachable via indirect
          // dispatch at runtime.
          if (F.use_empty())
            continue;
          F.setLinkage(llvm::GlobalValue::InternalLinkage);
          F.removeFnAttr(llvm::Attribute::NoInline);
          F.addFnAttr(llvm::Attribute::AlwaysInline);
          has_vm_handlers = true;
          inline_targets.insert(&F);
          for (auto *U : F.users()) {
            if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
              caller_names.push_back(CB->getFunction()->getName().str());
          }
        }
        if (!has_vm_handlers)
          return llvm::PreservedAnalyses::all();

        if (emitInlineDiagMarkers()) {
          for (auto *handler : inline_targets) {
            for (auto *U : handler->users()) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
              if (!CB)
                continue;
              emitInlineDiagMarker(*CB, *handler, "abi_vm_handler_inline");
            }
          }
        }

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
          buildCleanupPipeline(FPM, CleanupProfile::kPostInline);
          llvm::DenseSet<llvm::Function *> seen;
          for (const auto &name : caller_names) {
            auto *F = M.getFunction(name);
            if (!F || F->isDeclaration() || !seen.insert(F).second)
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

        // Cross-link registry records against the emulator trace map so the
        // downstream VMDeadMergedHandlerElimination pass has trace coverage.
        auto &trace_map = MAM.getResult<VMTraceMapAnalysis>(M);
        if (unsigned linked = virtual_callees.linkToTraceMap(trace_map)) {
          static bool vm_verbose =
              (std::getenv("OMILL_VM_VERBOSE") != nullptr);
          if (vm_verbose)
            llvm::errs() << "[omill] trace-linked " << linked
                         << " virtual callee records\n";
        }


        return llvm::PreservedAnalyses::none();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(InlineVMHandlersAndCleanupPass{});
    // After ABI-phase handler inlining, remove fully-demerged merged bodies.
    MPM.addPass(VMDeadMergedHandlerEliminationPass());
  }
  addPhaseMarker(MPM, "ABI: final cleanup");
  // Strip @llvm.compiler.used and run GlobalDCE to remove dead ISEL stubs.
  if (!envDisabled("OMILL_SKIP_STRIP_COMPILER_USED")) {
    MPM.addPass(StripCompilerUsedPass());
    MPM.addPass(llvm::GlobalDCEPass());
  }

  addPhaseMarker(MPM, "ABI: synthetic stack cleanup");
  if (!envDisabled("OMILL_SKIP_ABI_SYNTHETIC_STACK_CLEANUP")) {
    struct SentinelMemoryEliminationPass
        : llvm::PassInfoMixin<SentinelMemoryEliminationPass> {
      llvm::PreservedAnalyses run(llvm::Function &F,
                                   llvm::FunctionAnalysisManager &) {
        if (F.isDeclaration())
          return llvm::PreservedAnalyses::all();

        auto isSentinel = [](uint64_t v) -> bool {
          return v == 0xCCCCCCCCCCCCCCCCULL ||
                 v == 0xCDCDCDCDCDCDCDCDULL ||
                 v == 0xCCCCCCCCULL ||
                 v == 0xCDCDCDCDULL;
        };

        auto isSentinelPtr = [&](llvm::Value *ptr) -> bool {
          if (auto *i2p = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
            auto *ci = llvm::dyn_cast<llvm::ConstantInt>(i2p->getOperand(0));
            return ci && isSentinel(ci->getZExtValue());
          }
          auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(ptr);
          if (!ce || ce->getOpcode() != llvm::Instruction::IntToPtr)
            return false;
          auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
          return ci && isSentinel(ci->getZExtValue());
        };

        bool changed = false;
        llvm::SmallVector<llvm::Instruction *, 8> to_erase;
        for (auto &BB : F) {
          for (auto &I : BB) {
            if (auto *ms = llvm::dyn_cast<llvm::MemSetInst>(&I)) {
              if (auto *fill = llvm::dyn_cast<llvm::ConstantInt>(ms->getValue())) {
                uint8_t v = static_cast<uint8_t>(fill->getZExtValue());
                if (v == 0xCC || v == 0xCD) {
                  ms->setValue(llvm::ConstantInt::get(fill->getType(), 0));
                  changed = true;
                }
              }
              continue;
            }
            if (auto *cx = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(&I)) {
              if (isSentinelPtr(cx->getPointerOperand())) {
                cx->replaceAllUsesWith(llvm::PoisonValue::get(cx->getType()));
                to_erase.push_back(cx);
                changed = true;
              }
              continue;
            }
            if (auto *ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
              if (isSentinelPtr(ld->getPointerOperand())) {
                ld->replaceAllUsesWith(llvm::PoisonValue::get(ld->getType()));
                to_erase.push_back(ld);
                changed = true;
              }
              continue;
            }
            if (auto *st = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              if (isSentinelPtr(st->getPointerOperand())) {
                to_erase.push_back(st);
                changed = true;
              }
            }
          }
        }
        for (auto *I : to_erase)
          I->eraseFromParent();
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };

    struct ResolveIntToPtrCallsPass
        : llvm::PassInfoMixin<ResolveIntToPtrCallsPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &MAM) {
        auto *lifted = MAM.getCachedResult<LiftedFunctionAnalysis>(M);
        if (!lifted)
          return llvm::PreservedAnalyses::all();

        bool changed = false;
        for (auto &F : M) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->getCalledFunction())
                continue;

              auto *callee_val = call->getCalledOperand()->stripPointerCasts();
              llvm::ConstantInt *addr_ci = nullptr;
              if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_val)) {
                if (ce->getOpcode() == llvm::Instruction::IntToPtr)
                  addr_ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
              }
              if (!addr_ci) {
                if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_val))
                  addr_ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
              }
              if (!addr_ci)
                continue;

              auto *target_fn = lifted->lookup(addr_ci->getZExtValue());
              if (!target_fn)
                continue;
              auto *native_fn =
                  M.getFunction((target_fn->getName() + "_native").str());
              if (!native_fn)
                continue;

              auto *native_ty = native_fn->getFunctionType();
              unsigned n = std::min<unsigned>(native_ty->getNumParams(),
                                              call->arg_size());
              llvm::SmallVector<llvm::Value *, 8> args;
              llvm::IRBuilder<> B(call);
              for (unsigned i = 0; i < n; ++i) {
                auto *arg = call->getArgOperand(i);
                auto *expected = native_ty->getParamType(i);
                if (arg->getType() != expected) {
                  if (arg->getType()->isIntegerTy() && expected->isIntegerTy())
                    arg = B.CreateIntCast(arg, expected, false);
                  else if (arg->getType()->isPointerTy() && expected->isIntegerTy())
                    arg = B.CreatePtrToInt(arg, expected);
                  else if (arg->getType()->isIntegerTy() && expected->isPointerTy())
                    arg = B.CreateIntToPtr(arg, expected);
                  else
                    arg = B.CreateBitCast(arg, expected);
                }
                args.push_back(arg);
              }
              for (unsigned i = n; i < native_ty->getNumParams(); ++i)
                args.push_back(llvm::PoisonValue::get(native_ty->getParamType(i)));

              auto *new_call = B.CreateCall(native_fn, args);
              new_call->setCallingConv(native_fn->getCallingConv());
              if (call->getType() == new_call->getType()) {
                call->replaceAllUsesWith(new_call);
              } else if (!call->getType()->isVoidTy()) {
                llvm::Value *result = new_call;
                if (new_call->getType()->isVoidTy()) {
                  result = llvm::PoisonValue::get(call->getType());
                } else if (call->getType()->isIntegerTy() &&
                           new_call->getType()->isIntegerTy()) {
                  result = B.CreateIntCast(new_call, call->getType(), false);
                } else if (call->getType()->isPointerTy() &&
                           new_call->getType()->isIntegerTy()) {
                  result = B.CreateIntToPtr(new_call, call->getType());
                } else if (call->getType()->isIntegerTy() &&
                           new_call->getType()->isPointerTy()) {
                  result = B.CreatePtrToInt(new_call, call->getType());
                } else {
                  result = B.CreateBitCast(new_call, call->getType());
                }
                call->replaceAllUsesWith(result);
              }
              call->eraseFromParent();
              changed = true;
            }
          }
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };

    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(SentinelMemoryEliminationPass{});
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }

    if (!envDisabled("OMILL_SKIP_CONCRETIZE_ALLOCA_PTRS")) {
      llvm::FunctionPassManager FPM;
      FPM.addPass(RecoverAllocaPointersPass());
      FPM.addPass(llvm::DSEPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }

    if (!envDisabled("OMILL_SKIP_POST_ABI_INLINE")) {
      struct PreserveOutlinedWrappersPass
          : llvm::PassInfoMixin<PreserveOutlinedWrappersPass> {
        llvm::PreservedAnalyses run(llvm::Module &M,
                                     llvm::ModuleAnalysisManager &MAM) {
          bool changed = false;
          auto &virtual_callees =
              MAM.getResult<VirtualCalleeRegistryAnalysis>(M);
          for (auto &F : M) {
            if (F.isDeclaration())
              continue;
            if (F.hasFnAttribute("omill.vm_wrapper") ||
                F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
                F.getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
                virtual_callees.lookup(F.getName()).has_value()) {
              if (!F.hasFnAttribute(llvm::Attribute::NoInline)) {
                F.addFnAttr(llvm::Attribute::NoInline);
                changed = true;
              }
            }
          }
          return changed ? llvm::PreservedAnalyses::none()
                         : llvm::PreservedAnalyses::all();
        }
        static bool isRequired() { return true; }
      };

      MPM.addPass(PreserveOutlinedWrappersPass{});
      llvm::InlineParams params = llvm::getInlineParams(50);
      MPM.addPass(llvm::ModuleInlinerWrapperPass(params));
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      }
      if (!envDisabled("OMILL_SKIP_SPLIT_LARGE_ALLOCA")) {
        llvm::FunctionPassManager FPM;
        FPM.addPass(SplitLargeAllocaPass{});
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      }
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(RecoverStackFramePass{});
        buildCleanupPipeline(FPM, CleanupProfile::kBoundary);
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      }
      MPM.addPass(llvm::GlobalDCEPass());
    }

    if (!envDisabled("OMILL_SKIP_RESOLVE_INTTOPTR_CALLS")) {
      MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis,
                                            llvm::Module>());
      MPM.addPass(ResolveIntToPtrCallsPass{});
    }
  }
}

void buildDeobfuscationPipeline(llvm::FunctionPassManager &FPM,
                                const PipelineOptions &opts) {
  const bool is_windows = isWindowsTargetOS(opts.target_os);

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
  if (is_windows && !envDisabled("OMILL_SKIP_DEOBF_HASH_IMPORTS")) {
    FPM.addPass(HashImportAnnotationPass());
  }
  // Replace lazy_importer resolution with direct import references.
  if (is_windows && !envDisabled("OMILL_SKIP_DEOBF_RESOLVE_LAZY")) {
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

/// Unprotect semantic functions so AlwaysInlinerPass can inline them.
///
/// During a pipeline re-run (e.g. VM discovery rounds), semantic functions
/// are already protected with optnone+noinline from the first run's
/// ProtectRemillSemanticsPass.  This pass reverses the protection so that
/// AlwaysInlinerPass can inline semantics into newly lifted functions.
/// On the first pipeline run this is a no-op (nothing is protected yet).
struct UnprotectRemillSemanticsPass
    : llvm::PassInfoMixin<UnprotectRemillSemanticsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      if (F.hasFnAttribute(llvm::Attribute::AlwaysInline)) continue;
      auto name = F.getName();
      if (name.starts_with("sub_") || name.starts_with("block_") ||
          name.starts_with("__remill_") || name.starts_with("__omill_"))
        continue;
      F.removeFnAttr(llvm::Attribute::OptimizeNone);
      F.removeFnAttr(llvm::Attribute::NoInline);
      F.addFnAttr(llvm::Attribute::AlwaysInline);
      changed = true;
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

/// Resolve inttoptr(ptrtoint(alloca) ± δ) → GEP alloca, δ.
/// After VM handler inlining, the vmcontext alloca has a self-referencing
/// pointer: ptrtoint(alloca+off) is stored to a field, handlers reload it
/// and do `add delta / inttoptr / load|store`.  This pass forward-propagates
/// the ptrtoint-derived value through store→load pairs within the same alloca
/// and replaces each inttoptr with a direct GEP, enabling alias analysis and
/// downstream DSE/GVN.
struct ConcretizeAllocaPtrsPass
    : llvm::PassInfoMixin<ConcretizeAllocaPtrsPass> {

  /// Get the alloca and constant byte offset behind a pointer value.
  static std::pair<llvm::AllocaInst *, int64_t>
  getAllocaAndOffset(llvm::Value *ptr) {
    auto *base = ptr->stripInBoundsConstantOffsets();
    auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(base);
    if (!alloca)
      return {nullptr, 0};
    auto &DL = alloca->getDataLayout();
    llvm::APInt offset(DL.getPointerSizeInBits(), 0);
    if (ptr->stripAndAccumulateConstantOffsets(DL, offset,
                                               /*AllowNonInbounds=*/true))
      return {alloca, offset.getSExtValue()};
    return {nullptr, 0};
  }

  /// Get the total byte size of an alloca.
  static uint64_t getAllocaSize(llvm::AllocaInst *A) {
    auto &DL = A->getDataLayout();
    auto ty_size = DL.getTypeAllocSize(A->getAllocatedType());
    if (A->isArrayAllocation())
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(A->getArraySize()))
        return ty_size * CI->getZExtValue();
    return ty_size;
  }

  llvm::PreservedAnalyses run(llvm::Function &F,
                               llvm::FunctionAnalysisManager &) {
    if (F.isDeclaration() || F.empty())
      return llvm::PreservedAnalyses::all();

    // Phase 1: collect ptrtoint seeds from allocas in all blocks.
    // We scan beyond the entry block because SimplifyCFG / switch lowering
    // can move ptrtoint instructions into successor blocks (e.g., after an
    // early-exit switch on KUSER_SHARED_DATA).
    struct Seed {
      llvm::PtrToIntInst *pti;
      llvm::AllocaInst *alloca;
      int64_t base_offset;
    };
    llvm::SmallVector<Seed, 4> seeds;

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *pti = llvm::dyn_cast<llvm::PtrToIntInst>(&I);
        if (!pti)
          continue;
        auto [alloca, off] = getAllocaAndOffset(pti->getPointerOperand());
        if (!alloca)
          continue;
        seeds.push_back({pti, alloca, off});
      }
    }

    if (seeds.empty())
      return llvm::PreservedAnalyses::all();

    // Phase 2: BFS from each seed — track (Value, offset) pairs.
    struct StoreRec {
      llvm::AllocaInst *alloca;
      int64_t field_offset;
      int64_t ptr_offset;
    };
    struct ReplaceRec {
      llvm::IntToPtrInst *itp;
      llvm::AllocaInst *alloca;
      int64_t offset;
    };

    llvm::SmallVector<StoreRec, 8> stores;
    llvm::SmallVector<ReplaceRec, 64> replacements;
    // Map from ptrtoint-derived Value → (alloca, accumulated byte offset).
    struct ValInfo {
      llvm::AllocaInst *alloca;
      int64_t offset;
    };
    llvm::DenseMap<llvm::Value *, ValInfo> val_info;
    llvm::DenseSet<llvm::Value *> visited;

    struct WorkItem {
      llvm::Value *val;
      int64_t offset;
      llvm::AllocaInst *alloca;
    };
    llvm::SmallVector<WorkItem, 64> worklist;

    auto traceArithmetic = [&](llvm::Value *val, int64_t offset,
                                llvm::AllocaInst *alloca,
                                llvm::User *U) -> bool {
      auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(U);
      if (!bin)
        return false;
      if (bin->getOpcode() != llvm::Instruction::Add &&
          bin->getOpcode() != llvm::Instruction::Sub)
        return false;
      auto *lhs_ci =
          llvm::dyn_cast<llvm::ConstantInt>(bin->getOperand(0));
      auto *rhs_ci =
          llvm::dyn_cast<llvm::ConstantInt>(bin->getOperand(1));
      llvm::ConstantInt *ci = nullptr;
      bool val_is_lhs = (bin->getOperand(0) == val);
      if (val_is_lhs)
        ci = rhs_ci;
      else
        ci = lhs_ci;
      if (!ci)
        return false;
      int64_t delta = ci->getSExtValue();
      int64_t new_off;
      if (bin->getOpcode() == llvm::Instruction::Add) {
        new_off = offset + delta;
      } else {
        if (val_is_lhs)
          new_off = offset - delta;
        else
          return false;
      }
      worklist.push_back({bin, new_off, alloca});
      return true;
    };

    for (auto &s : seeds)
      worklist.push_back({s.pti, s.base_offset, s.alloca});

    while (!worklist.empty()) {
      auto [val, offset, alloca] = worklist.pop_back_val();
      if (!visited.insert(val).second)
        continue;
      val_info[val] = {alloca, offset};

      for (auto *U : val->users()) {
        if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(U)) {
          traceArithmetic(val, offset, alloca, bin);
          continue;
        }
        if (auto *si = llvm::dyn_cast<llvm::StoreInst>(U)) {
          if (si->getValueOperand() != val)
            continue;
          auto [st_alloca, st_off] =
              getAllocaAndOffset(si->getPointerOperand());
          if (st_alloca == alloca)
            stores.push_back({alloca, st_off, offset});
          continue;
        }
        if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(U)) {
          replacements.push_back({itp, alloca, offset});
          continue;
        }
      }
    }

    // Phase 3: iterative store-load forwarding with reaching-definitions.
    // The vmcontext self-reference pointer can be stored to field A, loaded
    // from A, then re-stored to field B, loaded from B, etc.  We iterate
    // until no new forwarded values are discovered.
    using FieldKey = std::pair<llvm::AllocaInst *, int64_t>;

    for (int iter = 0; iter < 8; ++iter) {
      size_t prev_val_info_size = val_info.size();

      // Build a set of tracked fields for reaching-definitions kill.
      llvm::DenseSet<FieldKey> tracked_fields;
      for (auto &sr : stores)
        tracked_fields.insert({sr.alloca, sr.field_offset});
      // Also track any field whose stored value is in val_info.
      for (auto &[val, info] : val_info) {
        for (auto *U : val->users()) {
          auto *si = llvm::dyn_cast<llvm::StoreInst>(U);
          if (!si || si->getValueOperand() != val)
            continue;
          auto [st_alloca, st_off] =
              getAllocaAndOffset(si->getPointerOperand());
          if (st_alloca)
            tracked_fields.insert({st_alloca, st_off});
        }
      }

      // Forward scan each basic block.
      for (auto &BB : F) {
        llvm::DenseMap<FieldKey, int64_t> current;

        for (auto &I : BB) {
          if (auto *si = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            auto [st_alloca, st_off] =
                getAllocaAndOffset(si->getPointerOperand());
            if (!st_alloca)
              continue;
            FieldKey key{st_alloca, st_off};
            auto vi = val_info.find(si->getValueOperand());
            if (vi != val_info.end() && vi->second.alloca == st_alloca) {
              current[key] = vi->second.offset;
            } else if (tracked_fields.count(key)) {
              current.erase(key);
            }
            continue;
          }

          auto *ld = llvm::dyn_cast<llvm::LoadInst>(&I);
          if (!ld || !ld->getType()->isIntegerTy())
            continue;
          auto [ld_alloca, ld_off] =
              getAllocaAndOffset(ld->getPointerOperand());
          if (!ld_alloca)
            continue;
          FieldKey key{ld_alloca, ld_off};
          auto it = current.find(key);
          if (it != current.end())
            worklist.push_back({ld, it->second, ld_alloca});
        }
      }

      // BFS: trace forwarded values through arithmetic, stores, and inttoptr.
      while (!worklist.empty()) {
        auto [val, offset, alloca] = worklist.pop_back_val();
        if (!visited.insert(val).second)
          continue;
        val_info[val] = {alloca, offset};

        for (auto *U : val->users()) {
          if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(U)) {
            traceArithmetic(val, offset, alloca, bin);
            continue;
          }
          if (auto *si = llvm::dyn_cast<llvm::StoreInst>(U)) {
            if (si->getValueOperand() != val)
              continue;
            auto [st_alloca, st_off] =
                getAllocaAndOffset(si->getPointerOperand());
            if (st_alloca == alloca)
              stores.push_back({alloca, st_off, offset});
            continue;
          }
          if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(U)) {
            replacements.push_back({itp, alloca, offset});
            continue;
          }
        }
      }

      // Fixed point: stop if no new val_info entries were discovered.
      if (val_info.size() == prev_val_info_size)
        break;
    }

    if (replacements.empty())
      return llvm::PreservedAnalyses::all();

    // Phase 4: replace inttoptr with GEP.
    bool changed = false;
    for (auto &r : replacements) {
      uint64_t alloca_size = getAllocaSize(r.alloca);
      if (r.offset < 0 || static_cast<uint64_t>(r.offset) >= alloca_size)
        continue;
      llvm::IRBuilder<> builder(r.itp);
      auto *gep = builder.CreateInBoundsGEP(
          builder.getInt8Ty(), r.alloca,
          builder.getInt64(r.offset));
      r.itp->replaceAllUsesWith(gep);
      r.itp->eraseFromParent();
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

}  // namespace

static void buildPreResolutionPipeline(llvm::ModulePassManager &MPM,
                                       const PipelineOptions &opts) {
  // Reset the phase timer origin on each pipeline build.
  PhaseMarkerPass::origin() = PhaseMarkerPass::Clock::now();
  addPhaseMarker(MPM, "Phase 0: start");

  const bool is_windows = isWindowsTargetOS(opts.target_os);

  // Stamp target architecture metadata so downstream analyses can query it.
  {
    auto arch = opts.target_arch;
    auto os = opts.target_os;
    struct StampTargetArchPass : llvm::PassInfoMixin<StampTargetArchPass> {
      TargetArch arch;
      std::string os;
      StampTargetArchPass(TargetArch a, std::string o)
          : arch(a), os(std::move(o)) {}
      llvm::PreservedAnalyses run(llvm::Module &M,
                                  llvm::ModuleAnalysisManager &) {
        setTargetArchMetadata(M, arch, os);
        return llvm::PreservedAnalyses::all();
      }
      static llvm::StringRef name() { return "StampTargetArchPass"; }
    };
    MPM.addPass(StampTargetArchPass(arch, os));
  }

  // Phase 0: Strip remill intrinsic bodies to prevent AlwaysInlinerPass from
  // inlining them via call-site alwaysinline attributes.  Their bodies contain
  // switch/unreachable patterns that poison the entire function's control flow.
  MPM.addPass(StripRemillIntrinsicBodiesPass());

  // Helper: wrap FPM in a scoped adaptor when a scope predicate is set,
  // otherwise use the standard module-to-function adaptor.
  auto addScopedFPM = [&](llvm::FunctionPassManager FPM) {
    if (opts.scope_predicate) {
      MPM.addPass(createScopedFPM(std::move(FPM), opts.scope_predicate));
    } else {
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }
  };

  // Phase 0: Externalize semantic functions BEFORE AlwaysInliner.
  // The ~2000 semantic functions live in anonymous C++ namespaces and have
  // internal linkage by construction.  AlwaysInlinerPass inlines them into
  // lifted traces, then replaces the original bodies with unreachable
  // (internal + no callers = dead).  Promoting to external prevents this
  // body destruction, keeping the bodies available for VM handler functions
  // discovered later in Phase 3.6.
  MPM.addPass(ExternalizeRemillSemanticsPass());

  // Phase 0: Unprotect semantics (no-op on first run; needed for re-runs
  // where ProtectRemillSemanticsPass already added optnone+noinline).
  MPM.addPass(UnprotectRemillSemanticsPass());

  // Phase 0: Inline remill's alwaysinline semantic functions so that
  // subsequent passes can see through them.
  MPM.addPass(RepairBeforeInlinePass{});
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
    addScopedFPM(std::move(FPM));
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
    addScopedFPM(std::move(FPM));
  }

  // Synthesize flag patterns: after SROA/mem2reg promotes flag values to
  // SSA, recognize xor(SF, OF) patterns and fold to icmp slt.  Follow
  // with InstCombine to fold compound patterns (JGE, JLE, JG).
  if (!envDisabled("OMILL_SKIP_SYNTHESIZE_FLAGS")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(SynthesizeFlagsPass());
    FPM.addPass(llvm::InstCombinePass());
    addScopedFPM(std::move(FPM));
  }

  // In staged test flows, stop here to avoid running later phases on
  // partially-lowered IR.  Internalize + DCE semantics since the late
  // internalize (Phase 3.6→3.7 boundary) won't run.
  if (opts.stop_after_state_optimization) {
    if (opts.preserve_lifted_semantics)
      return;
    MPM.addPass(InternalizeRemillSemanticsPass());
    MPM.addPass(llvm::GlobalDCEPass());
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
      if (is_windows)
        FPM.addPass(ResolveForcedExceptionsPass());
    }
    addScopedFPM(std::move(FPM));

    // Inline exception handlers into their callers.  This is critical:
    // CFF handlers are trampolines that call resolvers.  Without inlining,
    // ABI recovery creates a native wrapper for the handler that drops XMM
    // values (the handler doesn't use XMMs directly), so the resolver's SSE
    // computation gets all-zero XMM inputs and folds to ret 0.
    // Inlining merges the handler body into the caller (which HAS XMM values),
    // preserving the full State across the call chain.
    if (!envDisabled("OMILL_SKIP_CF_HANDLER_INLINE")) {
      MPM.addPass(RepairBeforeInlinePass{});
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
    addScopedFPM(std::move(FPM));
  }

  addPhaseMarker(MPM, "Phase 3.5: fold PC + IAT");
  // Phase 3.5: Fold program_counter to a constant and resolve IAT-indirect
  // dispatch_calls before ABI recovery eliminates program_counter.
  if (!envDisabled("OMILL_SKIP_PHASE35")) {
    MPM.addPass(llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(FoldProgramCounterPass());
    FPM.addPass(llvm::InstCombinePass());
    if (is_windows)
      FPM.addPass(ResolveIATCallsPass());
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    addScopedFPM(std::move(FPM));
  }

  // Phase 3.55: Proactive jump table concretization.
  // Runs after Phase 3.5 has folded program_counter and resolved IAT calls,
  // but before iterative target resolution.  Converts dispatch_jump sites
  // with jump table patterns (base + idx * stride loads from binary memory)
  // into switch instructions.
  if (opts.resolve_indirect_targets || opts.use_block_lifting) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(JumpTableConcretizerPass());
    addScopedFPM(std::move(FPM));
  }

  addPhaseMarker(MPM, "Phase 3.56: VM devirtualization");
  // Phase 3.56: VM Devirtualization.
  // Resolve handler dispatch targets from the emulator-derived flat trace map.
  // Must run after Phase 3 has lowered __remill_jump to __omill_dispatch_jump
  // and before Phase 3.6 resolves them.
  if (opts.vm_devirtualize) {
    addVMVerboseMarker(MPM, "vm.pre-dispatch-resolution");
    // Resolve opaque dispatch targets using the trace map.
    MPM.addPass(VMDispatchResolutionPass());
    addVMVerboseMarker(MPM, "vm.post-dispatch-resolution");

    // Lower resolved dispatch targets to direct calls.
    {
      llvm::FunctionPassManager FPM;
      // Convert dispatch_jump/dispatch_call with constant targets to
      // direct calls/branches (required for VMHandlerInlinerPass below).
      FPM.addPass(
          ResolveAndLowerControlFlowPass(ResolvePhases::ResolveTargets));
      FPM.addPass(
          LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }
    addVMVerboseMarker(MPM, "vm.post-resolved-dispatch-lowering");

    addPhaseMarker(MPM, "Phase 3.56: VM handler inlining");
    // Inline small handler calls. VMHandlerInlinerPass performs its own
    // inlining via llvm::InlineFunction and erases dead handlers, so no
    // separate AlwaysInlinerPass is needed.
    MPM.addPass(VMHandlerInlinerPass(/*max_handler_instrs=*/500,
                                     /*min_callsites=*/1));
    addVMVerboseMarker(MPM, "vm.post-handler-inlining");

    addPhaseMarker(MPM, "Phase 3.56: post-handler cleanup");
    // Clean up after handler inlining — scoped to functions that
    // VMHandlerInlinerPass tagged with "omill.needs_cleanup".
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(RecoverAllocaPointersPass());
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
    addVMVerboseMarker(MPM, "vm.post-handler-cleanup");

    // Eliminate merged handler bodies that have been fully demerged.
    // After VMHandlerInliner inlines handlers into callers, merged bodies
    // that are fully covered (every incoming hash has a demerged clone)
    // and have no remaining uses can be safely deleted.
    MPM.addPass(VMDeadMergedHandlerEliminationPass());
    addVMVerboseMarker(MPM, "vm.post-dead-merged-elimination");
  }

}

static void buildStandaloneInterproceduralResolutionEpoch(
    llvm::ModulePassManager &MPM) {
  addPhaseMarker(MPM, "Phase 3.7: IPCP");
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
  MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *Callee = CI->getCalledFunction()) {
            auto name = Callee->getName();
            if (name == "__omill_dispatch_call" ||
                name == "__omill_dispatch_jump")
              return true;
          }
    return false;
  }));
}

static void buildIterativeResolutionEpoch(llvm::ModulePassManager &MPM,
                                          const PipelineOptions &opts) {
  addPhaseMarker(MPM, "Phase 3.6: iterative target resolution");
  if (opts.use_block_lifting) {
    MPM.addPass(IterativeBlockDiscoveryPass(opts.max_resolution_iterations));
    if (opts.merge_block_functions_after_fixpoint) {
      MPM.addPass(MergeBlockFunctionsPass());
      MPM.addPass(llvm::GlobalDCEPass());
    }
  } else if (opts.resolve_indirect_targets) {
    MPM.addPass(IterativeTargetResolutionPass(
        opts.max_resolution_iterations, opts.run_ipcp_inside_resolution));
  }

  if (opts.interprocedural_const_prop &&
      (!opts.resolve_indirect_targets || !opts.run_ipcp_inside_resolution)) {
    buildStandaloneInterproceduralResolutionEpoch(MPM);
  }
}

static void buildBoundaryLoweringPipeline(llvm::ModulePassManager &MPM,
                                          const PipelineOptions &opts) {
  addPhaseMarker(MPM, "Phase 4: ABI recovery");
  if (opts.recover_abi) {
    buildABIRecoveryPipeline(MPM, opts);
    if (opts.refine_signatures)
      MPM.addPass(RefineFunctionSignaturesPass());
  }
}

static void buildFinalCleanupPipeline(llvm::ModulePassManager &MPM,
                                      const PipelineOptions &opts) {
  addPhaseMarker(MPM, "Phase 5: deobfuscation");
  if (opts.deobfuscate) {
    MPM.addPass(llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    buildDeobfuscationPipeline(FPM, opts);
    MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
      return F.getName().ends_with("_native");
    }));
  }

  if (opts.vm_devirtualize && opts.deobfuscate &&
      !envDisabled("OMILL_SKIP_VM_HANDLER_INLINE")) {
    MPM.addPass(VMHandlerInlinerPass());
    llvm::FunctionPassManager FPM;
    buildCleanupPipeline(FPM, CleanupProfile::kBoundary);
    MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
      if (!F.hasFnAttribute("omill.needs_cleanup"))
        return false;
      F.removeFnAttr("omill.needs_cleanup");
      return true;
    }));
  }

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

  if (!opts.preserve_lifted_semantics)
    buildLiftInfrastructureCleanupPipeline(MPM);

  addPhaseMarker(MPM, "Final: cleanup");
  MPM.addPass(llvm::GlobalDCEPass());
}

void buildPipeline(llvm::ModulePassManager &MPM, const PipelineOptions &opts) {
  buildPreResolutionPipeline(MPM, opts);
  if (opts.stop_after_state_optimization)
    return;
  buildIterativeResolutionEpoch(MPM, opts);
  buildBoundaryLoweringPipeline(MPM, opts);
  buildFinalCleanupPipeline(MPM, opts);
}

void buildLateCleanupPipeline(llvm::ModulePassManager &MPM) {
  // Eliminate calls to unresolved remill-signature semantic functions.
  // After the full pipeline + ABI recovery, any remaining
  //   declare ptr @sub_*(ptr noalias, i64, ptr noalias)
  // is a residual from failed dispatch resolution (bogus address outside
  // the binary image).  Replace all calls with unreachable.
  if (!envDisabled("OMILL_SKIP_DEAD_SEMANTIC_ELIM")) {
    struct DeadSemanticCallEliminationPass
        : llvm::PassInfoMixin<DeadSemanticCallEliminationPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        // Identify unresolved remill-signature declarations:
        //   declare ptr @sub_*(ptr noalias, i64, ptr noalias)
        llvm::SmallVector<llvm::Function *, 16> dead_semantics;
        auto *ptr_ty = llvm::PointerType::getUnqual(M.getContext());
        auto *i64_ty = llvm::Type::getInt64Ty(M.getContext());
        for (auto &F : M) {
          if (!F.isDeclaration()) continue;
          if (!F.getName().starts_with("sub_")) continue;
          auto *FT = F.getFunctionType();
          if (FT->getNumParams() != 3) continue;
          if (FT->getReturnType() != ptr_ty) continue;
          if (FT->getParamType(0) != ptr_ty) continue;
          if (FT->getParamType(1) != i64_ty) continue;
          if (FT->getParamType(2) != ptr_ty) continue;
          dead_semantics.push_back(&F);
        }

        if (dead_semantics.empty())
          return llvm::PreservedAnalyses::all();

        bool changed = false;
        for (auto *dead_fn : dead_semantics) {
          for (auto *user : llvm::make_early_inc_range(dead_fn->users())) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(user);
            if (!call) continue;
            auto *BB = call->getParent();
            // Replace result with poison.
            if (!call->getType()->isVoidTy())
              call->replaceAllUsesWith(
                  llvm::PoisonValue::get(call->getType()));
            // Collect successors before modifying.
            llvm::SmallVector<llvm::BasicBlock *, 2> succs;
            if (BB->getTerminator())
              for (auto *S : llvm::successors(BB))
                succs.push_back(S);
            // Erase call and everything after it.
            while (&BB->back() != call)
              BB->back().eraseFromParent();
            call->eraseFromParent();
            for (auto *S : succs)
              S->removePredecessor(BB);
            llvm::IRBuilder<> Builder(BB);
            Builder.CreateUnreachable();
            changed = true;
          }
        }

        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(DeadSemanticCallEliminationPass{});

    // After eliminating dead semantic calls, run cleanup to remove
    // the now-dead State stores and allocas.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::SimplifyCFGPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }
    MPM.addPass(llvm::GlobalDCEPass());
  }

  // Eliminate __remill_unknown_register_ accesses (global undef).
  if (!envDisabled("OMILL_SKIP_UNKNOWN_REG_ELIM")) {
    struct EliminateUnknownRegisterPass
        : llvm::PassInfoMixin<EliminateUnknownRegisterPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        auto *GV = M.getGlobalVariable("__remill_unknown_register_");
        if (!GV) return llvm::PreservedAnalyses::all();
        bool changed = false;
        for (auto *user : llvm::make_early_inc_range(GV->users())) {
          if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(user)) {
            LI->replaceAllUsesWith(
                llvm::Constant::getNullValue(LI->getType()));
            LI->eraseFromParent();
            changed = true;
          } else if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(user)) {
            SI->eraseFromParent();
            changed = true;
          }
        }
        if (GV->use_empty()) {
          GV->eraseFromParent();
          changed = true;
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(EliminateUnknownRegisterPass{});
  }

  // Iterative dead function elimination:
  // 1. Replace calls to unreachable-body functions with unreachable.
  // 2. SimplifyCFG + ADCE to remove dead code in callers.
  // 3. Internalize newly-unreachable _native functions → GlobalDCE.
  // Iterate because eliminating one layer of dead calls can create new
  // unreachable-body functions (when the only non-dead path called a dead fn).
  if (!envDisabled("OMILL_SKIP_DEAD_NATIVE_INTERN")) {
    struct PropagateUnreachableCallsPass
        : llvm::PassInfoMixin<PropagateUnreachableCallsPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        // Collect functions with unreachable-only body.
        llvm::SmallPtrSet<llvm::Function *, 32> dead_fns;
        for (auto &F : M) {
          if (F.isDeclaration() || F.empty()) continue;
          if (F.size() != 1) continue;
          auto &entry = F.getEntryBlock();
          if (entry.size() == 1 &&
              llvm::isa<llvm::UnreachableInst>(entry.front()))
            dead_fns.insert(&F);
        }
        if (dead_fns.empty())
          return llvm::PreservedAnalyses::all();

        bool changed = false;
        for (auto &F : M) {
          if (F.isDeclaration()) continue;
          if (dead_fns.count(&F)) continue;
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call) continue;
              auto *callee = call->getCalledFunction();
              if (!callee || !dead_fns.count(callee)) continue;
              // Replace call result with poison.
              if (!call->getType()->isVoidTy())
                call->replaceAllUsesWith(
                    llvm::PoisonValue::get(call->getType()));
              // Collect successors, erase tail, add unreachable.
              llvm::SmallVector<llvm::BasicBlock *, 2> succs;
              if (BB.getTerminator())
                for (auto *S : llvm::successors(&BB))
                  succs.push_back(S);
              while (&BB.back() != call)
                BB.back().eraseFromParent();
              call->eraseFromParent();
              for (auto *S : succs)
                S->removePredecessor(&BB);
              llvm::IRBuilder<> Builder(&BB);
              Builder.CreateUnreachable();
              changed = true;
              break;
            }
          }
        }

        // Internalize dead _native functions.
        for (auto *F : dead_fns) {
          if (F->getName().ends_with("_native") &&
              !F->hasLocalLinkage() &&
              !F->hasFnAttribute("omill.vm_wrapper")) {
            F->setLinkage(llvm::GlobalValue::InternalLinkage);
            changed = true;
          }
        }

        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };

    // Single pass: propagate unreachable from functions that were ALREADY
    // dead before this pipeline.  Don't iterate — iteration would cascade
    // through noreturn call chains (vmexit → vmenter → handler → entry),
    // incorrectly killing live functions.
    MPM.addPass(PropagateUnreachableCallsPass{});
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::SimplifyCFGPass());
      FPM.addPass(llvm::ADCEPass());
      MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    }
    MPM.addPass(llvm::GlobalDCEPass());
  }

  // Dead argument/return elimination: remove unused return values from
  // _native functions with internal linkage.  Requires internalization first,
  // since DAE only works on internal functions.
  if (!envDisabled("OMILL_SKIP_DEAD_ARG_ELIM")) {
    // Internalize non-entry _native functions so DAE can optimize them.
    struct InternalizeForDAEPass
        : llvm::PassInfoMixin<InternalizeForDAEPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        bool changed = false;
        for (auto &F : M) {
          if (F.isDeclaration() || F.hasLocalLinkage()) continue;
          if (!F.getName().ends_with("_native")) continue;
          // Keep the entry point (function matching --va address) external.
          // Entry points are called from outside the module.
          // Heuristic: entry _native functions have no callers within the module.
          bool has_internal_caller = false;
          for (auto *user : F.users()) {
            if (llvm::isa<llvm::CallInst>(user) ||
                llvm::isa<llvm::InvokeInst>(user)) {
              has_internal_caller = true;
              break;
            }
          }
          if (!has_internal_caller) continue;
          // VM wrapper boundary functions must stay external — their call
          // boundary is semantically meaningful and must not be inlined by
          // the ModuleInliner in subsequent cleanup passes.
          if (F.hasFnAttribute("omill.vm_wrapper")) continue;
          F.setLinkage(llvm::GlobalValue::InternalLinkage);
          changed = true;
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(InternalizeForDAEPass{});
    MPM.addPass(llvm::DeadArgumentEliminationPass());
  }

  // Split large native_stack allocas and promote to SSA.
  // After ABI recovery, each _native function has a [69632 x i8] alloca
  // with hundreds of constant-offset GEP accesses (stack spills).
  // Splitting into per-region allocas enables SROA.
  if (!envDisabled("OMILL_SKIP_SPLIT_LARGE_ALLOCA")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(SplitLargeAllocaPass{});
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::ADCEPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Replace sentinel data constants (0xCCCCCCCCCCCCCCCC from stack fill)
  // with poison.  These are reads from uninitialized stack slots that survived
  // as concrete constants through ABI recovery.  Replacing with poison lets
  // ADCE/SimplifyCFG eliminate dead code paths that depend on them.
  //
  // Must run AFTER ABI recovery + post-ABI deobfuscation, since those stages
  // create _native wrappers with native_stack memset(0xCC) fills.
  if (!envDisabled("OMILL_SKIP_SENTINEL_DATA_ELIM")) {
    struct SentinelDataEliminationPass
        : llvm::PassInfoMixin<SentinelDataEliminationPass> {
      llvm::PreservedAnalyses run(llvm::Function &F,
                                   llvm::FunctionAnalysisManager &) {
        if (F.isDeclaration())
          return llvm::PreservedAnalyses::all();

        auto isSentinelConst = [](llvm::ConstantInt *CI) -> bool {
          if (!CI || CI->getBitWidth() < 16) return false;
          uint64_t v = CI->getZExtValue();
          // Full-width 0xCCCC... pattern.
          uint64_t mask = (CI->getBitWidth() == 64)
              ? 0xFFFFFFFFFFFFFFFFULL
              : (1ULL << CI->getBitWidth()) - 1;
          if ((v & mask) == (0xCCCCCCCCCCCCCCCCULL & mask))
            return true;
          // 32-bit sentinel zero-extended in a 64-bit value.
          if (CI->getBitWidth() == 64 && v == 0xCCCCCCCCULL)
            return true;
          return false;
        };

        auto isSentinelPtr = [&](llvm::Value *ptr) -> bool {
          // ConstantExpr inttoptr(sentinel).
          if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
            if (ce->getOpcode() == llvm::Instruction::IntToPtr)
              return isSentinelConst(
                  llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0)));
          }
          // IntToPtrInst with sentinel.
          if (auto *i2p = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
            return isSentinelConst(
                llvm::dyn_cast<llvm::ConstantInt>(i2p->getOperand(0)));
          return false;
        };

        bool changed = false;

        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            // Eliminate load/store/cmpxchg to sentinel pointer.
            if (auto *ld = llvm::dyn_cast<llvm::LoadInst>(&I)) {
              if (isSentinelPtr(ld->getPointerOperand())) {
                ld->replaceAllUsesWith(
                    llvm::PoisonValue::get(ld->getType()));
                ld->eraseFromParent();
                changed = true;
              }
              continue;
            }
            if (auto *st = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              if (isSentinelPtr(st->getPointerOperand())) {
                st->eraseFromParent();
                changed = true;
                continue;
              }
              // Store of sentinel value → dead store (uninitialized data).
              if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(
                      st->getValueOperand())) {
                if (isSentinelConst(CI)) {
                  st->eraseFromParent();
                  changed = true;
                }
              }
              continue;
            }
            if (auto *cx = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(&I)) {
              if (isSentinelPtr(cx->getPointerOperand())) {
                cx->replaceAllUsesWith(
                    llvm::PoisonValue::get(cx->getType()));
                cx->eraseFromParent();
                changed = true;
              }
              continue;
            }

            if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
              // Calls to sentinel address → unreachable.
              if (isSentinelPtr(call->getCalledOperand())) {
                if (!call->getType()->isVoidTy())
                  call->replaceAllUsesWith(
                      llvm::PoisonValue::get(call->getType()));
                llvm::SmallVector<llvm::BasicBlock *, 2> succs;
                if (BB.getTerminator())
                  for (auto *S : llvm::successors(&BB))
                    succs.push_back(S);
                while (&BB.back() != call)
                  BB.back().eraseFromParent();
                call->eraseFromParent();
                for (auto *S : succs)
                  S->removePredecessor(&BB);
                llvm::IRBuilder<> Builder(&BB);
                Builder.CreateUnreachable();
                changed = true;
                break;
              }
              // Replace sentinel constants in call arguments.
              for (unsigned i = 0; i < call->arg_size(); ++i) {
                auto *CI = llvm::dyn_cast<llvm::ConstantInt>(
                    call->getArgOperand(i));
                if (isSentinelConst(CI)) {
                  call->setArgOperand(i,
                      llvm::PoisonValue::get(CI->getType()));
                  changed = true;
                }
              }
              continue;
            }
            if (auto *ret = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
              if (auto *rv = ret->getReturnValue()) {
                if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rv)) {
                  if (isSentinelConst(CI)) {
                    ret->setOperand(0,
                        llvm::PoisonValue::get(CI->getType()));
                    changed = true;
                  }
                }
                // Handle ret { i64 sentinel } (ConstantStruct/Aggregate).
                if (auto *CA = llvm::dyn_cast<llvm::Constant>(rv)) {
                  if (!llvm::isa<llvm::ConstantInt>(CA)) {
                    bool has_sentinel = false;
                    for (unsigned i = 0; i < CA->getNumOperands(); ++i) {
                      if (isSentinelConst(
                              llvm::dyn_cast<llvm::ConstantInt>(
                                  CA->getOperand(i)))) {
                        has_sentinel = true;
                        break;
                      }
                    }
                    if (has_sentinel) {
                      ret->setOperand(0,
                          llvm::PoisonValue::get(rv->getType()));
                      changed = true;
                    }
                  }
                }
              }
              continue;
            }
            if (auto *IV = llvm::dyn_cast<llvm::InsertValueInst>(&I)) {
              if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(
                      IV->getInsertedValueOperand())) {
                if (isSentinelConst(CI)) {
                  IV->setOperand(1,
                      llvm::PoisonValue::get(CI->getType()));
                  changed = true;
                }
              }
              continue;
            }
          }
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    llvm::FunctionPassManager FPM;
    FPM.addPass(SentinelDataEliminationPass{});
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Convert sentinel memsets (0xCC/0xCD) to zero-fill.
  // RecoverFunctionSignatures fills the synthetic stack with 0xCC to prevent
  // undef→UB during optimization.  Now that optimization is complete, convert
  // to zero-fill for cleaner output.
  if (!envDisabled("OMILL_SKIP_SENTINEL_MEMORY_ELIM")) {
    struct LateSentinelMemsetPass
        : llvm::PassInfoMixin<LateSentinelMemsetPass> {
      /// Check if an APInt's raw bytes are all the same sentinel byte
      /// (0xCC or 0xCD).
      static bool isSentinelBits(const llvm::APInt &bits) {
        unsigned bytes = bits.getBitWidth() / 8;
        if (bytes == 0 || bits.getBitWidth() % 8 != 0)
          return false;
        uint8_t first = static_cast<uint8_t>(bits.extractBitsAsZExtValue(8, 0));
        if (first != 0xCC && first != 0xCD)
          return false;
        for (unsigned i = 1; i < bytes; ++i) {
          if (static_cast<uint8_t>(
                  bits.extractBitsAsZExtValue(8, i * 8)) != first)
            return false;
        }
        return true;
      }

      llvm::PreservedAnalyses run(llvm::Function &F,
                                   llvm::FunctionAnalysisManager &) {
        if (F.isDeclaration())
          return llvm::PreservedAnalyses::all();
        bool changed = false;
        for (auto &BB : F) {
          for (auto &I : BB) {
            // Handle memset(0xCC) / memset(0xCD).
            if (auto *ms = llvm::dyn_cast<llvm::MemSetInst>(&I)) {
              auto *fill =
                  llvm::dyn_cast<llvm::ConstantInt>(ms->getValue());
              if (!fill)
                continue;
              uint8_t v = static_cast<uint8_t>(fill->getZExtValue());
              if (v == 0xCC || v == 0xCD) {
                ms->setValue(llvm::ConstantInt::get(fill->getType(), 0));
                changed = true;
              }
              continue;
            }
            // Handle store of sentinel float/double/integer constants.
            // Example: store float 0xC199999980000000 (= 0xCCCCCCCC as float)
            auto *si = llvm::dyn_cast<llvm::StoreInst>(&I);
            if (!si)
              continue;
            llvm::Value *val = si->getValueOperand();
            if (auto *cfp = llvm::dyn_cast<llvm::ConstantFP>(val)) {
              llvm::APInt bits = cfp->getValueAPF().bitcastToAPInt();
              if (isSentinelBits(bits)) {
                auto *zero = llvm::ConstantFP::getZero(cfp->getType());
                si->setOperand(0, zero);
                changed = true;
              }
            } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
              if (ci->getBitWidth() >= 16 && isSentinelBits(ci->getValue())) {
                si->setOperand(0,
                    llvm::ConstantInt::get(ci->getType(), 0));
                changed = true;
              }
            }
          }
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    llvm::FunctionPassManager FPM;
    FPM.addPass(LateSentinelMemsetPass{});
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Eliminate zero stores to alloca regions already zeroed by memset(0).
  // DSE cannot handle this when the alloca escapes through inttoptr.
  {
    struct DeadZeroStorePass : llvm::PassInfoMixin<DeadZeroStorePass> {
      /// Check if a constant is all-zero bits.
      static bool isZeroBits(llvm::Constant *C) {
        return C->isNullValue();
      }
      /// Get the alloca and byte offset from a pointer (strips GEPs).
      static std::pair<llvm::AllocaInst *, int64_t>
      getAllocaAndOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
        int64_t offset = 0;
        while (auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
          llvm::APInt gep_off(64, 0);
          if (!gep->accumulateConstantOffset(DL, gep_off))
            return {nullptr, 0};
          offset += gep_off.getSExtValue();
          ptr = gep->getPointerOperand();
        }
        return {llvm::dyn_cast<llvm::AllocaInst>(ptr), offset};
      }

      llvm::PreservedAnalyses run(llvm::Function &F,
                                   llvm::FunctionAnalysisManager &) {
        if (F.isDeclaration() || F.empty())
          return llvm::PreservedAnalyses::all();
        auto &DL = F.getDataLayout();
        auto &entry = F.getEntryBlock();

        // Find memset(alloca, 0, size) in the entry block.
        struct ZeroedAlloca {
          llvm::AllocaInst *alloca;
          uint64_t size;
        };
        llvm::SmallVector<ZeroedAlloca, 2> zeroed;
        for (auto &I : entry) {
          auto *ms = llvm::dyn_cast<llvm::MemSetInst>(&I);
          if (!ms)
            continue;
          auto *fill = llvm::dyn_cast<llvm::ConstantInt>(ms->getValue());
          if (!fill || fill->getZExtValue() != 0)
            continue;
          auto *len = llvm::dyn_cast<llvm::ConstantInt>(ms->getLength());
          if (!len)
            continue;
          auto *alloca =
              llvm::dyn_cast<llvm::AllocaInst>(ms->getDest());
          if (!alloca)
            continue;
          zeroed.push_back({alloca, len->getZExtValue()});
        }
        if (zeroed.empty())
          return llvm::PreservedAnalyses::all();

        // Forward scan: eliminate zero stores to zeroed regions.
        // Track which byte ranges have been overwritten with non-zero values.
        // Use interval tracking: set of (offset, size) non-zero writes.
        llvm::DenseMap<llvm::AllocaInst *, uint64_t> alloca_sizes;
        for (auto &z : zeroed)
          alloca_sizes[z.alloca] = z.size;

        // Collect dead stores, then erase them.
        llvm::SmallVector<llvm::StoreInst *, 64> dead;

        for (auto &BB : F) {
          // Per-BB: track which offsets have been written with non-zero.
          // Simple approach: just check entry-block stores that precede any
          // call or load from the same alloca.
          for (auto &I : BB) {
            auto *si = llvm::dyn_cast<llvm::StoreInst>(&I);
            if (!si)
              continue;
            auto [alloca, off] = getAllocaAndOffset(si->getPointerOperand(), DL);
            if (!alloca)
              continue;
            auto it = alloca_sizes.find(alloca);
            if (it == alloca_sizes.end())
              continue;
            if (off < 0 || static_cast<uint64_t>(off) >= it->second)
              continue;
            auto *val = llvm::dyn_cast<llvm::Constant>(si->getValueOperand());
            if (!val || !isZeroBits(val))
              continue;
            dead.push_back(si);
          }
        }

        for (auto *si : dead)
          si->eraseFromParent();

        return dead.empty() ? llvm::PreservedAnalyses::all()
                            : llvm::PreservedAnalyses::none();
      }
      static bool isRequired() { return true; }
    };

    llvm::FunctionPassManager FPM;
    FPM.addPass(DeadZeroStorePass{});
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // MBA simplification on post-ABI code.  MBA chains may be introduced by
  // inlining VM handlers that were individually simplified but recombine.
#if OMILL_ENABLE_SIMPLIFIER
  if (!envDisabled("OMILL_SKIP_DEOBF_SIMPLIFY_MBA")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(SimplifyMBAPass());
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
#endif

  // Resolve inttoptr(ptrtoint(alloca) ± δ) → GEP in post-ABI output.
  // After ABI recovery, the vmcontext alloca has self-referencing pointer
  // patterns that the main-pipeline ConcretizeAllocaPtrsPass couldn't see
  // (they're created by RecoverStackFrame).  Re-run here.
  if (!envDisabled("OMILL_SKIP_CONCRETIZE_ALLOCA_PTRS")) {
    // Reuse the file-scope ConcretizeAllocaPtrsPass.  Find ptrtoint-of-alloca
    // seeds, BFS through add/sub chains, forward through store→load pairs,
    // replace inttoptr with GEP.
    llvm::FunctionPassManager FPM;
    FPM.addPass(ConcretizeAllocaPtrsPass{});
    FPM.addPass(llvm::DSEPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // VmContext slot forwarding: replace loads from the vmcontext alloca
  // with the SSA value that was last stored to the same byte range.
  // This is a lightweight store-to-load forwarding pass that handles the
  // case where SROA can't decompose the alloca (ptrtoint escape) and GVN
  // can't see through it (the alloca is opaque to alias analysis).
  // Must run after ConcretizeAllocaPtrsPass (which resolves all alloca-
  // derived inttoptr→GEP, giving us clean GEP-based accesses).
  if (!envDisabled("OMILL_SKIP_VMCONTEXT_SLOT_FWD")) {
    struct VmContextSlotForwardingPass
        : llvm::PassInfoMixin<VmContextSlotForwardingPass> {
      static std::pair<llvm::AllocaInst *, int64_t>
      getAllocaAndOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
        int64_t offset = 0;
        while (auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
          llvm::APInt gep_off(64, 0);
          if (!gep->accumulateConstantOffset(DL, gep_off))
            return {nullptr, 0};
          offset += gep_off.getSExtValue();
          ptr = gep->getPointerOperand();
        }
        return {llvm::dyn_cast<llvm::AllocaInst>(ptr), offset};
      }

      static llvm::AllocaInst *findVmContextAlloca(llvm::Function &F) {
        for (auto &I : F.getEntryBlock()) {
          auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
          if (!AI)
            continue;
          auto *arrTy =
              llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType());
          if (!arrTy)
            continue;
          uint64_t sz = arrTy->getNumElements() *
                        F.getDataLayout().getTypeAllocSize(
                            arrTy->getElementType());
          // After SplitLargeAllocaPass, the vmcontext may be split into
          // smaller regions.  Accept any array alloca with a ptrtoint user.
          if (sz < 16)
            continue;
          bool has_pti = false;
          for (auto *U : AI->users()) {
            if (llvm::isa<llvm::PtrToIntInst>(U)) {
              has_pti = true;
              break;
            }
            if (auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
              for (auto *GU : G->users()) {
                if (llvm::isa<llvm::PtrToIntInst>(GU)) {
                  has_pti = true;
                  break;
                }
              }
              if (has_pti)
                break;
            }
          }
          if (has_pti)
            return AI;
        }
        return nullptr;
      }

      llvm::PreservedAnalyses run(llvm::Function &F,
                                   llvm::FunctionAnalysisManager &) {
        if (F.isDeclaration() || F.empty())
          return llvm::PreservedAnalyses::all();

        auto *AI = findVmContextAlloca(F);
        if (!AI)
          return llvm::PreservedAnalyses::all();

        auto &DL = F.getDataLayout();
        auto *arrTy = llvm::cast<llvm::ArrayType>(AI->getAllocatedType());
        uint64_t alloca_sz = arrTy->getNumElements() *
                             DL.getTypeAllocSize(arrTy->getElementType());

        // Track last stored value per byte range.
        // Key: {offset, store_size} → {stored_value, store_inst}
        // We use a flat array indexed by byte offset; each entry tracks
        // the store that last wrote it.
        struct SlotInfo {
          llvm::Value *val = nullptr;
          llvm::StoreInst *store = nullptr;
          int64_t slot_offset = -1; // offset of the store that wrote this byte
          uint64_t slot_size = 0;   // size of the store that wrote this byte
        };
        std::vector<SlotInfo> slots(alloca_sz);

        bool changed = false;
        llvm::SmallVector<llvm::Instruction *, 32> dead;

        // Process each basic block independently.
        for (auto &BB : F) {
          // Reset slot tracking at BB boundaries for soundness.
          // (Only entry-block stores are guaranteed to dominate all uses.)
          // For non-entry blocks, we still do intra-block forwarding.
          std::fill(slots.begin(), slots.end(), SlotInfo{});

          // If this is the entry block, initialize slots from memset(0).
          if (&BB == &F.getEntryBlock()) {
            for (auto &I : BB) {
              auto *MS = llvm::dyn_cast<llvm::MemSetInst>(&I);
              if (!MS)
                continue;
              auto [base, off] = getAllocaAndOffset(MS->getDest(), DL);
              if (base != AI || off < 0)
                continue;
              auto *fill = llvm::dyn_cast<llvm::ConstantInt>(MS->getValue());
              auto *len = llvm::dyn_cast<llvm::ConstantInt>(MS->getLength());
              if (!fill || !len)
                continue;
              if (fill->getZExtValue() != 0)
                continue;
              // Mark these bytes as storing zero. We don't track a specific
              // store inst for memset — individual byte loads will need to
              // construct the zero constant.
              uint64_t uoff = static_cast<uint64_t>(off);
              uint64_t end = uoff + len->getZExtValue();
              for (uint64_t b = uoff; b < end && b < alloca_sz; ++b) {
                // Mark with null store but set val to indicate "known zero"
                // We'll handle this specially when forwarding loads.
              }
              break; // Only one memset expected.
            }
          }

          for (auto &I : BB) {
            if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              auto [base, off] =
                  getAllocaAndOffset(SI->getPointerOperand(), DL);
              if (base != AI || off < 0)
                continue;
              uint64_t sz =
                  DL.getTypeStoreSize(SI->getValueOperand()->getType());
              uint64_t uoff = static_cast<uint64_t>(off);
              if (uoff + sz > alloca_sz)
                continue;
              // Record this store for every byte it covers.
              for (uint64_t b = uoff; b < uoff + sz; ++b) {
                slots[b] = {SI->getValueOperand(), SI, off, sz};
              }
              continue;
            }

            if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
              auto [base, off] =
                  getAllocaAndOffset(LI->getPointerOperand(), DL);
              if (base != AI || off < 0)
                continue;
              uint64_t sz = DL.getTypeStoreSize(LI->getType());
              uint64_t uoff = static_cast<uint64_t>(off);
              if (uoff + sz > alloca_sz)
                continue;

              // Check if all bytes of this load are covered by a single
              // store at the exact same offset and size.
              auto &first = slots[uoff];
              if (!first.val || !first.store)
                continue;
              if (first.slot_offset != off ||
                  first.slot_size != sz)
                continue;
              // Verify all bytes point to the same store.
              bool uniform = true;
              for (uint64_t b = uoff + 1; b < uoff + sz; ++b) {
                if (slots[b].store != first.store) {
                  uniform = false;
                  break;
                }
              }
              if (!uniform)
                continue;

              // Forward the stored value to the load.
              llvm::Value *fwd = first.val;
              if (fwd->getType() != LI->getType()) {
                // Type mismatch but same size — insert bitcast.
                if (DL.getTypeStoreSize(fwd->getType()) !=
                    DL.getTypeStoreSize(LI->getType()))
                  continue;
                llvm::IRBuilder<> builder(LI);
                fwd = builder.CreateBitCast(fwd, LI->getType());
              }
              LI->replaceAllUsesWith(fwd);
              dead.push_back(LI);
              changed = true;
              continue;
            }

            // memset to the alloca: clear slot tracking for those bytes.
            if (auto *MS = llvm::dyn_cast<llvm::MemSetInst>(&I)) {
              auto [base, off] = getAllocaAndOffset(MS->getDest(), DL);
              if (base != AI || off < 0)
                continue;
              auto *len = llvm::dyn_cast<llvm::ConstantInt>(MS->getLength());
              if (!len)
                continue;
              uint64_t uoff = static_cast<uint64_t>(off);
              uint64_t end = uoff + len->getZExtValue();
              for (uint64_t b = uoff; b < end && b < alloca_sz; ++b)
                slots[b] = {};
              continue;
            }

            // Calls that might write to the alloca: clear all tracking.
            if (auto *CI = llvm::dyn_cast<llvm::CallBase>(&I)) {
              if (CI->getIntrinsicID() == llvm::Intrinsic::memset ||
                  CI->getIntrinsicID() == llvm::Intrinsic::memcpy ||
                  CI->getIntrinsicID() == llvm::Intrinsic::memmove)
                continue;
              for (auto &arg : CI->args()) {
                if (!arg->getType()->isPointerTy())
                  continue;
                auto [base, off] = getAllocaAndOffset(arg.get(), DL);
                if (base == AI) {
                  std::fill(slots.begin(), slots.end(), SlotInfo{});
                  break;
                }
              }
            }
          }
        }

        for (auto *I : dead)
          I->eraseFromParent();

        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };

    llvm::FunctionPassManager FPM;
    FPM.addPass(VmContextSlotForwardingPass{});
    // Re-run ConcretizeAllocaPtrsPass: slot forwarding exposes new
    // ptrtoint-derived inttoptr chains (loaded ptrtoint values that
    // were previously hidden behind store-load round-trips).
    FPM.addPass(ConcretizeAllocaPtrsPass{});
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // VmContext dead store elimination.
  // After ConcretizeAllocaPtrsPass resolves alloca-derived inttoptr→GEP,
  // any remaining inttoptr users access external memory (driver structs,
  // kernel data, VM dispatch tables) and do NOT alias the alloca.
  // Standard DSE is blocked by the ptrtoint escape; this pass performs
  // byte-level liveness tracking on single-BB functions to find stores
  // that are overwritten before read or never read at all.
  if (!envDisabled("OMILL_SKIP_VMCONTEXT_DSE")) {
    struct VmContextDSEPass : llvm::PassInfoMixin<VmContextDSEPass> {
      /// Get the alloca and byte offset from a pointer (strips GEPs).
      static std::pair<llvm::AllocaInst *, int64_t>
      getAllocaAndOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
        int64_t offset = 0;
        while (auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
          llvm::APInt gep_off(64, 0);
          if (!gep->accumulateConstantOffset(DL, gep_off))
            return {nullptr, 0};
          offset += gep_off.getSExtValue();
          ptr = gep->getPointerOperand();
        }
        return {llvm::dyn_cast<llvm::AllocaInst>(ptr), offset};
      }

      /// Find large alloca with ptrtoint user — the vmcontext candidate.
      static llvm::AllocaInst *findVmContextAlloca(llvm::Function &F) {
        for (auto &I : F.getEntryBlock()) {
          auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
          if (!AI)
            continue;
          auto *arrTy = llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType());
          if (!arrTy)
            continue;
          uint64_t sz = arrTy->getNumElements() *
                        F.getDataLayout().getTypeAllocSize(
                            arrTy->getElementType());
          // After SplitLargeAllocaPass, the vmcontext may be split into
          // smaller regions.  Accept any array alloca with a ptrtoint user.
          if (sz < 16)
            continue;
          // Must have at least one ptrtoint user (the escape).
          bool has_pti = false;
          for (auto *U : AI->users()) {
            if (llvm::isa<llvm::PtrToIntInst>(U)) {
              has_pti = true;
              break;
            }
            // ptrtoint may be on a GEP of the alloca.
            if (auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
              for (auto *GU : G->users()) {
                if (llvm::isa<llvm::PtrToIntInst>(GU)) {
                  has_pti = true;
                  break;
                }
              }
              if (has_pti)
                break;
            }
          }
          if (has_pti)
            return AI;
        }
        return nullptr;
      }

      llvm::PreservedAnalyses run(llvm::Function &F,
                                   llvm::FunctionAnalysisManager &) {
        if (F.isDeclaration() || F.empty())
          return llvm::PreservedAnalyses::all();
        auto *AI = findVmContextAlloca(F);
        if (!AI)
          return llvm::PreservedAnalyses::all();

        auto &DL = F.getDataLayout();
        auto *arrTy = llvm::cast<llvm::ArrayType>(AI->getAllocatedType());
        uint64_t alloca_sz = arrTy->getNumElements() *
                             DL.getTypeAllocSize(arrTy->getElementType());

        // Byte-level tracking: pending[byte] = last StoreInst that wrote it.
        // A store is "live" if any byte it covers is loaded before being
        // overwritten by another store.
        std::vector<llvm::StoreInst *> pending(alloca_sz, nullptr);
        llvm::DenseSet<llvm::StoreInst *> live_stores;

        auto &entry = F.getEntryBlock();
        for (auto &I : entry) {
          if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
            auto [base, off] = getAllocaAndOffset(LI->getPointerOperand(), DL);
            if (base != AI || off < 0)
              continue;
            uint64_t sz = DL.getTypeStoreSize(LI->getType());
            uint64_t uoff = static_cast<uint64_t>(off);
            for (uint64_t b = uoff; b < uoff + sz && b < alloca_sz; ++b) {
              if (pending[b])
                live_stores.insert(pending[b]);
            }
            continue;
          }

          if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            auto [base, off] =
                getAllocaAndOffset(SI->getPointerOperand(), DL);
            if (base != AI || off < 0)
              continue;
            uint64_t sz = DL.getTypeStoreSize(SI->getValueOperand()->getType());
            uint64_t uoff = static_cast<uint64_t>(off);
            for (uint64_t b = uoff; b < uoff + sz && b < alloca_sz; ++b)
              pending[b] = SI;
            continue;
          }

          // memset to the alloca: treat as a store to every byte.
          if (auto *MS = llvm::dyn_cast<llvm::MemSetInst>(&I)) {
            auto [base, off] = getAllocaAndOffset(MS->getDest(), DL);
            if (base != AI || off < 0)
              continue;
            auto *len = llvm::dyn_cast<llvm::ConstantInt>(MS->getLength());
            if (!len)
              continue;
            uint64_t uoff = static_cast<uint64_t>(off);
            uint64_t end = uoff + len->getZExtValue();
            for (uint64_t b = uoff; b < end && b < alloca_sz; ++b)
              pending[b] = nullptr; // memset is not a StoreInst; clear pending
            continue;
          }

          // Calls that take a pointer to the alloca: conservatively mark
          // all pending bytes as live (the callee may read them).
          if (auto *CI = llvm::dyn_cast<llvm::CallBase>(&I)) {
            // Skip llvm.memset/memcpy intrinsics — already handled above
            // or known not to read the alloca.
            if (CI->getIntrinsicID() == llvm::Intrinsic::memset ||
                CI->getIntrinsicID() == llvm::Intrinsic::memcpy ||
                CI->getIntrinsicID() == llvm::Intrinsic::memmove)
              continue;
            // Check if any arg points into the alloca.
            bool touches_alloca = false;
            for (auto &arg : CI->args()) {
              if (!arg->getType()->isPointerTy())
                continue;
              auto [base, off] = getAllocaAndOffset(arg.get(), DL);
              if (base == AI) {
                touches_alloca = true;
                break;
              }
            }
            if (touches_alloca) {
              for (uint64_t b = 0; b < alloca_sz; ++b) {
                if (pending[b])
                  live_stores.insert(pending[b]);
              }
            }
          }
        }

        // For multi-BB functions: stores still in pending[] at end of entry
        // are visible to successor blocks.  Scan all non-entry BBs for loads
        // from the alloca; if any loads an offset whose pending store is set,
        // mark that store as live.
        if (F.size() > 1) {
          // Collect byte offsets that have a non-null pending store.
          llvm::DenseSet<uint64_t> pending_offsets;
          for (uint64_t b = 0; b < alloca_sz; ++b) {
            if (pending[b])
              pending_offsets.insert(b);
          }
          if (!pending_offsets.empty()) {
            for (auto &BB : F) {
              if (&BB == &entry)
                continue;
              for (auto &I : BB) {
                if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
                  auto [base, off] =
                      getAllocaAndOffset(LI->getPointerOperand(), DL);
                  if (base != AI || off < 0)
                    continue;
                  uint64_t sz = DL.getTypeStoreSize(LI->getType());
                  uint64_t uoff = static_cast<uint64_t>(off);
                  for (uint64_t b = uoff; b < uoff + sz && b < alloca_sz; ++b) {
                    if (pending[b])
                      live_stores.insert(pending[b]);
                  }
                }
                // Calls in non-entry BBs that take the alloca pointer:
                // conservatively mark all pending stores as live.
                if (auto *CI = llvm::dyn_cast<llvm::CallBase>(&I)) {
                  if (CI->getIntrinsicID() == llvm::Intrinsic::memset ||
                      CI->getIntrinsicID() == llvm::Intrinsic::memcpy ||
                      CI->getIntrinsicID() == llvm::Intrinsic::memmove)
                    continue;
                  for (auto &arg : CI->args()) {
                    if (!arg->getType()->isPointerTy())
                      continue;
                    auto [base, off] = getAllocaAndOffset(arg.get(), DL);
                    if (base == AI) {
                      for (uint64_t b = 0; b < alloca_sz; ++b) {
                        if (pending[b])
                          live_stores.insert(pending[b]);
                      }
                      break;
                    }
                  }
                }
              }
            }
          }
        }

        // Collect dead stores: any StoreInst to the alloca that isn't live.
        llvm::SmallVector<llvm::StoreInst *, 32> dead;
        for (auto &I : entry) {
          auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
          if (!SI)
            continue;
          auto [base, off] = getAllocaAndOffset(SI->getPointerOperand(), DL);
          if (base != AI || off < 0)
            continue;
          if (!live_stores.contains(SI))
            dead.push_back(SI);
        }

        for (auto *SI : dead)
          SI->eraseFromParent();

        return dead.empty() ? llvm::PreservedAnalyses::all()
                            : llvm::PreservedAnalyses::none();
      }
      static bool isRequired() { return true; }
    };

    llvm::FunctionPassManager FPM;
    FPM.addPass(VmContextDSEPass{});
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // Cleanup after sentinel elimination + concretization + vmcontext DSE.
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::AggressiveInstCombinePass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::DSEPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  // Strip inline diagnostic markers emitted by emitInlineDiagMarker().
  // These volatile stores to @__omill_inline_diag_sink.* are only needed
  // during pipeline development; remove them from the final output.
  if (!envDisabled("OMILL_SKIP_STRIP_INLINE_DIAG")) {
    struct StripInlineDiagMarkersPass
        : llvm::PassInfoMixin<StripInlineDiagMarkersPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        bool changed = false;
        llvm::SmallVector<llvm::GlobalVariable *, 16> to_erase;

        for (auto &GV : M.globals()) {
          if (!GV.getName().starts_with("__omill_inline_diag"))
            continue;
          to_erase.push_back(&GV);
        }

        if (to_erase.empty())
          return llvm::PreservedAnalyses::all();

        // Remove from @llvm.used / @llvm.compiler.used first.
        llvm::removeFromUsedLists(M, [&](llvm::Constant *C) {
          if (auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(C))
            return GV->getName().starts_with("__omill_inline_diag");
          return false;
        });

        // Erase all users (store volatile → sink), then the globals.
        for (auto *GV : to_erase) {
          llvm::SmallVector<llvm::User *, 8> users(GV->users());
          for (auto *U : users) {
            if (auto *I = llvm::dyn_cast<llvm::Instruction>(U))
              I->eraseFromParent();
          }
          GV->eraseFromParent();
          changed = true;
        }

        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(StripInlineDiagMarkersPass{});
  }

  // After late target patching and post-ABI cleanup, unreferenced _native
  // helpers that are not user-requested output roots are implementation-detail
  // debris. Keep them alive only while unresolved dispatch shims remain;
  // otherwise internalize them so the final GlobalDCE can drop the wrapper
  // plus any remill helper baggage it alone references.
  if (!envDisabled("OMILL_SKIP_INTERNALIZE_DEAD_NATIVE_HELPERS")) {
    struct InternalizeDeadNativeHelpersPass
        : llvm::PassInfoMixin<InternalizeDeadNativeHelpersPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        auto has_live_dispatch = [&](llvm::StringRef name) {
          auto *F = M.getFunction(name);
          return F && !F->use_empty();
        };
        if (has_live_dispatch("__omill_dispatch_call") ||
            has_live_dispatch("__omill_dispatch_jump")) {
          return llvm::PreservedAnalyses::all();
        }

        bool changed = false;
        for (auto &F : M) {
          if (F.isDeclaration() || !F.getName().ends_with("_native"))
            continue;
          if (F.hasFnAttribute("omill.output_root"))
            continue;
          if (!F.use_empty())
            continue;
          if (!F.hasExternalLinkage())
            continue;
          F.setLinkage(llvm::GlobalValue::InternalLinkage);
          changed = true;
        }

        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(InternalizeDeadNativeHelpersPass{});
  }

  MPM.addPass(llvm::GlobalDCEPass());
}

void buildPostPatchCleanupPipeline(llvm::ModulePassManager &MPM,
                                   unsigned inline_threshold) {
  llvm::InlineParams params = llvm::getInlineParams(inline_threshold);
  MPM.addPass(llvm::ModuleInlinerWrapperPass(params));
  buildCleanupPipeline(MPM, CleanupProfile::kBoundary);
  MPM.addPass(llvm::GlobalDCEPass());
}

void buildLiftInfrastructureCleanupPipeline(llvm::ModulePassManager &MPM) {
  MPM.addPass(InternalizeRemillSemanticsPass());
  MPM.addPass(llvm::GlobalDCEPass());
}

void registerModuleAnalyses(llvm::ModuleAnalysisManager &MAM) {
  MAM.registerPass([&] { return TargetArchAnalysis(); });
  MAM.registerPass([&] { return TraceLiftAnalysis(); });
  MAM.registerPass([&] { return CallGraphAnalysis(); });
  MAM.registerPass([&] { return CallingConventionAnalysis(); });
  MAM.registerPass([&] { return BinaryMemoryAnalysis(); });
  MAM.registerPass([&] { return LiftedFunctionAnalysis(); });
  MAM.registerPass([&] { return IterativeLiftingSessionAnalysis(); });
  MAM.registerPass([&] { return ExceptionInfoAnalysis(); });
  MAM.registerPass([&] { return BlockLiftAnalysis(); });
  MAM.registerPass([&] { return VMTraceMapAnalysis(); });
  MAM.registerPass([&] { return VirtualCalleeRegistryAnalysis(); });
}

void registerAAWithManager(llvm::AAManager &AAM) {
  AAM.registerFunctionAnalysis<SegmentsAA>();
}

}  // namespace omill

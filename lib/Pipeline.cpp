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
#include <llvm/Transforms/Scalar/TailRecursionElimination.h>
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
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

#include "omill/Utils/StateFieldMap.h"

#include <chrono>
#include <cstdlib>
#include <optional>
#include <set>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Analysis/RemillIntrinsicAnalysis.h"
#include "omill/Analysis/SegmentsAA.h"
#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Passes/CFGRecovery.h"
#include "omill/Passes/ControlFlowUnflattener.h"
#include "omill/Passes/OptimizeState.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Passes/ResolveForcedExceptions.h"
#include "omill/Passes/MemoryPointerElimination.h"
#include "omill/Passes/RecoverStackFrame.h"
#include "omill/Passes/RecoverStackFrameTypes.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Analysis/VirtualModel/Analysis.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Devirtualization/OutputRootClosure.h"
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
#include "omill/Passes/InterProceduralDeadStateStore.h"
#include "omill/Passes/IterativeTargetResolution.h"
#include "omill/Passes/EliminateDeadPaths.h"
#include "omill/Passes/CombinedFixedPointDevirt.h"
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
#include "omill/Passes/VirtualCFGMaterialization.h"
#include "omill/Passes/VMHandlerInliner.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Passes/VMDispatchResolution.h"
#include "omill/Passes/VMDeadMergedHandlerElimination.h"
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
#include "omill/Remill/Normalization.h"
#include "omill/Passes/RecoverAllocaPointers.h"
#include "omill/Analysis/TargetArchAnalysis.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/ProtectedBoundaryUtils.h"

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
          if (isDispatchJumpName(name))
            ++dispatch_jumps;
          else if (isDispatchCallName(name))
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

struct ClosedSliceShapeProbePass
    : llvm::PassInfoMixin<ClosedSliceShapeProbePass> {
  std::string label_;

  explicit ClosedSliceShapeProbePass(llvm::StringRef label) : label_(label) {}

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    unsigned closed_root_slice_fns = 0;
    unsigned declare_blk = 0;
    unsigned define_blk = 0;
    unsigned call_blk = 0;
    unsigned musttail_blk = 0;
    unsigned define_native = 0;
    unsigned call_native = 0;
    unsigned dispatch_calls = 0;
    unsigned vm_entry_calls = 0;
    unsigned missing_block_calls = 0;
    unsigned missing_block_handler_calls = 0;

    for (auto &F : M) {
      if (F.hasFnAttribute("omill.closed_root_slice"))
        ++closed_root_slice_fns;

      auto name = F.getName();
      if (name.starts_with("blk_")) {
        if (F.isDeclaration())
          ++declare_blk;
        else
          ++define_blk;
      }
      if (name.ends_with("_native") && !F.isDeclaration())
        ++define_native;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;
          auto *callee = CB->getCalledFunction();
          if (!callee)
            continue;
          auto callee_name = callee->getName();
          if (callee_name.starts_with("blk_")) {
            ++call_blk;
            if (auto *CI = llvm::dyn_cast<llvm::CallInst>(CB);
                CI && CI->isMustTailCall()) {
              ++musttail_blk;
            }
          } else if (callee_name.ends_with("_native")) {
            ++call_native;
          } else if (isDispatchIntrinsicName(callee_name)) {
            ++dispatch_calls;
          } else if (callee_name.starts_with("vm_entry_")) {
            ++vm_entry_calls;
          } else if (callee_name == "__remill_missing_block") {
            ++missing_block_calls;
          } else if (callee_name == "__omill_missing_block_handler") {
            ++missing_block_handler_calls;
          }
        }
      }
    }

    llvm::errs() << "[closed-slice-shape] " << label_
                 << " closed_fns=" << closed_root_slice_fns
                 << " declare_blk=" << declare_blk
                 << " define_blk=" << define_blk
                 << " call_blk=" << call_blk
                 << " musttail_blk=" << musttail_blk
                 << " define_native=" << define_native
                 << " call_native=" << call_native
                 << " dispatch=" << dispatch_calls
                 << " vm_entry_calls=" << vm_entry_calls
                 << " missing_block=" << missing_block_calls
                 << " missing_block_handler=" << missing_block_handler_calls
                 << "\n";
    return llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

void addClosedSliceShapeProbe(llvm::ModulePassManager &MPM,
                              llvm::StringRef label) {
  static bool enabled =
      (std::getenv("OMILL_DEBUG_CLOSED_SLICE_SHAPE") != nullptr);
  if (enabled)
    MPM.addPass(ClosedSliceShapeProbePass(label));
}

struct DebugPrintSelectedFunctionsPass
    : llvm::PassInfoMixin<DebugPrintSelectedFunctionsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    const char *raw = std::getenv("OMILL_DEBUG_PRINT_FUNCTIONS");
    if (!raw || raw[0] == '\0')
      return llvm::PreservedAnalyses::all();
    llvm::StringRef raw_names(raw);
    if (raw_names == "*" || raw_names.equals_insensitive("all")) {
      llvm::errs() << "[omill.debug.fn] module\n";
      M.print(llvm::errs(), nullptr);
      return llvm::PreservedAnalyses::all();
    }

    llvm::SmallVector<llvm::StringRef, 8> names;
    raw_names.split(names, ',', -1, false);
    for (auto name : names) {
      name = name.trim();
      if (name.empty())
        continue;
      if (name == "*" || name.equals_insensitive("all")) {
        llvm::errs() << "[omill.debug.fn] module\n";
        M.print(llvm::errs(), nullptr);
        continue;
      }
      if (auto *F = M.getFunction(name)) {
        llvm::errs() << "[omill.debug.fn] " << name << "\n";
        F->print(llvm::errs());
      } else {
        llvm::errs() << "[omill.debug.fn] missing " << name << "\n";
      }
    }

    return llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

struct DebugPrintSelectedFunctionsWithLabelPass
    : llvm::PassInfoMixin<DebugPrintSelectedFunctionsWithLabelPass> {
  std::string label;

  explicit DebugPrintSelectedFunctionsWithLabelPass(std::string label_)
      : label(std::move(label_)) {}

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    const char *raw = std::getenv("OMILL_DEBUG_LIFT_CLEANUP_FUNCTIONS");
    if (!raw || raw[0] == '\0')
      return llvm::PreservedAnalyses::all();

    llvm::errs() << "[omill.debug.cleanup] stage=" << label << "\n";
    llvm::StringRef raw_names(raw);
    llvm::SmallVector<llvm::StringRef, 8> names;
    raw_names.split(names, ',', -1, false);
    for (auto name : names) {
      name = name.trim();
      if (name.empty())
        continue;
      if (auto *F = M.getFunction(name)) {
        llvm::errs() << "[omill.debug.cleanup] fn=" << name
                     << " decl=" << F->isDeclaration()
                     << " linkage=" << static_cast<int>(F->getLinkage())
                     << " uses=" << F->getNumUses() << "\n";
      } else {
        llvm::errs() << "[omill.debug.cleanup] fn=" << name << " missing\n";
      }
    }

    return llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

bool envDisabled(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0') return false;
  return (v[0] == '1' && v[1] == '\0') ||
         (v[0] == 't' && v[1] == '\0') ||
         (v[0] == 'T' && v[1] == '\0');
}

bool envEnabled(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0') return false;
  return (v[0] == '1' && v[1] == '\0') ||
         (v[0] == 't' && v[1] == '\0') ||
         (v[0] == 'T' && v[1] == '\0') ||
         (v[0] == 'y' && v[1] == '\0') ||
         (v[0] == 'Y' && v[1] == '\0');
}

bool alwaysInlinerEnabled() {
  return !envDisabled("OMILL_SKIP_ALWAYS_INLINE");
}

bool abiAlwaysInlinerEnabled() {
  return alwaysInlinerEnabled() &&
         !envDisabled("OMILL_SKIP_ABI_ALWAYS_INLINE");
}

bool moduleInlinerEnabled() {
  return alwaysInlinerEnabled() &&
         !envDisabled("OMILL_SKIP_MODULE_INLINE");
}

bool enableClosedSliceContinuationDiscovery() {
  return envEnabled("OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY") &&
         !envDisabled("OMILL_SKIP_CLOSED_SLICE_CONTINUATION_DISCOVERY");
}

bool enableNoAbiClosedSliceContinuationRelift() {
  return envEnabled("OMILL_ENABLE_NOABI_CLOSED_SLICE_RELIFT");
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

static bool isGenericStaticDevirtSignalFunction(const llvm::Function &F) {
  auto name = F.getName();
  if (name.starts_with("vm_entry_"))
    return true;

  return F.hasFnAttribute("omill.vm_handler") ||
         F.hasFnAttribute("omill.vm_wrapper") ||
         F.hasFnAttribute("omill.protection_boundary") ||
         F.hasFnAttribute("omill.vm_newly_lifted") ||
         F.hasFnAttribute("omill.newly_lifted") ||
         F.hasFnAttribute("omill.virtual_specialized") ||
         F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
         F.getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
         F.getFnAttribute("omill.boundary_kind").isValid();
}

static bool moduleHasGenericStaticDevirtualizationCandidatesImpl(
    const llvm::Module &M) {
  for (const auto &F : M) {
    if (isGenericStaticDevirtSignalFunction(F))
      return true;
  }

  return false;
}

static bool moduleHasRootLocalGenericStaticDevirtualizationShapeImpl(
    const llvm::Module &M) {
  auto isRootLocalGenericStaticDevirtSignalFunction =
      [](const llvm::Function &F) {
        auto name = F.getName();
        if (name.starts_with("vm_entry_"))
          return true;

        return F.hasFnAttribute("omill.vm_handler") ||
               F.hasFnAttribute("omill.vm_wrapper") ||
               F.hasFnAttribute("omill.vm_newly_lifted") ||
               F.hasFnAttribute("omill.newly_lifted") ||
               F.hasFnAttribute("omill.virtual_specialized") ||
               F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
               F.getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
               F.getFnAttribute("omill.export_entry_seed_exprs").isValid();
      };

  llvm::SmallVector<const llvm::Function *, 16> worklist;
  llvm::SmallPtrSet<const llvm::Function *, 32> seen;
  bool saw_dispatch_like = false;
  bool saw_block_helper_edge = false;

  for (const auto &F : M) {
    if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root") &&
        seen.insert(&F).second) {
      worklist.push_back(&F);
    }
  }

  constexpr size_t kMaxReachable = 256;
  while (!worklist.empty() && seen.size() <= kMaxReachable) {
    const llvm::Function *F = worklist.pop_back_val();
    if (!F->hasFnAttribute("omill.output_root") &&
        isRootLocalGenericStaticDevirtSignalFunction(*F)) {
      return true;
    }

    for (const auto &BB : *F) {
      for (const auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;

        auto callee_name = callee->getName();
        if (isDispatchJumpName(callee_name) || isDispatchCallName(callee_name)) {
          saw_dispatch_like = true;
        } else if (callee_name.starts_with("blk_") ||
                   callee_name.starts_with("block_")) {
          saw_block_helper_edge = true;
        }

        if (!callee->isDeclaration() && seen.insert(callee).second)
          worklist.push_back(callee);
      }
    }
  }

  return saw_dispatch_like && saw_block_helper_edge;
}

static constexpr llvm::StringLiteral kLoopifiedTerminalPcMetadata =
    "omill.loopified_terminal_pc";
static constexpr llvm::StringLiteral kLoopifiedTerminalPcAttr =
    "omill.loopified_terminal_pc";
static constexpr llvm::StringLiteral kTerminalBoundaryCandidatePcAttr =
    "omill.terminal_boundary_candidate_pc";

std::optional<uint64_t> getTerminalBoundaryCandidatePc(
    const llvm::Function &F) {
  auto attr = F.getFnAttribute(kTerminalBoundaryCandidatePcAttr);
  if (!attr.isValid())
    return std::nullopt;
  uint64_t parsed_pc = 0;
  if (attr.getValueAsString().getAsInteger(16, parsed_pc))
    return std::nullopt;
  return parsed_pc;
}

llvm::Function *getOrCreateMissingBlockHandler(llvm::Module &M,
                                               llvm::Function *&handler) {
  if (handler)
    return handler;
  auto &ctx = M.getContext();
  auto *handler_ty = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx),
                                             {llvm::Type::getInt64Ty(ctx)},
                                             false);
  handler = llvm::cast<llvm::Function>(
      M.getOrInsertFunction("__omill_missing_block_handler", handler_ty)
          .getCallee());
  return handler;
}

void collectReachableClosedRootSliceFunctions(
    llvm::Module &M, llvm::SmallVectorImpl<llvm::Function *> &functions);
void collectReachableOutputRootFunctions(
    llvm::Module &M, llvm::SmallVectorImpl<llvm::Function *> &functions);
bool isLargeNoAbiStateOptimizationScopeModule(const llvm::Module &M);

bool getBoolMetadataValue(const llvm::Instruction &I, llvm::StringRef name) {
  auto *md = I.getMetadata(name);
  auto *tuple = llvm::dyn_cast_or_null<llvm::MDTuple>(md);
  if (!tuple || tuple->getNumOperands() == 0)
    return false;
  auto *value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(
      tuple->getOperand(0));
  return value && value->getZExtValue() != 0;
}

std::optional<uint64_t> getU64MetadataValue(const llvm::Instruction &I,
                                            llvm::StringRef name) {
  auto *md = I.getMetadata(name);
  auto *tuple = llvm::dyn_cast_or_null<llvm::MDTuple>(md);
  if (!tuple || tuple->getNumOperands() == 0)
    return std::nullopt;
  auto *value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(
      tuple->getOperand(0));
  if (!value)
    return std::nullopt;
  return value->getZExtValue();
}

bool isExecutableLikeTerminalBoundaryKind(llvm::StringRef kind) {
  return kind.contains("executable");
}

struct X86DecodeWindowScore {
  uint64_t end_pc = 0;
  unsigned instruction_count = 0;
};

bool looksLikePlausibleX86FunctionEntry(const BinaryMemoryMap &binary_memory,
                                        uint64_t pc);
bool isExactX86DirectControlFlowFallthrough(const BinaryMemoryMap &memory,
                                            uint64_t target_pc);

std::optional<X86DecodeWindowScore> scoreForwardDecodableX86Window(
    const BinaryMemoryMap &binary_memory, uint64_t start_pc,
    uint64_t limit_pc) {
  uint64_t current_pc = start_pc;
  unsigned instruction_count = 0;
  while (instruction_count < 8 && current_pc < limit_pc) {
    auto next_pc = nextDecodableX86InstructionPC(binary_memory, current_pc);
    if (!next_pc.has_value() || *next_pc <= current_pc)
      break;
    current_pc = *next_pc;
    ++instruction_count;
    if (current_pc >= limit_pc)
      break;
  }
  if (!instruction_count)
    return std::nullopt;
  return X86DecodeWindowScore{current_pc, instruction_count};
}

std::optional<uint64_t> recoverWrappedDirectCallTargetFromInvalidatedEntry(
    const BinaryMemoryMap &binary_memory, uint64_t source_pc, uint64_t failed_pc) {
  if (failed_pc <= source_pc || (failed_pc - source_pc) > 16)
    return std::nullopt;

  const uint64_t start_pc = source_pc > 16 ? (source_pc - 16) : 1;
  for (uint64_t call_pc = source_pc; call_pc > start_pc; --call_pc) {
    const uint64_t candidate_pc = call_pc - 1;
    uint8_t bytes[8] = {};
    if (!binary_memory.read(candidate_pc, bytes, sizeof(bytes)) || bytes[0] != 0xE8)
      continue;

    int32_t rel = 0;
    std::memcpy(&rel, bytes + 1, sizeof(rel));
    const uint64_t fallthrough_pc = candidate_pc + 5;
    const uint64_t target_pc = static_cast<uint64_t>(
        static_cast<int64_t>(fallthrough_pc) + static_cast<int64_t>(rel));
    if (!binary_memory.isExecutable(target_pc, 1) || fallthrough_pc >= source_pc)
      continue;

    uint8_t branch_bytes[6] = {};
    if (!binary_memory.read(fallthrough_pc, branch_bytes, sizeof(branch_bytes)))
      continue;

    std::optional<uint64_t> branch_target;
    if (branch_bytes[0] >= 0x70 && branch_bytes[0] <= 0x7F) {
      int8_t rel8 = static_cast<int8_t>(branch_bytes[1]);
      branch_target = static_cast<uint64_t>(
          static_cast<int64_t>(fallthrough_pc + 2) + static_cast<int64_t>(rel8));
    } else if (branch_bytes[0] == 0x0F &&
               (branch_bytes[1] & 0xF0u) == 0x80u) {
      int32_t rel32 = 0;
      std::memcpy(&rel32, branch_bytes + 2, sizeof(rel32));
      branch_target = static_cast<uint64_t>(
          static_cast<int64_t>(fallthrough_pc + 6) + static_cast<int64_t>(rel32));
    }
    if (!branch_target.has_value() || *branch_target <= failed_pc)
      continue;

    return target_pc;
  }

  return std::nullopt;
}

std::optional<uint64_t> recoverForwardInvalidatedX86InstructionStart(
    const BinaryMemoryMap &binary_memory, uint64_t source_pc,
    uint64_t failed_pc) {
  if (failed_pc <= source_pc || (failed_pc - source_pc) > 16)
    return std::nullopt;

  auto source_end = nextDecodableX86InstructionPC(binary_memory, source_pc);
  if (!source_end.has_value() || *source_end <= source_pc)
    return std::nullopt;

  const uint64_t search_limit =
      std::min<uint64_t>(failed_pc + 16, source_pc + 16);
  std::optional<uint64_t> best_pc;
  uint64_t best_end_pc = 0;
  unsigned best_instruction_count = 0;

  for (uint64_t candidate = source_pc + 1; candidate <= search_limit;
       ++candidate) {
    if (!binary_memory.isExecutable(candidate, 1))
      continue;
    const bool strong_boundary =
        isExactX86DirectControlFlowFallthrough(binary_memory, candidate) ||
        looksLikePlausibleX86FunctionEntry(binary_memory, candidate);
    if (!strong_boundary)
      continue;
    auto score =
        scoreForwardDecodableX86Window(binary_memory, candidate, search_limit);
    if (!score.has_value() || score->end_pc <= failed_pc)
      continue;
    if (score->instruction_count < 2 && score->end_pc < (failed_pc + 4))
      continue;
    if (!best_pc.has_value() || score->end_pc > best_end_pc ||
        (score->end_pc == best_end_pc &&
         score->instruction_count > best_instruction_count) ||
        (score->end_pc == best_end_pc &&
         score->instruction_count == best_instruction_count &&
         candidate < *best_pc)) {
      best_pc = candidate;
      best_end_pc = score->end_pc;
      best_instruction_count = score->instruction_count;
    }
  }

  return best_pc;
}

struct TerminalBoundaryReplacementTarget {
  llvm::Function *function = nullptr;
  uint64_t call_pc = 0;
};

TerminalBoundaryReplacementTarget findCompatibleTerminalBoundaryOwner(
    llvm::Module &M, llvm::Function &caller, uint64_t target_pc,
    std::optional<uint64_t> nearby_pc) {
  auto build_target = [&](llvm::Function *candidate)
      -> std::optional<TerminalBoundaryReplacementTarget> {
    if (!candidate || candidate == &caller ||
        candidate->getFunctionType() != caller.getFunctionType()) {
      return std::nullopt;
    }
    auto call_pc = extractStructuralCodeTargetPC(*candidate);
    if (!call_pc)
      return std::nullopt;
    return TerminalBoundaryReplacementTarget{candidate, call_pc};
  };

  if (auto target = build_target(findLiftedOrBlockFunctionByPC(M, target_pc));
      target.has_value()) {
    return *target;
  }
  if (auto target = build_target(findLiftedOrCoveredFunctionByPC(M, target_pc));
      target.has_value()) {
    return *target;
  }
  if (nearby_pc) {
    if (auto target =
            build_target(findLiftedOrBlockFunctionByPC(M, *nearby_pc));
        target.has_value()) {
      return *target;
    }
    if (auto target =
            build_target(findLiftedOrCoveredFunctionByPC(M, *nearby_pc));
        target.has_value()) {
      return *target;
    }
  }
  return {};
}

TerminalBoundaryReplacementTarget getOrCreateExecutableTerminalReplacement(
    llvm::Module &M, llvm::Function &caller, uint64_t target_pc,
    std::optional<uint64_t> nearby_pc, bool canonicalize_to_nearby_entry,
    const llvm::CallBase &call) {
  if (auto owner =
          findCompatibleTerminalBoundaryOwner(M, caller, target_pc, nearby_pc);
      owner.function) {
    return owner;
  }

  uint64_t placeholder_pc = target_pc;
  if (canonicalize_to_nearby_entry && nearby_pc.has_value()) {
    placeholder_pc = *nearby_pc;
  }

  const std::string name =
      "omill_executable_target_" + llvm::utohexstr(placeholder_pc);
  auto *replacement = M.getFunction(name);
  if (!replacement) {
    replacement = llvm::Function::Create(caller.getFunctionType(),
                                         llvm::GlobalValue::ExternalLinkage,
                                         name, M);
  }
  if (auto executable_fact = readExecutableTargetFact(call)) {
    executable_fact->raw_target_pc = placeholder_pc;
    writeExecutableTargetFact(*replacement, *executable_fact);
  } else {
    ExecutableTargetFact placeholder_fact;
    placeholder_fact.raw_target_pc = placeholder_pc;
    writeExecutableTargetFact(*replacement, placeholder_fact);
  }
  return {replacement, placeholder_pc};
}

bool rewriteMissingBlockHandlerCallToExecutableTarget(llvm::Module &M,
                                                      llvm::Function &F,
                                                      llvm::CallInst &call,
                                                      uint64_t target_pc,
                                                      std::optional<uint64_t> nearby_pc,
                                                      bool canonicalize_to_nearby_entry) {
  if (F.arg_size() < 2)
    return false;

  auto replacement = getOrCreateExecutableTerminalReplacement(
      M, F, target_pc, nearby_pc, canonicalize_to_nearby_entry, call);
  if (!replacement.function ||
      replacement.function->getFunctionType() != F.getFunctionType())
    return false;

  auto *bb = call.getParent();
  llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(bb));
  llvm::IRBuilder<> ir(&call);
  llvm::SmallVector<llvm::Value *, 8> args;
  args.reserve(F.arg_size());
  for (auto &arg : F.args())
    args.push_back(&arg);
  args[1] = llvm::ConstantInt::get(
      replacement.function->getFunctionType()->getParamType(1),
      replacement.call_pc);
  auto *replacement_call = ir.CreateCall(
      replacement.function->getFunctionType(), replacement.function, args);
  if (F.getReturnType()->isVoidTy()) {
    ir.CreateRetVoid();
  } else {
    ir.CreateRet(replacement_call);
  }

  for (auto *succ : old_succs)
    succ->removePredecessor(bb);

  llvm::SmallVector<llvm::Instruction *, 8> to_erase;
  for (llvm::Instruction *it = &call; it != nullptr; it = it->getNextNode())
    to_erase.push_back(it);
  for (auto *inst : to_erase) {
    if (!inst->use_empty())
      inst->replaceAllUsesWith(llvm::PoisonValue::get(inst->getType()));
    inst->eraseFromParent();
  }
  return true;
}

bool rewriteTerminalBoundaryOutputRoot(llvm::Module &M, llvm::Function &F,
                                       uint64_t target_pc,
                                       llvm::Function *&handler) {
  F.addFnAttr(kTerminalBoundaryCandidatePcAttr, llvm::utohexstr(target_pc));
  for (auto &BB : llvm::make_early_inc_range(F))
    BB.dropAllReferences();
  while (!F.empty())
    F.begin()->eraseFromParent();

  auto *entry = llvm::BasicBlock::Create(M.getContext(), "entry", &F);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(getOrCreateMissingBlockHandler(M, handler),
               {llvm::ConstantInt::get(llvm::Type::getInt64Ty(M.getContext()),
                                       target_pc)});
  if (F.getReturnType()->isVoidTy()) {
    B.CreateRetVoid();
  } else {
    B.CreateRet(llvm::Constant::getNullValue(F.getReturnType()));
  }
  return true;
}

TargetArch targetArchForModule(llvm::Module &M) {
  TargetArch arch = TargetArch::kX86_64;
  if (auto *md = M.getModuleFlag("omill.target_arch")) {
    if (auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(md))
      arch = static_cast<TargetArch>(ci->getZExtValue());
  }
  return arch;
}

bool isTargetMapped(const BinaryMemoryMap &binary_memory, uint64_t target_pc) {
  if (target_pc == 0)
    return false;
  uint8_t byte = 0;
  return binary_memory.read(target_pc, &byte, 1);
}

bool isTargetExecutable(const BinaryMemoryMap &binary_memory,
                        uint64_t target_pc) {
  if (target_pc == 0)
    return false;
  return binary_memory.isExecutable(target_pc, 1);
}

std::optional<bool> isTargetDecodableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch arch) {
  if (!isTargetExecutable(binary_memory, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      if (target_pc & 0x3)
        return false;
      uint8_t buf[4] = {};
      return binary_memory.read(target_pc, buf, sizeof(buf));
    }
    case TargetArch::kX86_64:
    default:
      return canDecodeX86InstructionAt(binary_memory, target_pc);
  }
}

uint64_t overlapDesyncWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 4;
    case TargetArch::kX86_64:
    default:
      return 8;
  }
}

bool looksLikePlausibleX86FunctionEntry(const BinaryMemoryMap &binary_memory,
                                        uint64_t pc) {
  uint8_t buf[6] = {};
  if (!binary_memory.read(pc, buf, sizeof(buf)))
    return false;
  if (buf[0] == 0x55 || buf[0] == 0x53 || buf[0] == 0x56 || buf[0] == 0x57)
    return true;
  if (buf[0] == 0x41 && buf[1] >= 0x50 && buf[1] <= 0x57)
    return true;
  if (buf[0] == 0x48 && buf[1] == 0x83 && buf[2] == 0xEC)
    return true;
  if (buf[0] == 0x48 && buf[1] == 0x81 && buf[2] == 0xEC)
    return true;
  if (buf[0] == 0x48 && buf[1] == 0x89 && buf[3] == 0x24 &&
      (buf[2] == 0x5C || buf[2] == 0x74 || buf[2] == 0x7C))
    return true;
  if (buf[0] == 0x4C && buf[1] == 0x89 && buf[3] == 0x24 &&
      (buf[2] == 0x44 || buf[2] == 0x4C || buf[2] == 0x54 ||
       buf[2] == 0x5C || buf[2] == 0x64 || buf[2] == 0x6C ||
       buf[2] == 0x74 || buf[2] == 0x7C))
    return true;
  return false;
}

std::optional<uint64_t> findNearbyExecutableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch arch) {
  if (!isTargetExecutable(binary_memory, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      auto aligned = target_pc & ~uint64_t(0x3);
      if (aligned == target_pc)
        return std::nullopt;
      auto decodable = isTargetDecodableEntry(binary_memory, aligned, arch);
      if (decodable.has_value() && *decodable)
        return aligned;
      return std::nullopt;
    }
    case TargetArch::kX86_64:
    default: {
      constexpr uint64_t kWindow = 64;
      uint64_t start = (target_pc > kWindow) ? (target_pc - kWindow) : 1;
      std::optional<uint64_t> overlapping_owner_pc;
      std::optional<uint64_t> plausible_overlapping_owner_pc;
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isTargetExecutable(binary_memory, pc))
          continue;
        if (pc < target_pc &&
            (target_pc - pc) <= overlapDesyncWindow(TargetArch::kX86_64) &&
            looksLikePlausibleX86FunctionEntry(binary_memory, pc)) {
          plausible_overlapping_owner_pc = pc;
        }
        auto next_pc = nextDecodableX86InstructionPC(binary_memory, pc);
        if (next_pc.has_value() && pc < target_pc && *next_pc > target_pc) {
          overlapping_owner_pc = pc;
          if (looksLikePlausibleX86FunctionEntry(binary_memory, pc))
            plausible_overlapping_owner_pc = pc;
        }
      }
      if (plausible_overlapping_owner_pc.has_value())
        return plausible_overlapping_owner_pc;
      if (overlapping_owner_pc.has_value())
        return overlapping_owner_pc;
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isTargetExecutable(binary_memory, pc))
          continue;
        auto decodable = isTargetDecodableEntry(binary_memory, pc, arch);
        if (decodable.has_value() && *decodable)
          return pc;
      }
      return std::nullopt;
    }
  }
}

bool isInImageRange(const BinaryMemoryMap &binary_memory, uint64_t target_pc) {
  const auto image_base = binary_memory.imageBase();
  const auto image_size = binary_memory.imageSize();
  if (!image_base || !image_size)
    return false;
  return target_pc >= image_base && target_pc < (image_base + image_size);
}

bool isExactX86DirectControlFlowFallthrough(const BinaryMemoryMap &memory,
                                            uint64_t target_pc) {
  constexpr uint64_t kLookback = 16;
  const uint64_t start = target_pc > kLookback ? target_pc - kLookback : 1;
  for (uint64_t pc = start; pc < target_pc; ++pc) {
    uint8_t bytes[2] = {};
    if (!memory.read(pc, bytes, sizeof(bytes)))
      continue;

    uint64_t fallthrough = 0;
    if (bytes[0] == 0xE8 || bytes[0] == 0xE9) {
      fallthrough = pc + 5;
    } else if (bytes[0] == 0xEB || (bytes[0] >= 0x70 && bytes[0] <= 0x7F) ||
               bytes[0] == 0xE3) {
      fallthrough = pc + 2;
    } else if (bytes[0] == 0x0F && bytes[1] >= 0x80 && bytes[1] <= 0x8F) {
      fallthrough = pc + 6;
    } else {
      continue;
    }

    if (fallthrough == target_pc)
      return true;
  }
  return false;
}

struct TerminalBoundaryClassification {
  uint64_t target_pc = 0;
  std::string kind;
  bool in_image = false;
  bool mapped = false;
  bool executable = false;
  std::optional<bool> decodable_entry;
  std::optional<uint64_t> nearby_entry_pc;
  bool canonicalize_placeholder_to_nearby_entry = false;
};

TerminalBoundaryClassification classifyTerminalBoundaryTarget(
    llvm::Module &M, const BinaryMemoryMap &binary_memory, uint64_t target_pc) {
  TerminalBoundaryClassification info;
  info.target_pc = target_pc;
  info.in_image = isInImageRange(binary_memory, target_pc);
  info.mapped = isTargetMapped(binary_memory, target_pc);
  info.executable = isTargetExecutable(binary_memory, target_pc);

  if (classifyProtectedBoundary(binary_memory, target_pc)) {
    info.kind = "protected_boundary_target";
    return info;
  }

  if (!info.mapped) {
    info.kind = info.in_image ? "in_image_unmapped_target"
                              : "out_of_image_unmapped_target";
    return info;
  }

  if (!info.executable) {
    info.kind = info.in_image ? "in_image_non_executable_target"
                              : "mapped_non_executable_target";
    return info;
  }

  auto arch = targetArchForModule(M);
  if (arch == TargetArch::kX86_64 &&
      isExactX86DirectControlFlowFallthrough(binary_memory, target_pc)) {
    info.decodable_entry = isTargetDecodableEntry(binary_memory, target_pc, arch);
    info.kind = info.in_image ? "in_image_executable_fallthrough_target"
                              : "mapped_executable_fallthrough_target";
    return info;
  }

  info.decodable_entry = isTargetDecodableEntry(binary_memory, target_pc, arch);
  if (info.decodable_entry.has_value() && *info.decodable_entry) {
    info.kind = info.in_image ? "in_image_executable_decodable_target"
                              : "mapped_executable_decodable_target";
    return info;
  }

  if (auto overlapping_owner =
          findNearbyExecutableEntry(binary_memory, target_pc, arch);
      overlapping_owner.has_value() && *overlapping_owner < target_pc) {
    auto next_pc =
        nextDecodableX86InstructionPC(binary_memory, *overlapping_owner);
    if (next_pc.has_value() && *next_pc > target_pc) {
      info.nearby_entry_pc = overlapping_owner;
      info.canonicalize_placeholder_to_nearby_entry = true;
      info.kind = info.in_image ? "in_image_executable_nearby_entry_target"
                                : "mapped_executable_nearby_entry_target";
      return info;
    }
  }

  const uint64_t nearby_window = [&]() -> uint64_t {
    switch (arch) {
      case TargetArch::kAArch64:
        return 4;
      case TargetArch::kX86_64:
      default:
        return 128;
    }
  }();
  if (auto nearby_covered_pc =
          findNearestCoveredLiftedOrBlockPC(M, target_pc, nearby_window);
      nearby_covered_pc.has_value() && *nearby_covered_pc != target_pc) {
    info.nearby_entry_pc = nearby_covered_pc;
    info.kind = info.in_image ? "in_image_executable_nearby_lifted_target"
                              : "mapped_executable_nearby_lifted_target";
    return info;
  }

  info.nearby_entry_pc = findNearbyExecutableEntry(binary_memory, target_pc,
                                                   arch);
  if (info.nearby_entry_pc.has_value()) {
    info.kind = info.in_image ? "in_image_executable_nearby_entry_target"
                              : "mapped_executable_nearby_entry_target";
    return info;
  }

  info.kind = info.in_image ? "in_image_executable_undecodable_target"
                            : "mapped_executable_undecodable_target";
  return info;
}

struct RewriteExecutableBoundaryHandlerCallsPass
    : llvm::PassInfoMixin<RewriteExecutableBoundaryHandlerCallsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);
    bool changed = false;
    llvm::DenseSet<llvm::Function *> reachable;
    if (isClosedRootSliceScopedModule(M)) {
      llvm::SmallVector<llvm::Function *, 16> reachable_list;
      collectReachableClosedRootSliceFunctions(M, reachable_list);
      reachable.insert(reachable_list.begin(), reachable_list.end());
    } else {
      llvm::SmallVector<llvm::Function *, 16> reachable_list;
      collectReachableOutputRootFunctions(M, reachable_list);
      reachable.insert(reachable_list.begin(), reachable_list.end());
    }

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (!reachable.contains(&F)) {
        continue;
      }

      llvm::SmallVector<llvm::CallInst *, 8> handler_calls;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          if (callee->getName() != "__omill_missing_block_handler" &&
              callee->getName() != "__omill_error_handler")
            continue;
          handler_calls.push_back(call);
        }
      }

      for (auto *call : handler_calls) {
        if (!call->getParent() || call->arg_size() != 1)
          continue;
        auto *target_ci =
            llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(0));
        if (!target_ci)
          continue;

        const uint64_t target_pc = target_ci->getZExtValue();
        auto executable_fact = readExecutableTargetFact(*call);
        const bool invalidated_entry =
            executable_fact &&
            executable_fact->invalidated_executable_entry;
        std::optional<uint64_t> invalidated_forward_entry_pc;
        std::optional<uint64_t> invalidated_wrapped_call_target_pc;
        if (invalidated_entry && targetArchForModule(M) == TargetArch::kX86_64) {
          auto source_pc = executable_fact->invalidated_entry_source_pc;
          auto failed_pc = executable_fact->invalidated_entry_failed_pc;
          if (source_pc.has_value() && failed_pc.has_value()) {
            invalidated_forward_entry_pc =
                recoverForwardInvalidatedX86InstructionStart(
                    binary_memory, *source_pc, *failed_pc);
            invalidated_wrapped_call_target_pc =
                recoverWrappedDirectCallTargetFromInvalidatedEntry(
                    binary_memory, *source_pc, *failed_pc);
          }
        }
        auto classification =
            classifyTerminalBoundaryTarget(M, binary_memory, target_pc);
        auto arch = targetArchForModule(M);
        if (invalidated_wrapped_call_target_pc.has_value()) {
          classification.nearby_entry_pc = invalidated_wrapped_call_target_pc;
          classification.canonicalize_placeholder_to_nearby_entry = true;
        } else if (invalidated_forward_entry_pc.has_value()) {
          classification.nearby_entry_pc = invalidated_forward_entry_pc;
          classification.canonicalize_placeholder_to_nearby_entry = true;
        } else if (invalidated_entry &&
                   !classification.nearby_entry_pc.has_value()) {
          classification.nearby_entry_pc =
              findNearbyExecutableEntry(binary_memory, target_pc, arch);
        }
        if (!invalidated_forward_entry_pc.has_value() &&
            classification.nearby_entry_pc.has_value() &&
            arch == TargetArch::kX86_64) {
          const uint64_t start =
              (*classification.nearby_entry_pc > overlapDesyncWindow(arch))
                  ? (*classification.nearby_entry_pc - overlapDesyncWindow(arch))
                  : 1;
          for (uint64_t candidate = *classification.nearby_entry_pc + 1;
               candidate > start; --candidate) {
            const uint64_t pc = candidate - 1;
            if (pc >= target_pc)
              continue;
            if ((target_pc - pc) > overlapDesyncWindow(arch))
              continue;
            if (looksLikePlausibleX86FunctionEntry(binary_memory, pc)) {
              classification.nearby_entry_pc = pc;
              classification.canonicalize_placeholder_to_nearby_entry = true;
            }
          }
        }
        if (!invalidated_entry &&
            !isExecutableLikeTerminalBoundaryKind(classification.kind)) {
          continue;
        }

        if (rewriteMissingBlockHandlerCallToExecutableTarget(
                M, F, *call, target_pc, classification.nearby_entry_pc,
                classification.canonicalize_placeholder_to_nearby_entry)) {
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};


void annotateLoopifiedTerminalBranch(llvm::BranchInst &br, uint64_t target_pc) {
  auto &ctx = br.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  br.setMetadata(kLoopifiedTerminalPcMetadata,
                 llvm::MDTuple::get(
                     ctx, {llvm::ConstantAsMetadata::get(
                              llvm::ConstantInt::get(i64_ty, target_pc))}));
}

std::optional<uint64_t> getLoopifiedTerminalBranchPc(const llvm::BranchInst &br) {
  auto *md = br.getMetadata(kLoopifiedTerminalPcMetadata);
  if (!md || md->getNumOperands() != 1)
    return std::nullopt;
  if (auto *ci =
          llvm::mdconst::dyn_extract<llvm::ConstantInt>(md->getOperand(0))) {
    return ci->getZExtValue();
  }
  return std::nullopt;
}

std::optional<uint64_t> getConstantIndirectCallTargetPc(
    const llvm::CallBase &call) {
  if (call.getCalledFunction())
    return std::nullopt;

  auto *called = call.getCalledOperand()->stripPointerCasts();
  auto *expr = llvm::dyn_cast<llvm::ConstantExpr>(called);
  if (!expr || expr->getOpcode() != llvm::Instruction::IntToPtr)
    return std::nullopt;

  auto *target = llvm::dyn_cast<llvm::ConstantInt>(expr->getOperand(0));
  if (!target)
    return std::nullopt;

  return target->getZExtValue();
}

llvm::Function *findLiftedOrBlockSymbolByPC(llvm::Module &M, uint64_t pc) {
  for (llvm::StringRef prefix : {"sub_", "blk_", "block_"}) {
    std::string name = (prefix + llvm::Twine::utohexstr(pc)).str();
    if (auto *fn = M.getFunction(name))
      return fn;
  }
  return nullptr;
}

struct PatchDefinedControlTargetsPass
    : llvm::PassInfoMixin<PatchDefinedControlTargetsPass> {
  static void copyCallSiteMetadata(llvm::CallBase &from, llvm::CallBase &to) {
    to.setCallingConv(from.getCallingConv());
    to.setAttributes(from.getAttributes());
    to.setDebugLoc(from.getDebugLoc());
  }

  static llvm::CallInst *rewriteToDirectCall(llvm::CallBase &call,
                                             llvm::Function &target_fn,
                                             llvm::ArrayRef<llvm::Value *> args) {
    llvm::IRBuilder<> builder(&call);
    auto *new_call = builder.CreateCall(target_fn.getFunctionType(), &target_fn,
                                        args, call.getName());
    copyCallSiteMetadata(call, *new_call);
    if (auto *old_call = llvm::dyn_cast<llvm::CallInst>(&call))
      new_call->setTailCallKind(old_call->getTailCallKind());
    if (!call.use_empty()) {
      if (call.getType() == new_call->getType()) {
        call.replaceAllUsesWith(new_call);
      } else if (!call.getType()->isVoidTy()) {
        call.replaceAllUsesWith(llvm::PoisonValue::get(call.getType()));
      }
    }
    call.eraseFromParent();
    return new_call;
  }

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    bool changed = false;
    const bool debug_patch =
        (std::getenv("OMILL_DEBUG_DEFINED_TARGET_PATCH") != nullptr);
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;

          if (auto *callee = call->getCalledFunction()) {
            if ((callee->getName() == "__remill_function_call" ||
                 callee->getName() == "__remill_jump") &&
                call->arg_size() >= 3) {
              auto *pc_ci =
                  llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
              if (!pc_ci)
                continue;
              auto *target_fn =
                  omill::findLiftedOrBlockFunctionByPC(M, pc_ci->getZExtValue());
              if (!target_fn) {
                target_fn = findLiftedOrBlockSymbolByPC(M, pc_ci->getZExtValue());
              }
              if (debug_patch) {
                llvm::errs() << "[defined-target-patch] remill-call pc=0x"
                             << llvm::utohexstr(pc_ci->getZExtValue())
                             << " target="
                             << (target_fn ? target_fn->getName() : "<missing>")
                             << " type_match="
                             << (target_fn &&
                                 target_fn->getFunctionType() ==
                                     call->getFunctionType())
                             << "\n";
              }
              if (!target_fn ||
                  target_fn->getFunctionType() != call->getFunctionType()) {
                continue;
              }
              rewriteToDirectCall(*call, *target_fn,
                                  {call->getArgOperand(0), call->getArgOperand(1),
                                   call->getArgOperand(2)});
              changed = true;
              continue;
            }

            if (call->arg_size() >= 3 &&
                omill::isDispatchIntrinsicName(callee->getName())) {
              auto *pc_ci =
                  llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
              if (!pc_ci)
                continue;
              auto *target_fn =
                  omill::findLiftedOrBlockFunctionByPC(M, pc_ci->getZExtValue());
              if (!target_fn) {
                target_fn = findLiftedOrBlockSymbolByPC(M, pc_ci->getZExtValue());
              }
              if (!target_fn)
                continue;
              rewriteToDirectCall(*call, *target_fn,
                                  {call->getArgOperand(0), call->getArgOperand(1),
                                   call->getArgOperand(2)});
              changed = true;
              continue;
            }

            uint64_t target_pc = 0;
            if (auto fact = readExecutableTargetFact(*callee))
              target_pc = fact->raw_target_pc;
            if (target_pc == 0)
              target_pc = omill::extractEntryVA(callee->getName());
            if (target_pc == 0)
              continue;
            auto *target_fn = omill::findLiftedOrBlockFunctionByPC(M, target_pc);
            if (!target_fn)
              target_fn = findLiftedOrBlockSymbolByPC(M, target_pc);
            if (!target_fn || target_fn == callee || target_fn->isDeclaration() ||
                target_fn->getFunctionType() != call->getFunctionType()) {
              continue;
            }
            call->setCalledFunction(target_fn);
            changed = true;
            continue;
          }

          auto *callee_fn =
              llvm::dyn_cast<llvm::Function>(call->getCalledOperand()->stripPointerCasts());
          if (callee_fn && callee_fn->getName().contains("CALLI") &&
              call->arg_size() >= 3) {
            auto *pc_ci =
                llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2));
            if (!pc_ci)
              continue;
            auto *target_fn =
                omill::findLiftedOrBlockFunctionByPC(M, pc_ci->getZExtValue());
            if (!target_fn) {
              target_fn = findLiftedOrBlockSymbolByPC(M, pc_ci->getZExtValue());
            }
            if (!target_fn)
              continue;
            rewriteToDirectCall(*call, *target_fn,
                                {call->getArgOperand(1), call->getArgOperand(2),
                                 call->getArgOperand(0)});
            changed = true;
            continue;
          }

          llvm::ConstantInt *target_ci = nullptr;
          if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(call->getCalledOperand());
              ce && ce->getOpcode() == llvm::Instruction::IntToPtr) {
            target_ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
          }
          if (!target_ci) {
            if (auto *itp =
                    llvm::dyn_cast<llvm::IntToPtrInst>(call->getCalledOperand()))
              target_ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
          }
          if (!target_ci)
            continue;
          auto *target_fn =
              omill::findLiftedOrBlockFunctionByPC(M, target_ci->getZExtValue());
          if (!target_fn) {
            target_fn = findLiftedOrBlockSymbolByPC(M, target_ci->getZExtValue());
          }
          if (!target_fn || target_fn->getFunctionType() != call->getFunctionType())
            continue;
          call->setCalledFunction(target_fn);
          changed = true;
        }
      }
    }
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

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

/// When a __remill_missing_block call targets a constant address inside
/// a non-executable PE section (e.g. .rdata import name table), the
/// block cannot be lifted — the target is a VM-internal token, not
/// code.  Rewrite those terminal calls to `ret ptr %memory` so the
/// enclosing function has a proper return path instead of collapsing
/// to `body: unreachable` via PropagateUnreachableCallsPass later.
struct RewriteNonExecutableMissingBlockToRetPass
    : llvm::PassInfoMixin<RewriteNonExecutableMissingBlockToRetPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                               llvm::ModuleAnalysisManager &MAM) {
    auto *binary_memory = MAM.getCachedResult<BinaryMemoryAnalysis>(M);
    if (!binary_memory || !binary_memory->imageBase())
      return llvm::PreservedAnalyses::all();

    auto *missing_fn = M.getFunction("__remill_missing_block");
    if (!missing_fn || missing_fn->use_empty())
      return llvm::PreservedAnalyses::all();

    llvm::SmallVector<llvm::CallInst *, 8> to_rewrite;
    for (auto *user : missing_fn->users()) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(user);
      if (!call || call->arg_size() < 2)
        continue;
      auto *pc_const =
          llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
      if (!pc_const)
        continue;
      uint64_t target_pc = pc_const->getZExtValue();
      if (target_pc == 0)
        continue;
      if (isInImageRange(*binary_memory, target_pc) &&
          !isTargetExecutable(*binary_memory, target_pc)) {
        to_rewrite.push_back(call);
      }
    }

    if (to_rewrite.empty())
      return llvm::PreservedAnalyses::all();

    unsigned rewritten = 0;
    for (auto *call : to_rewrite) {
      auto *BB = call->getParent();
      auto *F = BB->getParent();
      llvm::Value *memory = nullptr;
      if (F->arg_size() >= 3)
        memory = F->getArg(2);
      if (!memory || !memory->getType()->isPointerTy())
        continue;

      call->replaceAllUsesWith(memory);
      llvm::SmallVector<llvm::BasicBlock *, 2> succs;
      if (BB->getTerminator())
        for (auto *S : llvm::successors(BB))
          succs.push_back(S);
      while (&BB->back() != call)
        BB->back().eraseFromParent();
      call->eraseFromParent();
      for (auto *S : succs)
        S->removePredecessor(BB);
      llvm::IRBuilder<> Builder(BB);
      Builder.CreateRet(memory);
      ++rewritten;
    }

    if (rewritten > 0 &&
        std::getenv("OMILL_DEBUG_NONEXEC_REWRITE") != nullptr)
      llvm::errs() << "[nonexec-missing-block] rewrote " << rewritten
                   << " non-executable missing_block calls to ret\n";
    return rewritten > 0 ? llvm::PreservedAnalyses::none()
                         : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

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
      if (isDispatchIntrinsicName(name) ||
          name == "__remill_function_return") {
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
    // passes create new unresolved-dispatch declarations.
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

bool hasLiftedRemillSignature(const llvm::Function &F) {
  auto *FT = F.getFunctionType();
  if (!FT)
    return false;
  if (FT->getNumParams() != 3)
    return false;
  if (!FT->getReturnType()->isPointerTy())
    return false;
  if (!FT->getParamType(0)->isPointerTy())
    return false;
  if (!FT->getParamType(1)->isIntegerTy(64))
    return false;
  if (!FT->getParamType(2)->isPointerTy())
    return false;
  return true;
}

bool isLiftedPipelineFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;

  auto name = F.getName();
  if (name.starts_with("sub_") || name.starts_with("block_") ||
      name.starts_with("blk_") || name.starts_with("__lifted_")) {
    return true;
  }

  if (F.hasFnAttribute("omill.vm_newly_lifted") ||
      F.hasFnAttribute("omill.newly_lifted") ||
      F.hasFnAttribute("omill.vm_handler") ||
      F.hasFnAttribute("omill.vm_wrapper") ||
      F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
      F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()) {
    return true;
  }

  // Checkpointed lifted IR may retain the Remill function signature while
  // using non-standard names. Semantic helpers are protected with optnone
  // before the early lowering/state phases and should stay out of scope.
  return hasLiftedRemillSignature(F) &&
         !F.hasFnAttribute(llvm::Attribute::OptimizeNone);
}

bool shouldRunClosedRootSliceScopedPass(llvm::Function &F) {
  if (!isClosedRootSliceScopedModule(*F.getParent()))
    return true;
  return isClosedRootSliceFunction(F);
}

bool shouldRunClosedRootSliceScopedPassOnlyWhenScoped(llvm::Function &F) {
  return isClosedRootSliceScopedModule(*F.getParent()) &&
         isClosedRootSliceFunction(F);
}

bool isClosedRootSliceCodeBearingFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.hasFnAttribute("omill.localized_continuation_shim"))
    return false;

  auto name = F.getName();
  if (name.starts_with("sub_") || name.starts_with("block_") ||
      name.starts_with("blk_") || name.starts_with("__lifted_")) {
    return true;
  }

  return F.hasFnAttribute("omill.output_root") ||
         F.hasFnAttribute("omill.virtual_specialized") ||
         F.hasFnAttribute("omill.closed_root_slice_root") ||
         F.hasFnAttribute("omill.vm_wrapper") ||
         F.hasFnAttribute("omill.vm_newly_lifted") ||
         F.hasFnAttribute("omill.newly_lifted") ||
         F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
         F.getFnAttribute("omill.vm_outlined_virtual_call").isValid();
}

bool shouldRunClosedRootSliceCodeBearingPass(llvm::Function &F) {
  if (!isClosedRootSliceScopedModule(*F.getParent()))
    return true;
  return isClosedRootSliceFunction(F) &&
         isClosedRootSliceCodeBearingFunction(F);
}

bool shouldRunClosedRootSliceNativePass(llvm::Function &F) {
  if (!F.getName().ends_with("_native"))
    return false;
  if (!isClosedRootSliceScopedModule(*F.getParent()))
    return true;
  return isClosedRootSliceFunction(F);
}

bool moduleFlagEnabled(const llvm::Module &M, llvm::StringRef flag_name) {
  auto *md = M.getModuleFlag(flag_name);
  auto *constant_md = llvm::dyn_cast_or_null<llvm::ConstantAsMetadata>(md);
  auto *constant_int =
      constant_md ? llvm::dyn_cast<llvm::ConstantInt>(constant_md->getValue())
                  : nullptr;
  return constant_int && constant_int->isOne();
}

bool isNoABIModeModule(const llvm::Module &M) {
  return moduleFlagEnabled(M, "omill.no_abi_mode");
}

bool isSyntheticBlockLikeFunctionName(llvm::StringRef name) {
  return name.starts_with("blk_") || name.starts_with("block_");
}

bool isClosedRootSliceNativeSubHelperName(llvm::StringRef name) {
  return name.starts_with("sub_") && name.ends_with("_native");
}

bool hasCorrespondingLiftedOutputRoot(const llvm::Function &F) {
  if (!F.getName().ends_with("_native"))
    return false;
  llvm::StringRef lifted_name = F.getName().drop_back(7);
  auto *lifted = F.getParent()->getFunction(lifted_name);
  return lifted &&
         (lifted->hasFnAttribute("omill.output_root") ||
          isClosedRootSliceRoot(*lifted));
}

struct InternalizeDeadNativeHelpersPass
    : llvm::PassInfoMixin<InternalizeDeadNativeHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    const bool has_live_dispatch = llvm::any_of(M, [](llvm::Function &F) {
      return isDispatchIntrinsicName(F.getName()) && !F.use_empty();
    });
    if (has_live_dispatch) {
      return llvm::PreservedAnalyses::all();
    }

    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      if (F.hasFnAttribute("omill.output_root") || isClosedRootSliceRoot(F) ||
          hasCorrespondingLiftedOutputRoot(F)) {
        continue;
      }
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

llvm::Function *lookupDefinedLiftedOrBlockTarget(llvm::Module &M, uint64_t pc);

llvm::DenseSet<llvm::Function *> collectStructurallyReferencedLiftedTargets(
    llvm::Module &M) {
  llvm::DenseSet<llvm::Function *> targets;
  const bool debug_public_root_seeds =
      (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
  auto record_target = [&](uint64_t pc) {
    if (auto *F = lookupDefinedLiftedOrBlockTarget(M, pc)) {
      targets.insert(F);
      if (debug_public_root_seeds) {
        llvm::errs() << "[structural-target] keep pc=0x"
                     << llvm::utohexstr(pc) << " fn=" << F->getName() << "\n";
      }
    } else if (debug_public_root_seeds) {
      llvm::errs() << "[structural-target] missing pc=0x"
                   << llvm::utohexstr(pc) << "\n";
    }
  };

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;

        if (auto *callee = call->getCalledFunction()) {
          if ((callee->getName() == "__remill_function_call" ||
               callee->getName() == "__remill_jump") &&
              call->arg_size() >= 3) {
            if (auto *pc_ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              record_target(pc_ci->getZExtValue());
            }
          }

          if (call->arg_size() >= 2 &&
              isDispatchIntrinsicName(callee->getName())) {
            if (auto *pc_ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              record_target(pc_ci->getZExtValue());
            }
          }

          if (!callee->isDeclaration())
            continue;
          if (uint64_t target_pc = extractEntryVA(callee->getName()); target_pc != 0)
            record_target(target_pc);
          continue;
        }

        if (auto *callee_fn = llvm::dyn_cast<llvm::Function>(
                call->getCalledOperand()->stripPointerCasts())) {
          if (callee_fn->getName().contains("CALLI") && call->arg_size() >= 3) {
            if (auto *pc_ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2))) {
              record_target(pc_ci->getZExtValue());
            }
          }
        }

        llvm::ConstantInt *target_ci = nullptr;
        if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(call->getCalledOperand());
            ce && ce->getOpcode() == llvm::Instruction::IntToPtr) {
          target_ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
        }
        if (!target_ci) {
          if (auto *itp =
                  llvm::dyn_cast<llvm::IntToPtrInst>(call->getCalledOperand()))
            target_ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
        }
        if (target_ci)
          record_target(target_ci->getZExtValue());
      }
    }
  }

  return targets;
}

struct InternalizeDeadLiftedHelpersPass
    : llvm::PassInfoMixin<InternalizeDeadLiftedHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;
    llvm::SmallVector<llvm::Function *, 16> erase_list;
    llvm::DenseSet<llvm::Function *> structurally_referenced_targets =
        collectStructurallyReferencedLiftedTargets(M);
    llvm::SmallVector<llvm::GlobalValue *, 8> compiler_used_targets;
    const bool debug_public_root_seeds =
        (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
    for (auto &F : M) {
      if (!isLiftedFunction(F))
        continue;
      if (F.hasFnAttribute("omill.output_root") || isClosedRootSliceRoot(F))
        continue;
      if (structurally_referenced_targets.contains(&F)) {
        compiler_used_targets.push_back(&F);
        if (F.hasLocalLinkage()) {
          F.setLinkage(llvm::GlobalValue::ExternalLinkage);
          changed = true;
        }
        if (debug_public_root_seeds) {
          llvm::errs() << "[lift-cleanup] preserve " << F.getName()
                       << " via structural reference linkage="
                       << static_cast<int>(F.getLinkage()) << "\n";
        }
        continue;
      }
      if (!F.use_empty())
        continue;
      if (F.hasExternalLinkage()) {
        if (debug_public_root_seeds) {
          llvm::errs() << "[lift-cleanup] internalize " << F.getName() << "\n";
        }
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
        changed = true;
      }
      if (F.use_empty())
        erase_list.push_back(&F);
    }

    if (!compiler_used_targets.empty()) {
      llvm::appendToCompilerUsed(M, compiler_used_targets);
      changed = true;
    }

    for (auto *F : erase_list) {
      F->eraseFromParent();
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

struct EraseDeadTrivialSelfLoopPlaceholderCallsPass
    : llvm::PassInfoMixin<EraseDeadTrivialSelfLoopPlaceholderCallsPass> {
  static bool isDirectSyntheticSelfLoop(const llvm::Function &F) {
    if (F.isDeclaration() || F.empty() || F.size() != 1)
      return false;

    const auto &BB = F.getEntryBlock();
    const auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
    if (!br || !br->isUnconditional() || br->getSuccessor(0) != &BB)
      return false;

    for (const auto &I : BB) {
      if (&I == BB.getTerminator() || I.isDebugOrPseudoInst())
        continue;
      return false;
    }
    return true;
  }

  static bool isSelfRecursiveTailLoopShell(const llvm::Function &F) {
    if (F.isDeclaration() || F.empty() || F.size() != 1)
      return false;

    const auto &BB = F.getEntryBlock();
    const llvm::CallBase *self_call = nullptr;
    const llvm::ReturnInst *ret = nullptr;
    for (const auto &I : BB) {
      if (I.isDebugOrPseudoInst())
        continue;
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee == &F) {
          if (self_call)
            return false;
          self_call = CB;
          continue;
        }
        if (!callee || !callee->isDeclaration())
          return false;
        continue;
      }
      if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
        if (ret)
          return false;
        ret = RI;
      }
    }

    if (!self_call || !ret)
      return false;
    const llvm::Value *returned = ret->getReturnValue();
    return returned && returned->stripPointerCasts() == self_call;
  }


  static bool isTrivialSelfLoopPlaceholderImpl(
      const llvm::Function &F, llvm::DenseSet<const llvm::Function *> &visiting) {
    if (!visiting.insert(&F).second)
      return true;

    if (isDirectSyntheticSelfLoop(F) || isSelfRecursiveTailLoopShell(F)) {
      visiting.erase(&F);
      return true;
    }

    if (F.isDeclaration() || F.empty() || F.size() != 1) {
      visiting.erase(&F);
      return false;
    }

    const llvm::CallBase *call = nullptr;
    const llvm::ReturnInst *ret = nullptr;
    for (const auto &I : F.getEntryBlock()) {
      if (I.isDebugOrPseudoInst())
        continue;
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        if (call) {
          visiting.erase(&F);
          return false;
        }
        call = CB;
        continue;
      }
      if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
        if (ret) {
          visiting.erase(&F);
          return false;
        }
        ret = RI;
        continue;
      }
      visiting.erase(&F);
      return false;
    }

    auto *callee = call ? call->getCalledFunction() : nullptr;
    if (!call || !ret || !callee || callee->isDeclaration()) {
      visiting.erase(&F);
      return false;
    }

    const llvm::Value *returned = ret->getReturnValue();
    if (returned && returned->stripPointerCasts() != call) {
      visiting.erase(&F);
      return false;
    }

    const bool placeholder = isTrivialSelfLoopPlaceholderImpl(*callee, visiting);
    visiting.erase(&F);
    return placeholder;
  }

  static bool isTrivialSelfLoopPlaceholder(const llvm::Function &F) {
    llvm::DenseSet<const llvm::Function *> visiting;
    return isTrivialSelfLoopPlaceholderImpl(F, visiting);
  }

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || !CI->use_empty() || CI->isMustTailCall())
            continue;
          auto *callee = CI->getCalledFunction();
          if (!callee || !isTrivialSelfLoopPlaceholder(*callee))
            continue;

          bool has_following_call = false;
          for (auto it = std::next(CI->getIterator()), end = BB.end(); it != end;
               ++it) {
            if (it->isDebugOrPseudoInst())
              continue;
            if (llvm::isa<llvm::CallBase>(&*it)) {
              has_following_call = true;
              break;
            }
          }
          if (!has_following_call)
            continue;

          CI->eraseFromParent();
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};


static constexpr llvm::StringLiteral kRootEntrySeedExprsAttr =
    "omill.export_entry_seed_exprs";


struct DirectABIShapingPass : llvm::PassInfoMixin<DirectABIShapingPass> {
  static llvm::Type *abiScalarType(llvm::LLVMContext &ctx, unsigned size,
                                   bool is_vector) {
    if (is_vector)
      return llvm::FixedVectorType::get(llvm::Type::getInt64Ty(ctx), 2);
    switch (size) {
      case 1:
        return llvm::Type::getInt8Ty(ctx);
      case 2:
        return llvm::Type::getInt16Ty(ctx);
      case 4:
        return llvm::Type::getInt32Ty(ctx);
      case 8:
      default:
        return llvm::Type::getInt64Ty(ctx);
    }
  }

  static llvm::Value *bytePtrAtOffset(llvm::IRBuilder<> &B, llvm::Value *base,
                                      uint64_t offset) {
    auto *i8 = llvm::Type::getInt8Ty(B.getContext());
    auto *byte_base = B.CreatePointerBitCastOrAddrSpaceCast(
        base, llvm::PointerType::get(B.getContext(), 0));
    return B.CreateConstGEP1_64(i8, byte_base, offset);
  }

  static void applyRequestedRootSeedExprs(llvm::Module &M, llvm::IRBuilder<> &B,
                                          llvm::Function &shim,
                                          llvm::Value *state_storage) {
    auto attr = shim.getFnAttribute(kRootEntrySeedExprsAttr);
    if (!attr.isValid() || !attr.isStringAttribute())
      return;

    StateFieldMap field_map(M);
    auto getShimParamAsI64 = [&](unsigned index) -> llvm::Value * {
      if (index >= shim.arg_size())
        return nullptr;
      auto *arg = shim.getArg(index);
      if (arg->getType()->isPointerTy())
        return B.CreatePtrToInt(arg, B.getInt64Ty(), arg->getName() + ".i64");
      if (arg->getType()->isIntegerTy())
        return B.CreateZExtOrTrunc(arg, B.getInt64Ty(), arg->getName() + ".i64");
      return nullptr;
    };

    std::function<llvm::Value *(llvm::StringRef)> evalExpr;
    evalExpr = [&](llvm::StringRef text) -> llvm::Value * {
      text = text.trim();
      if (text.starts_with("param(") && text.ends_with(")")) {
        unsigned idx = 0;
        if (!text.drop_front(6).drop_back().getAsInteger(10, idx))
          return getShimParamAsI64(idx);
        return nullptr;
      }
      if (text.starts_with("const(") && text.ends_with(")")) {
        auto body = text.drop_front(6).drop_back();
        uint64_t value = 0;
        if (body.starts_with("0x")) {
          if (!body.drop_front(2).getAsInteger(16, value))
            return llvm::ConstantInt::get(B.getInt64Ty(), value);
        } else if (!body.getAsInteger(10, value)) {
          return llvm::ConstantInt::get(B.getInt64Ty(), value);
        }
        return nullptr;
      }
      auto evalBinary = [&](llvm::StringRef op, auto &&fn) -> llvm::Value * {
        if (!text.starts_with(op) || !text.ends_with(")"))
          return nullptr;
        auto body = text.drop_front(op.size()).drop_back();
        int depth = 0;
        size_t split = llvm::StringRef::npos;
        for (size_t i = 0; i < body.size(); ++i) {
          char c = body[i];
          if (c == '(') ++depth;
          else if (c == ')') --depth;
          else if (c == ',' && depth == 0) { split = i; break; }
        }
        if (split == llvm::StringRef::npos)
          return nullptr;
        auto *lhs = evalExpr(body.take_front(split));
        auto *rhs = evalExpr(body.drop_front(split + 1));
        if (!lhs || !rhs)
          return nullptr;
        return fn(lhs, rhs);
      };
      auto evalUnary = [&](llvm::StringRef op) -> llvm::Value * {
        if (!text.starts_with(op) || !text.ends_with(")"))
          return nullptr;
        auto *v = evalExpr(text.drop_front(op.size()).drop_back());
        if (!v)
          return nullptr;
        return B.CreateAnd(v, llvm::ConstantInt::get(B.getInt64Ty(), 0xffffffffull));
      };
      if (auto *v = evalUnary("zext32("))
        return v;
      if (auto *v = evalBinary("add64(", [&](llvm::Value *lhs, llvm::Value *rhs) {
            return B.CreateAdd(lhs, rhs);
          }))
        return v;
      if (auto *v = evalBinary("xor64(", [&](llvm::Value *lhs, llvm::Value *rhs) {
            return B.CreateXor(lhs, rhs);
          }))
        return v;
      if (auto *v = evalBinary("xor32(", [&](llvm::Value *lhs, llvm::Value *rhs) {
            auto *x = B.CreateXor(lhs, rhs);
            return B.CreateAnd(x,
                               llvm::ConstantInt::get(B.getInt64Ty(), 0xffffffffull));
          }))
        return v;
      if (auto *v = evalBinary("and32(", [&](llvm::Value *lhs, llvm::Value *rhs) {
            auto *x = B.CreateAnd(lhs, rhs);
            return B.CreateAnd(x,
                               llvm::ConstantInt::get(B.getInt64Ty(), 0xffffffffull));
          }))
        return v;
      return nullptr;
    };

    llvm::SmallVector<llvm::StringRef, 16> entries;
    attr.getValueAsString().split(entries, ';', -1, false);
    for (auto entry : entries) {
      entry = entry.trim();
      if (entry.empty())
        continue;
      auto pair = entry.split('=');
      if (pair.first.empty() || pair.second.empty())
        continue;
      auto field = field_map.fieldByName(pair.first.trim());
      if (!field || field->size != 8)
        continue;
      auto *value = evalExpr(pair.second);
      if (!value)
        continue;
      auto *dest_i8 = bytePtrAtOffset(B, state_storage, field->offset);
      auto *dest = B.CreatePointerBitCastOrAddrSpaceCast(
          dest_i8, llvm::PointerType::get(M.getContext(), 0));
      B.CreateStore(value, dest);
    }
  }


  static void copyABIRelevantAttrs(llvm::Function &from, llvm::Function &to) {
    for (auto &attr_set : from.getAttributes().getFnAttrs()) {
      if (attr_set.isEnumAttribute()) {
        auto kind = attr_set.getKindAsEnum();
        if (kind == llvm::Attribute::AlwaysInline ||
            kind == llvm::Attribute::NoInline ||
            kind == llvm::Attribute::OptimizeNone) {
          continue;
        }
        to.addFnAttr(kind);
      } else if (attr_set.isStringAttribute()) {
        auto key = attr_set.getKindAsString();
        if (key == "omill.internal_output_root")
          continue;
        to.addFnAttr(key, attr_set.getValueAsString());
      }
    }
  }

  static llvm::Value *buildRequestedRootReturnTransform(
      llvm::IRBuilder<> &B, llvm::Value *root_call, llvm::Type *ret_ty,
      llvm::StringRef transform) {
    if (!root_call || !ret_ty || !ret_ty->isIntegerTy())
      return nullptr;
    if (!transform.starts_with("low8_add_const:"))
      return nullptr;

    unsigned imm = 0;
    if (transform.drop_front(15).getAsInteger(10, imm) || imm > 0xffu)
      return nullptr;

    llvm::Value *call_i64 = root_call;
    if (call_i64->getType()->isPointerTy()) {
      call_i64 = B.CreatePtrToInt(call_i64, B.getInt64Ty(), "root.call.i64");
    } else if (call_i64->getType()->isIntegerTy()) {
      call_i64 = B.CreateZExtOrTrunc(call_i64, B.getInt64Ty(), "root.call.i64");
    } else {
      return nullptr;
    }

    auto *low8 = B.CreateTrunc(call_i64, B.getInt8Ty(), "root.ret.low8");
    auto *sum8 = B.CreateAdd(low8, B.getInt8(static_cast<uint8_t>(imm)),
                             "root.ret.sum8");
    if (ret_ty->isIntegerTy(8))
      return sum8;
    return B.CreateZExt(sum8, ret_ty, "root.ret.zext");
  }


  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
    auto &cc_info = MAM.getResult<CallingConventionAnalysis>(M);
    bool changed = false;
    llvm::SmallVector<llvm::Function *, 8> roots;
    for (auto &F : M) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.internal_output_root") &&
          hasLiftedRemillSignature(F)) {
        roots.push_back(&F);
      }
    }

    for (auto *root : roots) {
      auto *abi = cc_info.getABI(root);
      if (!abi)
        continue;

      llvm::SmallVector<llvm::Type *, 8> param_tys;
      for (auto &param : abi->params)
        param_tys.push_back(
            abiScalarType(M.getContext(), param.size, /*is_vector=*/false));

      llvm::Type *ret_ty = llvm::Type::getVoidTy(M.getContext());
      if (abi->ret.has_value()) {
        ret_ty = abiScalarType(M.getContext(), abi->ret->size,
                               abi->ret->is_vector);
      }

      auto *new_fty = llvm::FunctionType::get(ret_ty, param_tys, false);
      if (root->getFunctionType() == new_fty)
        continue;

      const std::string public_name = root->getName().str();
      std::string internal_name = "__omill_internal_output_root_" + public_name;
      while (M.getFunction(internal_name))
        internal_name += "_";

      const bool had_closed_slice = root->hasFnAttribute("omill.closed_root_slice");
      const bool had_closed_slice_root =
          root->hasFnAttribute("omill.closed_root_slice_root");

      root->setName(internal_name);
      root->removeFnAttr("omill.output_root");
      root->addFnAttr("omill.internal_output_root", "1");
      root->setLinkage(llvm::GlobalValue::InternalLinkage);
      root->removeFnAttr(llvm::Attribute::OptimizeNone);
      root->removeFnAttr(llvm::Attribute::AlwaysInline);
      root->addFnAttr(llvm::Attribute::NoInline);

      auto *shim = llvm::Function::Create(
          new_fty, llvm::GlobalValue::ExternalLinkage, public_name, M);
      copyABIRelevantAttrs(*root, *shim);
      shim->addFnAttr("omill.output_root", "1");
      if (had_closed_slice)
        shim->addFnAttr("omill.closed_root_slice", "1");
      if (had_closed_slice_root)
        shim->addFnAttr("omill.closed_root_slice_root", "1");

      auto *entry = llvm::BasicBlock::Create(M.getContext(), "entry", shim);
      llvm::IRBuilder<> B(entry);

      uint64_t max_offset = 0;
      for (auto &param : abi->params)
        max_offset = std::max<uint64_t>(max_offset, param.state_offset + param.size);
      if (abi->ret.has_value())
        max_offset = std::max<uint64_t>(max_offset,
                                        abi->ret->state_offset + abi->ret->size);
      for (auto off : abi->xmm_live_ins)
        max_offset = std::max<uint64_t>(max_offset, off + 16);
      for (auto off : abi->extra_gpr_live_ins)
        max_offset = std::max<uint64_t>(max_offset, off + 8);
      for (auto off : abi->extra_gpr_live_outs)
        max_offset = std::max<uint64_t>(max_offset, off + 8);

      const uint64_t state_size = std::max<uint64_t>(4096, max_offset + 0x40);
      auto *state_storage_ty =
          llvm::ArrayType::get(llvm::Type::getInt8Ty(M.getContext()), state_size);
      auto *state_storage = B.CreateAlloca(state_storage_ty, nullptr, "abi.state");
      state_storage->setAlignment(llvm::Align(16));
      auto *state_ptr =
          B.CreatePointerBitCastOrAddrSpaceCast(state_storage,
                                                root->getArg(0)->getType());
      B.CreateMemSet(
          B.CreatePointerBitCastOrAddrSpaceCast(
              state_storage, llvm::PointerType::get(M.getContext(), 0)),
          B.getInt8(0), state_size, llvm::Align(16));

      unsigned arg_index = 0;
      for (auto &param : abi->params) {
        if (arg_index >= shim->arg_size())
          break;
        auto *dest_i8 = bytePtrAtOffset(B, state_storage, param.state_offset);
        auto *dest = B.CreatePointerBitCastOrAddrSpaceCast(
            dest_i8, llvm::PointerType::get(M.getContext(), 0));
        B.CreateStore(shim->getArg(arg_index), dest);
        ++arg_index;
      }

      applyRequestedRootSeedExprs(M, B, *shim, state_storage);

      uint64_t entry_va = extractEntryVA(public_name);
      auto *pc = llvm::ConstantInt::get(llvm::Type::getInt64Ty(M.getContext()),
                                        entry_va);
      auto *memory =
          llvm::ConstantPointerNull::get(
              llvm::cast<llvm::PointerType>(root->getArg(2)->getType()));
      auto *root_call = B.CreateCall(root, {state_ptr, pc, memory});

      if (!abi->ret.has_value()) {
        B.CreateRetVoid();
      } else {
        auto transform_attr =
            shim->getFnAttribute("omill.requested_root_return_transform");
        if (transform_attr.isValid() && transform_attr.isStringAttribute()) {
          if (auto *ret = buildRequestedRootReturnTransform(
                  B, root_call, ret_ty, transform_attr.getValueAsString())) {
            B.CreateRet(ret);
            changed = true;
            continue;
          }
        }
        auto *dest_i8 = bytePtrAtOffset(B, state_storage, abi->ret->state_offset);
        auto *dest = B.CreatePointerBitCastOrAddrSpaceCast(
            dest_i8, llvm::PointerType::get(M.getContext(), 0));
        auto *ret = B.CreateLoad(ret_ty, dest);
        B.CreateRet(ret);
      }

      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct CanonicalizeABIBoundaryDeclarationsPass
    : llvm::PassInfoMixin<CanonicalizeABIBoundaryDeclarationsPass> {
  struct NativeBoundaryDecodeSummary {
    std::optional<uint64_t> direct_target_pc;
    std::optional<uint64_t> continuation_pc;
  };

  static NativeBoundaryDecodeSummary decodeNativeBoundarySummaryFromBinary(
      const BinaryMemoryMap &binary_memory, uint64_t boundary_pc) {
    NativeBoundaryDecodeSummary summary;
    uint8_t bytes[192] = {};
    if (!binary_memory.read(boundary_pc, bytes, sizeof(bytes)))
      return summary;
    for (unsigned i = 0; i + 4 < sizeof(bytes); ++i) {
      if (bytes[i] != 0xE8)
        continue;
      int32_t rel = 0;
      std::memcpy(&rel, &bytes[i + 1], sizeof(rel));
      summary.direct_target_pc =
          static_cast<uint64_t>(static_cast<int64_t>(boundary_pc) +
                                static_cast<int64_t>(i) + 5 +
                                static_cast<int64_t>(rel));
      summary.continuation_pc = boundary_pc + i + 5;
      break;
    }
    return summary;
  }

  static bool looksLikeVmEnterExecutableTarget(
      const BinaryMemoryMap &binary_memory, uint64_t boundary_pc) {
    uint8_t bytes[32] = {};
    if (!binary_memory.read(boundary_pc, bytes, sizeof(bytes)))
      return false;

    unsigned stack_setup_ops = 0;
    bool saw_pushfq = false;
    bool saw_early_direct_call = false;
    for (unsigned i = 0; i < 16 && i < sizeof(bytes); ++i) {
      switch (bytes[i]) {
        case 0x50:
        case 0x51:
        case 0x52:
        case 0x53:
        case 0x54:
        case 0x55:
        case 0x56:
        case 0x57:
        case 0x58:
        case 0x59:
        case 0x5A:
        case 0x5B:
        case 0x5C:
        case 0x5D:
        case 0x5E:
        case 0x5F:
          ++stack_setup_ops;
          break;
        case 0x9C:
          ++stack_setup_ops;
          saw_pushfq = true;
          break;
        case 0xE8:
          if (i < 24)
            saw_early_direct_call = true;
          break;
        default:
          break;
      }
    }

    return saw_pushfq && stack_setup_ops >= 5 && !saw_early_direct_call;
  }

  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
    const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);
    bool changed = false;
    llvm::SmallVector<llvm::Function *, 16> decls;
    for (auto &F : M) {
      if (F.isDeclaration() &&
          (F.getName().starts_with("blk_") || F.getName().starts_with("sub_"))) {
        decls.push_back(&F);
      }
    }

    for (auto *decl : decls) {
      uint64_t boundary_pc = 0;
      uint64_t target_pc = 0;
      uint64_t executable_target_pc = 0;
      if (auto fact = readExecutableTargetFact(*decl))
        executable_target_pc = fact->raw_target_pc;
      auto boundary_fact = readBoundaryFact(*decl);
      uint64_t vm_enter_target_pc =
          boundary_fact && boundary_fact->is_vm_enter && boundary_fact->boundary_pc
              ? *boundary_fact->boundary_pc
              : 0;
      if (boundary_fact && boundary_fact->boundary_pc)
        boundary_pc = *boundary_fact->boundary_pc;
      if (!boundary_pc)
        boundary_pc = vm_enter_target_pc;
      if (!boundary_pc)
        boundary_pc = executable_target_pc;
      if (!boundary_pc)
        boundary_pc = extractEntryVA(decl->getName());
      if (!boundary_pc)
        boundary_pc = extractBlockPC(decl->getName());
      if (!boundary_pc)
        continue;

      const auto native_summary =
          decodeNativeBoundarySummaryFromBinary(binary_memory, boundary_pc);

      if (!executable_target_pc) {
        std::string existing_exec_name =
            "omill_executable_target_" + llvm::utohexstr(boundary_pc);
        if (M.getFunction(existing_exec_name))
          executable_target_pc = boundary_pc;
      }
      if (!vm_enter_target_pc) {
        std::string existing_vm_enter_name =
            "omill_vm_enter_target_" + llvm::utohexstr(boundary_pc);
        if (M.getFunction(existing_vm_enter_name))
          vm_enter_target_pc = boundary_pc;
      }

      const bool is_explicit_vm_enter =
          vm_enter_target_pc != 0 ||
          (boundary_fact &&
           (boundary_fact->exit_disposition == BoundaryDisposition::kVmEnter ||
            boundary_fact->exit_disposition ==
                BoundaryDisposition::kNestedVmEnter));
      const bool looks_like_vm_enter =
          looksLikeVmEnterExecutableTarget(binary_memory, boundary_pc);

      target_pc = boundary_pc;
      if (!is_explicit_vm_enter) {
        if (boundary_fact && boundary_fact->native_target_pc)
          target_pc = *boundary_fact->native_target_pc;
        if (!target_pc)
          if (native_summary.direct_target_pc.has_value()) {
            target_pc = *native_summary.direct_target_pc;
          }
      }
      if (!target_pc)
        target_pc = executable_target_pc ? executable_target_pc : boundary_pc;

      const bool is_direct_native_target =
          target_pc != boundary_pc;
      const bool is_vm_enter_executable_target =
          !is_direct_native_target &&
          (is_explicit_vm_enter || looks_like_vm_enter);
      const bool is_decodable_executable_target =
          !is_direct_native_target && !is_vm_enter_executable_target &&
          (executable_target_pc != 0 ||
           canDecodeX86InstructionAt(binary_memory, boundary_pc));

      const bool is_native_reenter =
          boundary_fact &&
          boundary_fact->exit_disposition ==
              BoundaryDisposition::kVmExitNativeCallReenter;
      if (is_direct_native_target && is_native_reenter &&
          native_summary.continuation_pc.has_value()) {
        auto *continuation =
            findLiftedOrBlockFunctionByPC(M, *native_summary.continuation_pc);
        if (continuation && !continuation->isDeclaration() &&
            decl->arg_size() >= 3 && continuation->arg_size() >= 3 &&
            continuation->getReturnType() == decl->getReturnType()) {
          std::string native_name = "omill_native_target_";
          native_name += llvm::utohexstr(target_pc);
          auto *native_decl = M.getFunction(native_name);
          if (!native_decl) {
            native_decl = llvm::Function::Create(
                decl->getFunctionType(), llvm::GlobalValue::ExternalLinkage,
                native_name, M);
          }
          BoundaryFact native_decl_fact;
          native_decl_fact.boundary_pc = boundary_pc;
          native_decl_fact.native_target_pc = target_pc;
          native_decl_fact.kind = BoundaryKind::kNativeBoundary;
          writeBoundaryFact(*native_decl, native_decl_fact);

          auto *entry =
              llvm::BasicBlock::Create(M.getContext(), "entry", decl);
          llvm::IRBuilder<> ir(entry);
          auto arg_it = decl->arg_begin();
          llvm::Value *state_arg = &*arg_it++;
          llvm::Value *memory_arg = nullptr;
          auto *continuation_pc = llvm::ConstantInt::get(
              continuation->getFunctionType()->getParamType(1),
              *native_summary.continuation_pc);
          ++arg_it;  // skip current pc arg
          memory_arg = &*arg_it;
          auto *native_call =
              ir.CreateCall(native_decl, {state_arg,
                                          llvm::ConstantInt::get(
                                              decl->getFunctionType()->getParamType(1),
                                              target_pc),
                                          memory_arg});
          auto *continuation_call =
              ir.CreateCall(continuation, {state_arg, continuation_pc, native_call});
          ir.CreateRet(continuation_call);
          auto updated_boundary_fact = boundary_fact.value_or(BoundaryFact{});
          updated_boundary_fact.boundary_pc = boundary_pc;
          updated_boundary_fact.continuation_pc =
              *native_summary.continuation_pc;
          updated_boundary_fact.kind = BoundaryKind::kNativeBoundary;
          if (updated_boundary_fact.exit_disposition ==
              BoundaryDisposition::kUnknown) {
            updated_boundary_fact.exit_disposition =
                BoundaryDisposition::kVmExitNativeCallReenter;
          }
          writeBoundaryFact(*decl, updated_boundary_fact);
          changed = true;
          continue;
        }
      }

      std::string replacement_name =
          (is_direct_native_target
               ? "omill_native_target_"
               : (is_vm_enter_executable_target
                      ? "omill_vm_enter_target_"
                      : (is_decodable_executable_target
                             ? "omill_executable_target_"
                             : "omill_native_boundary_"))) +
          llvm::utohexstr(target_pc);
      auto *replacement = M.getFunction(replacement_name);
      if (!replacement) {
        replacement = llvm::Function::Create(decl->getFunctionType(),
                                             llvm::GlobalValue::ExternalLinkage,
                                             replacement_name, M);
        for (auto &attr : decl->getAttributes().getFnAttrs()) {
          if (attr.isEnumAttribute())
            replacement->addFnAttr(attr.getKindAsEnum());
          else if (attr.isStringAttribute())
            replacement->addFnAttr(attr.getKindAsString(),
                                   attr.getValueAsString());
        }
        if (is_direct_native_target || is_vm_enter_executable_target ||
            !is_decodable_executable_target) {
          BoundaryFact replacement_boundary_fact =
              boundary_fact.value_or(BoundaryFact{});
          replacement_boundary_fact.boundary_pc = boundary_pc;
          if (is_direct_native_target) {
            replacement_boundary_fact.native_target_pc = target_pc;
            replacement_boundary_fact.kind = BoundaryKind::kNativeBoundary;
          } else if (is_vm_enter_executable_target) {
            replacement_boundary_fact.is_vm_enter = true;
            replacement_boundary_fact.exit_disposition =
                BoundaryDisposition::kNestedVmEnter;
            replacement_boundary_fact.kind =
                BoundaryKind::kNestedVmEnterBoundary;
          }
          writeBoundaryFact(*replacement, replacement_boundary_fact);
        }
        if (is_decodable_executable_target) {
          ExecutableTargetFact fact;
          fact.raw_target_pc = boundary_pc;
          writeExecutableTargetFact(*replacement, fact);
        }
      }

      decl->replaceAllUsesWith(replacement);
      if (decl->use_empty()) {
        decl->eraseFromParent();
      }
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

unsigned countNonDebugInstructions(const llvm::Function &F) {
  unsigned inst_count = 0;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::DbgInfoIntrinsic>(&I))
        continue;
      ++inst_count;
    }
  }
  return inst_count;
}

bool isSyntheticBlockLikeNativeHelperName(llvm::StringRef name) {
  if (isSyntheticBlockLikeFunctionName(name))
    return true;
  if (!name.ends_with("_native"))
    return false;

  auto stem = name.drop_back(7);
  if (stem.ends_with("_pair"))
    stem = stem.drop_back(5);

  if (stem.starts_with("blk_")) {
    uint64_t pc = 0;
    return !stem.drop_front(4).getAsInteger(16, pc);
  }
  if (stem.starts_with("block_"))
    return extractBlockPC(stem) != 0;

  return false;
}

bool shouldPreserveOutlinedWrapper(
    const llvm::Function &F,
    const VirtualCalleeRegistry *virtual_callees = nullptr) {
  return F.hasFnAttribute("omill.vm_wrapper") ||
         F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
         F.getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
         F.getFnAttribute("omill.trace_native_target").isValid() ||
         (virtual_callees &&
          virtual_callees->lookup(F.getName()).has_value());
}

static bool loopifyClosedSliceSelfRecursiveBlockHelper(llvm::Function &F,
                                                       bool debug);

static bool isModeledStructuralBoundaryTarget(const llvm::Function &F) {
  auto name = F.getName();
  return readBoundaryFact(F).has_value() ||
         readExecutableTargetFact(F).has_value() ||
         name.starts_with("omill_native_target_") ||
         name.starts_with("omill_native_boundary_") ||
         name.starts_with("omill_vm_enter_target_") ||
         name.starts_with("omill_executable_target_");
}

static llvm::Value *coerceValueToType(llvm::IRBuilder<> &B, llvm::Value *V,
                                      llvm::Type *target_ty,
                                      llvm::StringRef name) {
  if (V->getType() == target_ty)
    return V;
  if (V->getType()->isIntegerTy() && target_ty->isIntegerTy())
    return B.CreateIntCast(V, target_ty, false, name);
  if (V->getType()->isPointerTy() && target_ty->isIntegerTy())
    return B.CreatePtrToInt(V, target_ty, name);
  if (V->getType()->isIntegerTy() && target_ty->isPointerTy())
    return B.CreateIntToPtr(V, target_ty, name);
  if ((V->getType()->isPointerTy() && target_ty->isPointerTy()) ||
      (V->getType()->isVectorTy() && target_ty->isVectorTy()) ||
      (V->getType()->isFloatingPointTy() && target_ty->isFloatingPointTy())) {
    return B.CreateBitCast(V, target_ty, name);
  }
  return nullptr;
}

bool maybeMarkClosedRootSliceHelperForInlining(
    llvm::Function &F, unsigned max_inst_count, bool native_helper,
    const VirtualCalleeRegistry *virtual_callees = nullptr) {
  const bool debug_inline =
      (std::getenv("OMILL_DEBUG_CLOSED_SLICE_INLINE") != nullptr);
  auto debug_skip = [&](llvm::StringRef reason) {
    if (!debug_inline)
      return;
    llvm::errs() << "[closed-slice-inline] skip " << F.getName()
                 << " native=" << native_helper << " reason=" << reason
                 << "\n";
  };
  auto debug_mark = [&](unsigned inline_budget, unsigned inst_count) {
    if (!debug_inline)
      return;
    llvm::errs() << "[closed-slice-inline] mark " << F.getName()
                 << " native=" << native_helper
                 << " insts=" << inst_count
                 << " budget=" << inline_budget
                 << " uses=" << F.getNumUses() << "\n";
  };

  if (F.isDeclaration()) {
    debug_skip("declaration");
    return false;
  }
  if (!isClosedRootSliceFunction(F)) {
    debug_skip("not_closed_root_slice");
    return false;
  }
  if (isClosedRootSliceRoot(F)) {
    debug_skip("root");
    return false;
  }
  if (F.getName().ends_with("_native") != native_helper) {
    debug_skip("native_mismatch");
    return false;
  }
  const bool is_block_like =
      isSyntheticBlockLikeNativeHelperName(F.getName());
  if (!native_helper && is_block_like && !F.hasLocalLinkage() &&
      !isNoABIModeModule(*F.getParent())) {
    debug_skip("externally_visible_helper");
    return false;
  }
  const bool is_native_sub_helper =
      native_helper && isClosedRootSliceNativeSubHelperName(F.getName()) &&
      !F.hasFnAttribute("omill.output_root");
  if (!is_block_like && !is_native_sub_helper) {
    debug_skip("not_helper_shape");
    return false;
  }
  if (native_helper && shouldPreserveOutlinedWrapper(F, virtual_callees)) {
    debug_skip("preserve_outlined_wrapper");
    return false;
  }
  if (is_native_sub_helper && F.getNumUses() > 2) {
    debug_skip("native_sub_too_many_uses");
    return false;
  }
  unsigned inline_budget = max_inst_count;
  if (is_native_sub_helper && F.use_empty()) {
    // Dead closed-slice native wrappers still clutter ABI output if they keep
    // external linkage. Internalize them regardless of size so GlobalDCE can
    // erase the unreachable state-wrapper remnants.
    inline_budget = std::numeric_limits<unsigned>::max();
  }
  if (native_helper) {
    // Late continuation discovery can produce a few larger closed-slice
    // blk_*_native wrappers with a single remaining caller. Allow a wider
    // inline budget in that case so the root wrapper still collapses.
    if (is_block_like && F.hasOneUse())
      inline_budget = std::max(inline_budget, 1024u);
    else if (is_block_like && F.getNumUses() <= 2)
      inline_budget = std::max(inline_budget, 512u);
    else if (F.hasOneUse())
      inline_budget = std::max(inline_budget, 384u);
    else if (F.getNumUses() <= 2)
      inline_budget = std::max(inline_budget, 192u);

  } else if (enableClosedSliceContinuationDiscovery()) {
    // The experimental continuation discovery path exposes a few larger
    // lifted blk_* continuations before ABI recovery. Inline single-caller
    // continuations earlier so ABI recovery sees a flatter closed slice.
    if (F.hasOneUse())
      inline_budget = std::max(inline_budget, 192u);
    else if (F.getNumUses() <= 2)
      inline_budget = std::max(inline_budget, 96u);
  }
  if (!native_helper && isNoABIModeModule(*F.getParent())) {
    loopifyClosedSliceSelfRecursiveBlockHelper(F, debug_inline);
    // No-ABI readability mode can keep one remaining internal blk_* call
    // solely due conservative inline budgeting. Allow a larger budget for
    // single-use closed-slice helpers in this mode.
    if (F.hasOneUse())
      inline_budget = std::max(inline_budget, 512u);
    else if (F.getNumUses() <= 2)
      inline_budget = std::max(inline_budget, 256u);
  }
  const unsigned inst_count = countNonDebugInstructions(F);
  if (inst_count > inline_budget) {
    if (debug_inline) {
      llvm::errs() << "[closed-slice-inline] skip " << F.getName()
                   << " native=" << native_helper
                   << " reason=budget insts=" << inst_count
                   << " budget=" << inline_budget
                   << " uses=" << F.getNumUses() << "\n";
    }
    return false;
  }
  debug_mark(inline_budget, inst_count);

  bool changed = false;
  if (F.hasFnAttribute(llvm::Attribute::OptimizeNone)) {
    F.removeFnAttr(llvm::Attribute::OptimizeNone);
    changed = true;
  }
  if (F.hasFnAttribute(llvm::Attribute::NoInline)) {
    F.removeFnAttr(llvm::Attribute::NoInline);
    changed = true;
  }
  if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
    F.addFnAttr(llvm::Attribute::AlwaysInline);
    changed = true;
  }
  if (!F.hasLocalLinkage()) {
    F.setLinkage(llvm::GlobalValue::InternalLinkage);
    changed = true;
  }
  return changed;
}

bool maybeMarkClosedRootSliceSemanticHelperForInlining(llvm::Function &F,
                                                       unsigned max_inst_count) {
  if (F.isDeclaration() || !F.hasLocalLinkage())
    return false;

  auto name = F.getName();
  if (name.starts_with("sub_") || isSyntheticBlockLikeFunctionName(name) ||
      name.starts_with("__remill_") || name.starts_with("__omill_") ||
      name.ends_with("_native")) {
    return false;
  }
  if (!F.getMetadata("remill.function.type"))
    return false;
  if (countNonDebugInstructions(F) > max_inst_count)
    return false;

  bool has_direct_caller = false;
  for (auto *U : F.users()) {
    auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
    if (!CB || CB->getCalledFunction() != &F)
      return false;
    has_direct_caller = true;
  }
  if (!has_direct_caller)
    return false;

  bool changed = false;
  if (F.hasFnAttribute(llvm::Attribute::OptimizeNone)) {
    F.removeFnAttr(llvm::Attribute::OptimizeNone);
    changed = true;
  }
  if (F.hasFnAttribute(llvm::Attribute::NoInline)) {
    F.removeFnAttr(llvm::Attribute::NoInline);
    changed = true;
  }
  if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
    F.addFnAttr(llvm::Attribute::AlwaysInline);
    changed = true;
  }

  return changed;
}

bool neutralizeInlinedFunctionReturns(llvm::Function &F) {
  if (F.isDeclaration())
    return false;

  llvm::SmallVector<llvm::CallInst *, 4> to_neutralize;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee || callee->getName() != "__remill_function_return")
        continue;

      auto *term = BB.getTerminator();
      if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(term)) {
        if (RI->getReturnValue() == CI)
          continue;
      }

      to_neutralize.push_back(CI);
    }
  }

  for (auto *CI : to_neutralize) {
    llvm::Value *mem = CI->getArgOperand(2);
    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();
  }

  return !to_neutralize.empty();
}

std::optional<uint64_t> parseSyntheticBlockLikePC(llvm::StringRef name) {
  if (name.starts_with("blk_")) {
    uint64_t pc = 0;
    if (!name.drop_front(4).getAsInteger(16, pc))
      return pc;
    return std::nullopt;
  }
  if (name.starts_with("block_")) {
    uint64_t pc = extractBlockPC(name);
    if (pc != 0)
      return pc;
  }
  return std::nullopt;
}

bool markClosedRootSliceContinuationFunction(llvm::Function &F) {
  bool changed = false;
  if (!F.hasFnAttribute("omill.closed_root_slice")) {
    F.addFnAttr("omill.closed_root_slice", "1");
    changed = true;
  }
  if (!F.hasLocalLinkage()) {
    F.setLinkage(llvm::GlobalValue::InternalLinkage);
    changed = true;
  }
  return changed;
}

llvm::Function *findSyntheticBlockLikeDefinition(llvm::Module &M, uint64_t pc) {
  auto blk_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *F = M.getFunction(blk_name); F && !F->isDeclaration())
    return F;

  auto block_name =
      (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *F = M.getFunction(block_name); F && !F->isDeclaration())
    return F;

  auto sub_name = (llvm::Twine("sub_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *F = M.getFunction(sub_name); F && !F->isDeclaration())
    return F;

  return nullptr;
}

llvm::Function *lookupDefinedLiftedOrBlockTarget(llvm::Module &M, uint64_t pc) {
  auto blk_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *F = M.getFunction(blk_name); F && !F->isDeclaration())
    return F;

  auto block_name =
      (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *F = M.getFunction(block_name); F && !F->isDeclaration())
    return F;

  auto sub_name = (llvm::Twine("sub_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *F = M.getFunction(sub_name); F && !F->isDeclaration())
    return F;

  return nullptr;
}

llvm::Function *findNearestSyntheticBlockLikeOwner(llvm::Module &M,
                                                   uint64_t target_pc,
                                                   uint64_t max_distance,
                                                   uint64_t *resolved_pc =
                                                       nullptr) {
  if (!target_pc)
    return nullptr;

  llvm::Function *best = nullptr;
  uint64_t best_pc = 0;
  uint64_t best_distance = std::numeric_limits<uint64_t>::max();

  auto consider = [&](llvm::Function &F, uint64_t candidate_pc) {
    if (candidate_pc == 0 || candidate_pc > target_pc)
      return;
    const uint64_t distance = target_pc - candidate_pc;
    if (distance == 0 || distance > max_distance)
      return;
    if (!best || distance < best_distance ||
        (distance == best_distance && candidate_pc > best_pc)) {
      best = &F;
      best_pc = candidate_pc;
      best_distance = distance;
    }
  };

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (auto pc = parseSyntheticBlockLikePC(F.getName()))
      consider(F, *pc);
  }

  if (best && resolved_pc)
    *resolved_pc = best_pc;
  return best;
}

uint64_t nearbyLiftedOrBlockTargetSearchWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 4;
    case TargetArch::kX86_64:
    default:
      return 128;
  }
}

llvm::Function *findNearestDefinedLiftedOrBlockTarget(llvm::Module &M,
                                                      uint64_t target_pc,
                                                      uint64_t *resolved_pc =
                                                          nullptr) {
  if (!target_pc)
    return nullptr;

  const uint64_t window =
      nearbyLiftedOrBlockTargetSearchWindow(targetArchForModule(M));
  if (auto *synthetic_owner =
          findNearestSyntheticBlockLikeOwner(M, target_pc, window,
                                             resolved_pc)) {
    return synthetic_owner;
  }
  auto nearest_pc = findNearestCoveredLiftedOrBlockPC(M, target_pc, window);
  if (!nearest_pc || *nearest_pc == target_pc)
    return nullptr;

  auto *best = findLiftedOrCoveredFunctionByPC(M, *nearest_pc);
  if (best && resolved_pc)
    *resolved_pc = *nearest_pc;
  return best;
}

llvm::Function *findExactOrNearbyDefinedLiftedOrBlockTarget(
    llvm::Module &M, uint64_t target_pc, uint64_t *resolved_pc = nullptr) {
  if (auto *exact = findLiftedOrCoveredFunctionByPC(M, target_pc)) {
    if (resolved_pc)
      *resolved_pc = target_pc;
    return exact;
  }
  return findNearestDefinedLiftedOrBlockTarget(M, target_pc, resolved_pc);
}

void collectReachableClosedRootSliceFunctions(
    llvm::Module &M, llvm::SmallVectorImpl<llvm::Function *> &functions) {
  llvm::DenseSet<llvm::Function *> seen;
  auto queue_fn = [&](llvm::Function *F) {
    if (!F || F->isDeclaration())
      return;
    if (!seen.insert(F).second)
      return;
    functions.push_back(F);
  };
  auto queue_structural_targets = [&]() {
    auto summary = collectOutputRootClosureTargets(
        M,
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(M, target) != nullptr;
        },
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(M, target) != nullptr;
        },
        [&](uint64_t target) { return target; },
        /*include_defined_targets=*/true);
    auto queue_targets = [&](const std::vector<uint64_t> &targets) {
      for (uint64_t target : targets)
        queue_fn(lookupDefinedLiftedOrBlockTarget(M, target));
    };
    queue_targets(summary.constant_code_targets);
    queue_targets(summary.constant_calli_targets);
    queue_targets(summary.constant_dispatch_targets);
    queue_targets(summary.annotated_vm_continuation_targets);
  };

  for (auto &F : M) {
    if (isClosedRootSliceFunction(F))
      queue_fn(&F);
  }
  queue_structural_targets();

  for (size_t i = 0; i < functions.size(); ++i) {
    auto *F = functions[i];
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->isDeclaration())
          continue;
        queue_fn(callee);
      }
    }
  }
}

void collectReachableClosedRootSliceCodeFunctionsFromRoots(
    llvm::Module &M, llvm::SmallVectorImpl<llvm::Function *> &functions) {
  llvm::DenseSet<llvm::Function *> seen;
  llvm::DenseSet<llvm::Function *> recorded;
  llvm::SmallVector<llvm::Function *, 16> traversal_queue;
  auto enqueue_traversal = [&](llvm::Function *F) {
    if (!F || F->isDeclaration())
      return;
    if (!seen.insert(F).second)
      return;
    traversal_queue.push_back(F);
  };

  auto maybe_record = [&](llvm::Function *F) {
    if (!F || F->isDeclaration() ||
        !isClosedRootSliceCodeBearingFunction(*F) ||
        !recorded.insert(F).second) {
      return;
    }
    functions.push_back(F);
  };

  for (auto &F : M) {
    if (isClosedRootSliceFunction(F))
      maybe_record(&F);
  }
  {
    auto summary = collectOutputRootClosureTargets(
        M,
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(M, target) != nullptr;
        },
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(M, target) != nullptr;
        },
        [&](uint64_t target) { return target; },
        /*include_defined_targets=*/true);
    auto enqueue_targets = [&](const std::vector<uint64_t> &targets) {
      for (uint64_t target : targets)
        enqueue_traversal(lookupDefinedLiftedOrBlockTarget(M, target));
    };
    enqueue_targets(summary.constant_code_targets);
    enqueue_targets(summary.constant_calli_targets);
    enqueue_targets(summary.constant_dispatch_targets);
    enqueue_targets(summary.annotated_vm_continuation_targets);
  }

  for (auto &F : M) {
    if (isClosedRootSliceRoot(F))
      enqueue_traversal(&F);
  }

  if (traversal_queue.empty()) {
    for (auto &F : M) {
      if (isClosedRootSliceFunction(F))
        enqueue_traversal(&F);
    }
  }

  for (size_t i = 0; i < traversal_queue.size(); ++i) {
    auto *F = traversal_queue[i];
    maybe_record(F);
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->isDeclaration())
          continue;
        enqueue_traversal(callee);
      }
    }
  }
}

bool isOutputRootNativeFunction(const llvm::Function &F) {
  if (F.isDeclaration() || !F.getName().ends_with("_native"))
    return false;
  return F.hasFnAttribute("omill.output_root") ||
         hasCorrespondingLiftedOutputRoot(F);
}

bool isOutputRootClosureSeedFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.hasFnAttribute("omill.output_root"))
    return true;
  if (F.hasFnAttribute("omill.internal_output_root"))
    return true;
  return F.getName().starts_with("__omill_internal_output_root_");
}

void collectReachableOutputRootFunctions(
    llvm::Module &M, llvm::SmallVectorImpl<llvm::Function *> &functions) {
  llvm::DenseSet<llvm::Function *> seen;
  auto queue_fn = [&](llvm::Function *F) {
    if (!F || F->isDeclaration())
      return;
    if (!seen.insert(F).second)
      return;
    functions.push_back(F);
  };
  auto queue_structural_targets = [&]() {
    auto summary = collectOutputRootClosureTargets(
        M,
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(M, target) != nullptr;
        },
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(M, target) != nullptr;
        },
        [&](uint64_t target) { return target; },
        /*include_defined_targets=*/true);
    auto queue_targets = [&](const std::vector<uint64_t> &targets) {
      for (uint64_t target : targets)
        queue_fn(lookupDefinedLiftedOrBlockTarget(M, target));
    };
    queue_targets(summary.constant_code_targets);
    queue_targets(summary.constant_calli_targets);
    queue_targets(summary.constant_dispatch_targets);
    queue_targets(summary.annotated_vm_continuation_targets);
  };

  for (auto &F : M)
    if (isOutputRootClosureSeedFunction(F) || isOutputRootNativeFunction(F))
      queue_fn(&F);

  queue_structural_targets();
  if (isLargeNoAbiStateOptimizationScopeModule(M))
    return;

  for (size_t i = 0; i < functions.size(); ++i) {
    auto *F = functions[i];
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->isDeclaration())
          continue;
        queue_fn(callee);
      }
    }
  }
}

bool maybeMarkOutputRootNativeHelperForInlining(
    llvm::Function &F, unsigned max_inst_count,
    const llvm::DenseSet<llvm::Function *> &reachable,
    const VirtualCalleeRegistry *virtual_callees = nullptr) {
  if (F.isDeclaration() || !reachable.contains(&F))
    return false;
  if (!F.getName().ends_with("_native"))
    return false;
  if (isOutputRootNativeFunction(F))
    return false;

  const bool is_block_like =
      isSyntheticBlockLikeNativeHelperName(F.getName());
  const bool is_native_sub_helper =
      isClosedRootSliceNativeSubHelperName(F.getName()) &&
      !F.hasFnAttribute("omill.output_root");
  if (!is_block_like && !is_native_sub_helper)
    return false;
  if (shouldPreserveOutlinedWrapper(F, virtual_callees))
    return false;
  if (is_native_sub_helper && F.getNumUses() > 2)
    return false;

  unsigned inline_budget = max_inst_count;
  if (F.hasOneUse())
    inline_budget = std::max(inline_budget,
                             is_block_like ? 1024u : 384u);
  else if (F.getNumUses() <= 2)
    inline_budget = std::max(inline_budget,
                             is_block_like ? 512u : 192u);
  else if (is_block_like && F.getNumUses() <= 3)
    inline_budget = std::max(inline_budget, 1024u);

  const unsigned inst_count = countNonDebugInstructions(F);
  if (inst_count > inline_budget)
    return false;

  bool changed = false;
  if (F.hasFnAttribute(llvm::Attribute::OptimizeNone)) {
    F.removeFnAttr(llvm::Attribute::OptimizeNone);
    changed = true;
  }
  if (F.hasFnAttribute(llvm::Attribute::NoInline)) {
    F.removeFnAttr(llvm::Attribute::NoInline);
    changed = true;
  }
  if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
    F.addFnAttr(llvm::Attribute::AlwaysInline);
    changed = true;
  }
  if (!F.hasLocalLinkage()) {
    F.setLinkage(llvm::GlobalValue::InternalLinkage);
    changed = true;
  }
  return changed;
}

bool maybeMarkOutputRootSemanticHelperForInlining(
    llvm::Function &F, unsigned max_inst_count,
    const llvm::DenseSet<llvm::Function *> &reachable) {
  if (F.isDeclaration() || !reachable.contains(&F) || !F.hasLocalLinkage())
    return false;

  auto name = F.getName();
  if (name.starts_with("sub_") || isSyntheticBlockLikeFunctionName(name) ||
      name.starts_with("__remill_") || name.starts_with("__omill_") ||
      name.ends_with("_native")) {
    return false;
  }
  if (!F.getMetadata("remill.function.type"))
    return false;
  if (countNonDebugInstructions(F) > max_inst_count)
    return false;

  bool has_direct_caller = false;
  for (auto *U : F.users()) {
    auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
    if (!CB || CB->getCalledFunction() != &F)
      return false;
    if (!reachable.contains(CB->getFunction()))
      continue;
    has_direct_caller = true;
  }
  if (!has_direct_caller)
    return false;

  bool changed = false;
  if (F.hasFnAttribute(llvm::Attribute::OptimizeNone)) {
    F.removeFnAttr(llvm::Attribute::OptimizeNone);
    changed = true;
  }
  if (F.hasFnAttribute(llvm::Attribute::NoInline)) {
    F.removeFnAttr(llvm::Attribute::NoInline);
    changed = true;
  }
  if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
    F.addFnAttr(llvm::Attribute::AlwaysInline);
    changed = true;
  }

  return changed;
}

bool markReachableClosedRootSliceFunctions(llvm::Module &M) {
  llvm::SmallVector<llvm::Function *, 16> reachable;
  collectReachableClosedRootSliceFunctions(M, reachable);

  bool changed = false;
  for (auto *F : reachable) {
    if (!F->hasFnAttribute("omill.closed_root_slice")) {
      F->addFnAttr("omill.closed_root_slice", "1");
      changed = true;
    }
  }
  return changed;
}

bool rebuildClosedRootSliceCodeScope(llvm::Module &M) {
  if (!isClosedRootSliceScopedModule(M))
    return false;

  llvm::SmallVector<llvm::Function *, 16> reachable;
  collectReachableClosedRootSliceCodeFunctionsFromRoots(M, reachable);
  llvm::DenseSet<llvm::Function *> keep(reachable.begin(), reachable.end());

  bool has_root = false;
  for (auto &F : M) {
    if (!isClosedRootSliceRoot(F))
      continue;
    keep.insert(&F);
    has_root = true;
  }

  bool changed = false;
  for (auto &F : M) {
    const bool should_keep = keep.contains(&F);
    if (should_keep) {
      if (!F.hasFnAttribute("omill.closed_root_slice")) {
        F.addFnAttr("omill.closed_root_slice", "1");
        changed = true;
      }
      continue;
    }

    if (F.hasFnAttribute("omill.closed_root_slice")) {
      F.removeFnAttr("omill.closed_root_slice");
      changed = true;
    }
  }

  M.setModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope",
                  static_cast<uint32_t>(has_root ? 1 : 0));
  return changed;
}

bool isOutputRootClosureScopedModule(const llvm::Module &M) {
  auto *flag = M.getModuleFlag("omill.output_root_closure_scope");
  if (!flag)
    return false;
  if (auto *value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(flag))
    return value->getZExtValue() != 0;
  return false;
}

bool rebuildOutputRootClosureCodeScope(llvm::Module &M) {
  constexpr unsigned kLargeLiftedFunctionThreshold = 512;

  unsigned lifted_count = 0;
  for (auto &F : M) {
    if (!isLiftedPipelineFunction(F))
      continue;
    if (++lifted_count >= kLargeLiftedFunctionThreshold)
      break;
  }

  const bool enable_scope =
      isNoABIModeModule(M) && lifted_count >= kLargeLiftedFunctionThreshold;
  llvm::SmallVector<llvm::Function *, 16> reachable;
  llvm::DenseSet<llvm::Function *> keep;
  if (enable_scope) {


    collectReachableOutputRootFunctions(M, reachable);
    keep.insert(reachable.begin(), reachable.end());
  }

  bool changed = false;
  for (auto &F : M) {
    const bool should_keep = enable_scope && keep.contains(&F);
    if (should_keep) {
      if (!F.hasFnAttribute("omill.output_root_closure")) {
        F.addFnAttr("omill.output_root_closure", "1");
        changed = true;
      }
      continue;
    }
    if (F.hasFnAttribute("omill.output_root_closure")) {
      F.removeFnAttr("omill.output_root_closure");
      changed = true;
    }
  }

  const bool was_scoped = isOutputRootClosureScopedModule(M);
  M.setModuleFlag(llvm::Module::Override, "omill.output_root_closure_scope",
                  static_cast<uint32_t>(enable_scope ? 1 : 0));
  return changed || was_scoped != enable_scope;
}

bool isLargeNoAbiGenericStaticScopeModule(const llvm::Module &M) {
  auto *flag = M.getModuleFlag("omill.large_noabi_generic_static_scope");
  if (!flag)
    return false;
  if (auto *value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(flag))
    return value->getZExtValue() != 0;
  return false;
}


bool isLargeNoAbiStateOptimizationScopeModule(const llvm::Module &M) {
  auto *flag = M.getModuleFlag("omill.large_noabi_state_scope");
  if (!flag)
    return false;
  if (auto *value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(flag))
    return value->getZExtValue() != 0;
  return false;
}

bool rebuildLargeNoAbiStateOptimizationScope(llvm::Module &M) {
  constexpr unsigned kLargeLiftedFunctionThreshold = 512;

  unsigned lifted_count = 0;
  for (auto &F : M) {
    if (!isLiftedPipelineFunction(F))
      continue;
    if (++lifted_count >= kLargeLiftedFunctionThreshold)
      break;
  }

  const bool enable_scope =
      isNoABIModeModule(M) && lifted_count >= kLargeLiftedFunctionThreshold;
  const bool was_scoped = isLargeNoAbiStateOptimizationScopeModule(M);
  M.setModuleFlag(llvm::Module::Override, "omill.large_noabi_state_scope",
                  static_cast<uint32_t>(enable_scope ? 1 : 0));
  return was_scoped != enable_scope;
}

unsigned countLiftedPipelineFunctions(const llvm::Module &M) {
  unsigned count = 0;
  for (auto &F : M) {
    if (isLiftedPipelineFunction(F))
      ++count;
  }
  return count;
}


bool isTerminalMissingBlockStub(const llvm::Function &F) {
  const llvm::Function *missing_block = nullptr;
  unsigned direct_calls = 0;

  for (const auto &BB : F) {
    for (const auto &I : BB) {
      const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;
      auto *callee = CB->getCalledFunction();
      if (!callee)
        return false;
      ++direct_calls;
      if (callee->getName() != "__remill_missing_block")
        return false;
      missing_block = callee;
    }
  }

  return missing_block != nullptr && direct_calls == 1;
}

unsigned countClosedRootSliceDeclaredContinuationCalls(llvm::Module &M) {
  unsigned count = 0;
  const bool debug_late_closure =
      (std::getenv("OMILL_DEBUG_LATE_CLOSED_SLICE_CONTINUATION") != nullptr);
  llvm::SmallVector<llvm::Function *, 16> reachable;
  collectReachableClosedRootSliceFunctions(M, reachable);
  for (auto *F : reachable) {
    if (debug_late_closure)
      llvm::errs() << "[late-closure] scan function " << F->getName() << "\n";
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (debug_late_closure) {
          llvm::errs() << "  [late-closure] callee=";
          if (callee) {
            llvm::errs() << callee->getName()
                         << " decl=" << callee->isDeclaration();
          } else {
            llvm::errs() << "<indirect>";
          }
          llvm::errs() << "\n";
        }
        if (!callee || !callee->isDeclaration())
          continue;
        if (parseSyntheticBlockLikePC(callee->getName()))
          ++count;
      }
    }
  }
  return count;
}

bool hasClosedRootSlicePostCleanupMaterializationWork(llvm::Module &M) {
  if (!isClosedRootSliceScopedModule(M))
    return false;
  if (isNoABIModeModule(M))
    return true;
  if (countClosedRootSliceDeclaredContinuationCalls(M) != 0)
    return true;

  llvm::SmallVector<llvm::Function *, 16> reachable;
  collectReachableClosedRootSliceFunctions(M, reachable);
  for (auto *F : reachable) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto callee_name = callee->getName();
        if (isDispatchIntrinsicName(callee_name)) {
          return true;
        }
        if (callee->isDeclaration() &&
            isSyntheticBlockLikeFunctionName(callee_name)) {
          return true;
        }
      }
    }
  }
  return false;
}

void collectClosedRootSliceContinuationPCs(
    llvm::Module &M, llvm::SmallVectorImpl<uint64_t> &pcs) {
  llvm::DenseSet<uint64_t> seen;
  llvm::SmallVector<llvm::Function *, 16> reachable;
  collectReachableClosedRootSliceFunctions(M, reachable);
  for (auto *F : reachable) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || !callee->isDeclaration())
          continue;
        auto maybe_pc = parseSyntheticBlockLikePC(callee->getName());
        if (!maybe_pc)
          continue;
        if (seen.insert(*maybe_pc).second)
          pcs.push_back(*maybe_pc);
      }
    }
  }
}

struct MarkClosedRootSliceHelpersForInliningPass
    : llvm::PassInfoMixin<MarkClosedRootSliceHelpersForInliningPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    if (!isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    bool changed = false;
    for (auto &F : M) {
      changed |= maybeMarkClosedRootSliceHelperForInlining(
          F, /*max_inst_count=*/24, /*native_helper=*/false);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct MarkClosedRootSliceNativeHelpersForInliningPass
    : llvm::PassInfoMixin<MarkClosedRootSliceNativeHelpersForInliningPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    if (!isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    auto &virtual_callees =
        MAM.getResult<VirtualCalleeRegistryAnalysis>(M);
    bool changed = false;
    for (auto &F : M) {
      // Native wrappers grow substantially after ABI recovery. Allow a wider
      // bound here so the closed-slice block wrapper chain still collapses.
      changed |= maybeMarkClosedRootSliceHelperForInlining(
          F, /*max_inst_count=*/96, /*native_helper=*/true,
          &virtual_callees);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct MarkClosedRootSliceSemanticHelpersForInliningPass
    : llvm::PassInfoMixin<MarkClosedRootSliceSemanticHelpersForInliningPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    if (!isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    bool changed = false;
    for (auto &F : M) {
      changed |= maybeMarkClosedRootSliceSemanticHelperForInlining(
          F, /*max_inst_count=*/96);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

/// Aggressively mark every remill instruction-semantics template that is
/// directly called by a lifted block which has not yet been through
/// late-block reintegration. Unlike MarkClosedRootSliceSemanticHelpersForInlining,
/// this pass applies no instruction-count limit: late-lifted blocks contain
/// calls to large templates (CALLI/MOVI vector variants etc.) that the
/// existing 96-instruction cap excludes, leaving them in the final IR.
///
/// Idempotency: only walks lifted functions without
/// `omill.late_block_semantics_marked`. Once a function has been visited,
/// it sets the attribute and is skipped on subsequent invocations.
struct MarkLateBlockReachableSemanticHelpersPass
    : llvm::PassInfoMixin<MarkLateBlockReachableSemanticHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (!isLiftedPipelineFunction(F))
        continue;
      if (F.hasFnAttribute("omill.late_block_semantics_marked"))
        continue;

      bool any_marked_here = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->isDeclaration())
            continue;
          // Only consider remill-shaped semantic templates: they have
          // remill.function.type metadata and are not lifted/intrinsic
          // helpers themselves.
          auto name = callee->getName();
          if (name.starts_with("sub_") ||
              isSyntheticBlockLikeFunctionName(name) ||
              name.starts_with("__remill_") ||
              name.starts_with("__omill_") ||
              name.ends_with("_native")) {
            continue;
          }
          if (!callee->getMetadata("remill.function.type"))
            continue;
          if (callee->hasFnAttribute(llvm::Attribute::AlwaysInline))
            continue;
          if (callee->hasFnAttribute(llvm::Attribute::OptimizeNone)) {
            callee->removeFnAttr(llvm::Attribute::OptimizeNone);
            changed = true;
          }
          if (callee->hasFnAttribute(llvm::Attribute::NoInline)) {
            callee->removeFnAttr(llvm::Attribute::NoInline);
            changed = true;
          }
          callee->addFnAttr(llvm::Attribute::AlwaysInline);
          changed = true;
          any_marked_here = true;
        }
      }
      // Tag the function so we don't re-walk it on subsequent cleanup
      // invocations. Even if we found nothing, walking this function once
      // is enough — its body shape is stable until a new lift adds
      // new callsites, and a new lift will clear the attr by replacing F.
      F.addFnAttr("omill.late_block_semantics_marked");
      (void)any_marked_here;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct UnprotectReachableClosedRootSliceHelpersPass
    : llvm::PassInfoMixin<UnprotectReachableClosedRootSliceHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    if (!isClosedRootSliceScopedModule(M) || !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    llvm::SmallVector<llvm::Function *, 16> reachable;
    collectReachableClosedRootSliceFunctions(M, reachable);

    bool changed = false;
    for (auto *F : reachable) {
      if (!F || F->isDeclaration() || !isClosedRootSliceFunction(*F) ||
          isClosedRootSliceRoot(*F)) {
        continue;
      }

      auto name = F->getName();
      if (!isSyntheticBlockLikeFunctionName(name) &&
          !isSyntheticBlockLikeNativeHelperName(name)) {
        continue;
      }

      if (F->hasFnAttribute(llvm::Attribute::OptimizeNone)) {
        F->removeFnAttr(llvm::Attribute::OptimizeNone);
        changed = true;
      }
      if (F->hasFnAttribute(llvm::Attribute::NoInline)) {
        F->removeFnAttr(llvm::Attribute::NoInline);
        changed = true;
      }
      if (!F->hasLocalLinkage() && !F->hasFnAttribute("omill.output_root")) {
        F->setLinkage(llvm::GlobalValue::InternalLinkage);
        changed = true;
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct SanitizeModeledBoundaryPoisonMemoryArgsPass
    : llvm::PassInfoMixin<SanitizeModeledBoundaryPoisonMemoryArgsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;

    for (auto &F : M) {
      if (F.isDeclaration() || F.arg_size() < 3)
        continue;

      auto *memory_arg = F.getArg(2);
      if (!memory_arg || !memory_arg->getType()->isPointerTy())
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (!callee || CB->arg_size() < 3 ||
              !isModeledStructuralBoundaryTarget(*callee)) {
            continue;
          }

          auto *old_memory_arg = CB->getArgOperand(2);
          if (!llvm::isa<llvm::PoisonValue>(old_memory_arg) &&
              !llvm::isa<llvm::UndefValue>(old_memory_arg)) {
            continue;
          }

          llvm::IRBuilder<> B(CB);
          auto name = (callee->getName() + ".memoryfix").str();
          auto *replacement = coerceValueToType(
              B, memory_arg, old_memory_arg->getType(), name);
          if (!replacement)
            continue;

          CB->setArgOperand(2, replacement);
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct MarkOutputRootNativeHelpersForInliningPass
    : llvm::PassInfoMixin<MarkOutputRootNativeHelpersForInliningPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    if (isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    llvm::SmallVector<llvm::Function *, 16> reachable_list;
    collectReachableOutputRootFunctions(M, reachable_list);
    if (reachable_list.empty())
      return llvm::PreservedAnalyses::all();

    llvm::DenseSet<llvm::Function *> reachable(reachable_list.begin(),
                                               reachable_list.end());
    auto &virtual_callees =
        MAM.getResult<VirtualCalleeRegistryAnalysis>(M);
    bool changed = false;
    for (auto &F : M) {
      changed |= maybeMarkOutputRootNativeHelperForInlining(
          F, /*max_inst_count=*/96, reachable, &virtual_callees);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct MarkOutputRootSemanticHelpersForInliningPass
    : llvm::PassInfoMixin<MarkOutputRootSemanticHelpersForInliningPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    if (isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    llvm::SmallVector<llvm::Function *, 16> reachable_list;
    collectReachableOutputRootFunctions(M, reachable_list);
    if (reachable_list.empty())
      return llvm::PreservedAnalyses::all();

    llvm::DenseSet<llvm::Function *> reachable(reachable_list.begin(),
                                               reachable_list.end());
    bool changed = false;
    for (auto &F : M) {
      changed |= maybeMarkOutputRootSemanticHelperForInlining(
          F, /*max_inst_count=*/96, reachable);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct NeutralizeInlinedFunctionReturnsPass
    : llvm::PassInfoMixin<NeutralizeInlinedFunctionReturnsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M)
      changed |= neutralizeInlinedFunctionReturns(F);
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct RelaxClosedSliceMustTailMissingBlockPass
    : llvm::PassInfoMixin<RelaxClosedSliceMustTailMissingBlockPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    if (!isClosedRootSliceScopedModule(M) || !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration() || !isClosedRootSliceFunction(F) ||
          !isSyntheticBlockLikeFunctionName(F.getName())) {
        continue;
      }

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call || !call->isMustTailCall())
            continue;

          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;

          call->setTailCallKind(llvm::CallInst::TCK_Tail);
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

static bool isEntryAllocaBackedInteger(const llvm::Value *V,
                                       const llvm::Function &F,
                                       unsigned depth);

static bool isEntryAllocaBackedPointer(const llvm::Value *V,
                                       const llvm::Function &F,
                                       unsigned depth = 0) {
  if (!V || depth > 8)
    return false;
  auto *stripped = V->stripPointerCasts();
  auto *obj = llvm::getUnderlyingObject(stripped);
  auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(obj);
  if (alloca && alloca->getFunction() == &F &&
      alloca->getParent() == &F.getEntryBlock()) {
    return true;
  }

  if (auto *gep = llvm::dyn_cast<llvm::GEPOperator>(stripped))
    return isEntryAllocaBackedPointer(gep->getPointerOperand(), F, depth + 1);

  if (auto *i2p = llvm::dyn_cast<llvm::Operator>(stripped);
      i2p && i2p->getOpcode() == llvm::Instruction::IntToPtr) {
    return isEntryAllocaBackedInteger(i2p->getOperand(0), F, depth + 1);
  }

  return false;
}

static bool isEntryAllocaBackedInteger(const llvm::Value *V,
                                       const llvm::Function &F,
                                       unsigned depth) {
  if (!V || depth > 8)
    return false;
  auto *stripped = V->stripPointerCasts();

  if (auto *p2i = llvm::dyn_cast<llvm::Operator>(stripped);
      p2i && p2i->getOpcode() == llvm::Instruction::PtrToInt) {
    return isEntryAllocaBackedPointer(p2i->getOperand(0), F, depth + 1);
  }

  auto recurse_binop = [&](const llvm::Value *lhs, const llvm::Value *rhs) {
    return isEntryAllocaBackedInteger(lhs, F, depth + 1) ||
           isEntryAllocaBackedInteger(rhs, F, depth + 1);
  };

  if (auto *op = llvm::dyn_cast<llvm::Operator>(stripped)) {
    switch (op->getOpcode()) {
      case llvm::Instruction::Add:
      case llvm::Instruction::Sub:
      case llvm::Instruction::Or:
        return recurse_binop(op->getOperand(0), op->getOperand(1));
      default:
        break;
    }
  }

  return false;
}

static bool isLoopifiableRecursiveTailSuffixInst(const llvm::Instruction &I,
                                                 const llvm::Function &F) {
  if (llvm::isa<llvm::DbgInfoIntrinsic>(I) || llvm::isa<llvm::FreezeInst>(I))
    return true;

  if (auto *call = llvm::dyn_cast<llvm::CallBase>(&I)) {
    auto *asm_target = llvm::dyn_cast<llvm::InlineAsm>(
        call->getCalledOperand()->stripPointerCasts());
    if (asm_target && call->use_empty() &&
        asm_target->getAsmString().trim() == "int3") {
      return true;
    }
  }

  if (auto *intr = llvm::dyn_cast<llvm::IntrinsicInst>(&I)) {
    switch (intr->getIntrinsicID()) {
      case llvm::Intrinsic::lifetime_end:
      case llvm::Intrinsic::lifetime_start:
        return isEntryAllocaBackedPointer(intr->getArgOperand(1), F);
      default:
        return false;
    }
  }

  if (auto *load = llvm::dyn_cast<llvm::LoadInst>(&I))
    return isEntryAllocaBackedPointer(load->getPointerOperand(), F);

  if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I))
    return isEntryAllocaBackedPointer(store->getPointerOperand(), F);

  if (I.use_empty() && !I.mayHaveSideEffects() &&
      !I.isTerminator() && !llvm::isa<llvm::PHINode>(I))
    return true;

  return false;
}

static bool computeStableSelfRecursivePC(
    llvm::Function &F, llvm::ArrayRef<llvm::CallInst *> recursive_calls,
    llvm::ConstantInt *&stable_pc) {
  stable_pc = nullptr;

  for (auto *call : recursive_calls) {
    auto *pc_arg = call->getArgOperand(1);
    if (pc_arg == F.getArg(1)) {
      continue;
    }

    auto *pc_const = llvm::dyn_cast<llvm::ConstantInt>(pc_arg);
    if (!pc_const)
      return false;
    if (!stable_pc) {
      stable_pc = pc_const;
    } else if (stable_pc->getValue() != pc_const->getValue()) {
      return false;
    }
  }

  if (!stable_pc)
    return true;

  for (auto *user : F.users()) {
    auto *call = llvm::dyn_cast<llvm::CallBase>(user);
    if (!call || call->getCalledOperand()->stripPointerCasts() != &F)
      return false;

    if (call->getFunction() == &F)
      continue;

    auto *pc_const = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
    if (!pc_const || pc_const->getValue() != stable_pc->getValue())
      return false;
  }

  return true;
}

static llvm::BasicBlock *getOrCreateLoopHeaderAfterAllocas(llvm::Function &F) {
  auto &entry = F.getEntryBlock();
  auto split_it = entry.getFirstNonPHIOrDbgOrAlloca();
  auto *split_pt = split_it == entry.end() ? nullptr : &*split_it;
  if (!split_pt)
    return nullptr;

  if (auto *br = llvm::dyn_cast<llvm::BranchInst>(entry.getTerminator());
      br && br->isUnconditional() && split_pt == entry.getTerminator()) {
    return br->getSuccessor(0);
  }

  if (split_pt == entry.getTerminator())
    return nullptr;

  return llvm::SplitBlock(&entry, split_pt,
                          static_cast<llvm::DominatorTree *>(nullptr),
                          nullptr, nullptr, "selfrec.loop");
}

static bool loopifyClosedSliceSelfRecursiveBlockHelper(llvm::Function &F,
                                                       bool debug) {
  if (F.isDeclaration() || !isClosedRootSliceFunction(F) ||
      !isSyntheticBlockLikeFunctionName(F.getName())) {
    return false;
  }

  llvm::SmallVector<llvm::CallInst *, 4> recursive_calls;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (call && call->getCalledFunction() == &F)
        recursive_calls.push_back(call);
    }
  }
  if (recursive_calls.empty())
    return false;

  llvm::ConstantInt *stable_pc = nullptr;
  if (!computeStableSelfRecursivePC(F, recursive_calls, stable_pc)) {
    if (debug)
      llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                   << " reason=unstable-pc\n";
    return false;
  }

  llvm::SmallVector<llvm::CallInst *, 4> loopifiable_calls;
  bool rejected = false;
  for (auto *call : recursive_calls) {
    if (call->arg_size() < 3) {
      rejected = true;
      if (debug)
        llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                     << " reason=short-args\n";
      break;
    }
    if (call->getArgOperand(0) != F.getArg(0) ||
        call->getArgOperand(2) != F.getArg(2)) {
      rejected = true;
      if (debug)
        llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                     << " reason=arg-mismatch\n";
      break;
    }

    auto *pc_arg = call->getArgOperand(1);
    if (pc_arg != F.getArg(1)) {
      auto *pc_const = llvm::dyn_cast<llvm::ConstantInt>(pc_arg);
      if (!pc_const || !stable_pc ||
          pc_const->getValue() != stable_pc->getValue()) {
        rejected = true;
        if (debug)
          llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                       << " reason=pc-mismatch\n";
        break;
      }
    }

    auto *term = call->getParent()->getTerminator();
    auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
    auto *ret = llvm::dyn_cast<llvm::ReturnInst>(term);
    const bool is_uncond_branch_tail = br && br->isUnconditional();
    const bool is_direct_return_tail =
        ret && (!ret->getReturnValue() || ret->getReturnValue() == call);
    if (!is_uncond_branch_tail && !is_direct_return_tail) {
      rejected = true;
      if (debug)
        llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                     << " reason=non-tail-branch-or-return\n";
      break;
    }

    bool safe_suffix = true;
    for (auto *I = call->getNextNode(); I; I = I->getNextNode()) {
      if (I == term)
        break;
      if (!isLoopifiableRecursiveTailSuffixInst(*I, F)) {
        safe_suffix = false;
        if (debug)
          llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                       << " reason=unsafe-suffix inst=" << I->getOpcodeName()
                       << "\n";
        break;
      }
    }
    if (!safe_suffix)
      break;

    loopifiable_calls.push_back(call);
  }

  if (loopifiable_calls.size() != recursive_calls.size()) {
    if (debug && !rejected)
      llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                   << " reason=partial-match\n";
    return false;
  }

  auto *loop_header = getOrCreateLoopHeaderAfterAllocas(F);
  if (!loop_header) {
    if (debug)
      llvm::errs() << "[selfrec-loopify] skip " << F.getName()
                   << " reason=no-loop-header\n";
    return false;
  }

  bool changed = false;
  for (auto *call : loopifiable_calls) {
    auto *BB = call->getParent();
    auto *old_term = BB->getTerminator();
    if (auto *old_br = llvm::dyn_cast<llvm::BranchInst>(old_term)) {
      auto *succ = old_br->getSuccessor(0);
      succ->removePredecessor(BB);
    }

    llvm::SmallVector<llvm::Instruction *, 16> erase_list;
    for (auto it = llvm::BasicBlock::iterator(call), end = BB->end();
         it != end; ++it) {
      erase_list.push_back(&*it);
    }

    for (auto it = erase_list.rbegin(); it != erase_list.rend(); ++it)
      (*it)->eraseFromParent();

    llvm::IRBuilder<> B(BB);
    B.CreateBr(loop_header);
    changed = true;
  }

  if (!changed)
    return false;

  llvm::removeUnreachableBlocks(F);
  if (debug)
    llvm::errs() << "[selfrec-loopify] transformed " << F.getName()
                 << " recursive_sites=" << loopifiable_calls.size() << "\n";
  if (envEnabled("OMILL_DEBUG_SELFREC_LOOPIFY_DUMP"))
    F.print(llvm::errs());
  return true;
}

static bool isLoopifiableNativeRecursiveTailSuffixInst(
    const llvm::Instruction &I, const llvm::CallInst &call,
    const llvm::Function &F) {
  if (auto *ev = llvm::dyn_cast<llvm::ExtractValueInst>(&I))
    return ev->getAggregateOperand() == &call;

  return isLoopifiableRecursiveTailSuffixInst(I, F);
}

static bool isTerminalSyntheticMemoryArgValue(llvm::Value *V) {
  auto *C = llvm::dyn_cast<llvm::Constant>(V);
  if (!C)
    return false;
  return C->isNullValue() || llvm::isa<llvm::PoisonValue>(C) ||
         llvm::isa<llvm::UndefValue>(C);
}

struct SingleCallerCommonContinuationNativeHelperShape {
  llvm::Function *caller = nullptr;
  llvm::BasicBlock *continuation = nullptr;
  llvm::SmallVector<llvm::CallInst *, 16> callsites;
};

static bool matchSingleCallerCommonContinuationNativeHelperShape(
    llvm::Function &helper,
    SingleCallerCommonContinuationNativeHelperShape &shape,
    bool debug = false) {
  auto debug_skip = [&](llvm::StringRef reason) {
    if (!debug)
      return;
    llvm::errs() << "[native-common-cont] skip " << helper.getName()
                 << " reason=" << reason << "\n";
  };
  if (helper.isDeclaration() || !helper.hasLocalLinkage() ||
      !helper.getName().ends_with("_native") ||
      !isSyntheticBlockLikeNativeHelperName(helper.getName()) ||
      helper.hasFnAttribute("omill.output_root")) {
    debug_skip("helper-shape");
    return false;
  }

  llvm::DenseSet<llvm::Function *> callers;
  for (auto *U : helper.users()) {
    auto *call = llvm::dyn_cast<llvm::CallInst>(U);
    if (!call || call->getCalledFunction() != &helper) {
      debug_skip("non-direct-call-user");
      return false;
    }
    callers.insert(call->getFunction());
  }
  if (callers.size() != 1) {
    debug_skip("not-single-caller");
    return false;
  }

  shape.caller = *callers.begin();
  if (!shape.caller || shape.caller == &helper) {
    debug_skip("invalid-caller");
    return false;
  }

  llvm::BasicBlock *continuation = nullptr;
  for (auto *U : helper.users()) {
    auto *call = llvm::dyn_cast<llvm::CallInst>(U);
    if (!call || call->getFunction() != shape.caller) {
      debug_skip("callsite-caller-mismatch");
      return false;
    }

    auto *term = call->getParent()->getTerminator();
    auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
    if (!br || !br->isUnconditional()) {
      debug_skip("callsite-no-common-branch");
      return false;
    }

    auto *succ = br->getSuccessor(0);
    if (!continuation)
      continuation = succ;
    else if (continuation != succ) {
      debug_skip("different-continuations");
      return false;
    }

    shape.callsites.push_back(call);
  }

  if (!continuation || shape.callsites.empty()) {
    debug_skip("missing-continuation");
    return false;
  }

  shape.continuation = continuation;
  return true;
}

struct ForceInlineSingleCallerCommonContinuationNativeHelpersPass
    : llvm::PassInfoMixin<
          ForceInlineSingleCallerCommonContinuationNativeHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    if (isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    const bool debug = envEnabled("OMILL_DEBUG_SELFREC_LOOPIFY");
    bool changed = false;
    constexpr unsigned kMaxCallSites = 32;
    constexpr unsigned kMaxInstructionCount = 8192;

    for (auto &F : M) {
      SingleCallerCommonContinuationNativeHelperShape shape;
      if (!matchSingleCallerCommonContinuationNativeHelperShape(F, shape, debug))
        continue;
      if (!shape.caller || !isOutputRootNativeFunction(*shape.caller))
        continue;

      const unsigned inst_count = countNonDebugInstructions(F);
      if (shape.callsites.size() > kMaxCallSites ||
          inst_count > kMaxInstructionCount) {
        if (debug) {
          llvm::errs() << "[native-common-cont] skip " << F.getName()
                       << " reason=budget callsites=" << shape.callsites.size()
                       << " insts=" << inst_count << "\n";
        }
        continue;
      }

      bool local_change = false;
      if (F.hasFnAttribute(llvm::Attribute::OptimizeNone)) {
        F.removeFnAttr(llvm::Attribute::OptimizeNone);
        local_change = true;
      }
      if (F.hasFnAttribute(llvm::Attribute::NoInline)) {
        F.removeFnAttr(llvm::Attribute::NoInline);
        local_change = true;
      }
      if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
        F.addFnAttr(llvm::Attribute::AlwaysInline);
        local_change = true;
      }
      if (!F.hasLocalLinkage()) {
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
        local_change = true;
      }

      if (local_change && debug) {
        llvm::errs() << "[native-common-cont] force-inline " << F.getName()
                     << " caller=" << shape.caller->getName()
                     << " callsites=" << shape.callsites.size()
                     << " insts=" << inst_count << "\n";
      }
      changed |= local_change;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

static bool isCanonicalizableMutualNativeHelperName(llvm::StringRef name) {
  if (!name.ends_with("_native"))
    return false;
  return isSyntheticBlockLikeFunctionName(name) || name.starts_with("sub_");
}

static bool isCanonicalizableMutualNativeBlockHelper(
    const llvm::Function &F) {
  return !F.isDeclaration() &&
         !F.hasFnAttribute("omill.output_root") &&
         isCanonicalizableMutualNativeHelperName(F.getName());
}

static void collectDirectCanonicalizableMutualNativeCallees(
    llvm::Function &F, llvm::SmallPtrSetImpl<llvm::Function *> &callees) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->isDeclaration() ||
          !isCanonicalizableMutualNativeHelperName(callee->getName())) {
        continue;
      }
      callees.insert(callee);
    }
  }
}

static llvm::Function *getSingleSyntheticBlockLikeNativePeerCallee(
    llvm::Function &F) {
  llvm::SmallPtrSet<llvm::Function *, 4> callees;
  collectDirectCanonicalizableMutualNativeCallees(F, callees);
  llvm::Function *peer = nullptr;
  for (auto *callee : callees) {
    if (callee == &F)
      continue;
    if (peer && peer != callee)
      return nullptr;
    peer = callee;
  }
  return peer;
}

static bool hasOnlySelfAndPeerSyntheticBlockLikeNativeCallees(
    llvm::Function &F, llvm::Function &peer) {
  llvm::SmallPtrSet<llvm::Function *, 4> callees;
  collectDirectCanonicalizableMutualNativeCallees(F, callees);
  if (!callees.contains(&peer))
    return false;
  for (auto *callee : callees) {
    if (callee != &F && callee != &peer)
      return false;
  }
  return true;
}

static bool collectTailLikeCallsToCallee(
    llvm::Function &caller, llvm::Function &callee,
    llvm::SmallVectorImpl<llvm::CallInst *> &calls, bool debug = false) {
  for (auto &BB : caller) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call || call->getCalledFunction() != &callee)
        continue;

      auto *term = call->getParent()->getTerminator();
      auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
      if (!br || !br->isUnconditional()) {
        if (debug)
          llvm::errs() << "[native-mutrec-loopify] skip " << caller.getName()
                       << "->" << callee.getName()
                       << " reason=non-uncond-tail\n";
        return false;
      }

      bool safe_suffix = true;
      for (auto *next = call->getNextNode(); next; next = next->getNextNode()) {
        if (next == term)
          break;
        if (!isLoopifiableNativeRecursiveTailSuffixInst(*next, *call, caller)) {
          safe_suffix = false;
          if (debug)
            llvm::errs() << "[native-mutrec-loopify] skip " << caller.getName()
                         << "->" << callee.getName()
                         << " reason=unsafe-suffix inst="
                         << next->getOpcodeName() << "\n";
          break;
        }
      }
      if (!safe_suffix)
        return false;

      auto *successor = br->getSuccessor(0);
      for (auto *U : call->users()) {
        auto *user_inst = llvm::dyn_cast<llvm::Instruction>(U);
        auto *ev = llvm::dyn_cast<llvm::ExtractValueInst>(U);
        auto *phi = llvm::dyn_cast<llvm::PHINode>(U);
        const bool same_block_extract =
            user_inst && ev && user_inst->getParent() == call->getParent();
        const bool successor_phi =
            phi && phi->getParent() == successor &&
            phi->getBasicBlockIndex(call->getParent()) >= 0 &&
            phi->getIncomingValueForBlock(call->getParent()) == call;
        if (!same_block_extract && !successor_phi) {
          if (debug)
            llvm::errs() << "[native-mutrec-loopify] skip " << caller.getName()
                         << "->" << callee.getName()
                         << " reason=unsupported-call-user\n";
          return false;
        }
      }

      calls.push_back(call);
    }
  }

  return !calls.empty();
}

static llvm::Function *canonicalizeMutualRecursiveNativeBlockHelperPair(
    llvm::Function &A, llvm::Function &B, bool debug = false) {
  if (A.getCallingConv() != B.getCallingConv())
    return nullptr;
  if (A.isVarArg() || B.isVarArg())
    return nullptr;
  if (A.getReturnType() != B.getReturnType())
    return nullptr;

  const unsigned max_args = std::max(A.arg_size(), B.arg_size());
  llvm::SmallVector<llvm::Type *, 8> union_arg_types;
  union_arg_types.reserve(max_args);
  for (unsigned i = 0; i < max_args; ++i) {
    llvm::Type *ty = nullptr;
    if (i < A.arg_size())
      ty = A.getArg(i)->getType();
    if (i < B.arg_size()) {
      if (!ty)
        ty = B.getArg(i)->getType();
      else if (ty != B.getArg(i)->getType())
        return nullptr;
    }
    if (!ty)
      return nullptr;
    union_arg_types.push_back(ty);
  }

  auto &M = *A.getParent();
  auto &Ctx = M.getContext();
  llvm::SmallVector<llvm::Type *, 8> dispatcher_arg_types;
  dispatcher_arg_types.push_back(llvm::Type::getInt1Ty(Ctx));
  dispatcher_arg_types.append(union_arg_types.begin(), union_arg_types.end());

  llvm::StringRef a_name = A.getName();
  llvm::StringRef a_base =
      a_name.ends_with("_native") ? a_name.drop_back(7) : a_name;
  std::string merged_name = (a_base + "_pair_native").str();
  while (M.getFunction(merged_name))
    merged_name += "_m";

  auto *dispatcher = llvm::Function::Create(
      llvm::FunctionType::get(A.getReturnType(), dispatcher_arg_types, false),
      llvm::GlobalValue::InternalLinkage, merged_name, M);
  dispatcher->setCallingConv(A.getCallingConv());
  dispatcher->setVisibility(A.getVisibility());
  dispatcher->setUnnamedAddr(A.getUnnamedAddr());
  dispatcher->setDSOLocal(true);
  if (A.hasFnAttribute("omill.closed_root_slice") ||
      B.hasFnAttribute("omill.closed_root_slice")) {
    dispatcher->addFnAttr("omill.closed_root_slice", "1");
  }
  dispatcher->addFnAttr(llvm::Attribute::NoInline);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", dispatcher);
  auto *dispatch_entry =
      llvm::BasicBlock::Create(Ctx, "dispatch.entry", dispatcher);

  auto clone_into_dispatcher = [&](llvm::Function &Src, bool dispatch_to_b)
      -> llvm::BasicBlock * {
    llvm::ValueToValueMapTy vmap;
    for (unsigned i = 0; i < Src.arg_size(); ++i)
      vmap[Src.getArg(i)] = dispatcher->getArg(i + 1);

    llvm::SmallVector<llvm::BasicBlock *, 32> cloned_blocks;
    cloned_blocks.reserve(Src.size());
    for (auto &BB : Src) {
      auto *cloned =
          llvm::CloneBasicBlock(&BB, vmap, "." + Src.getName().str(), dispatcher);
      vmap[&BB] = cloned;
      cloned_blocks.push_back(cloned);
    }

    for (auto *cloned : cloned_blocks) {
      for (auto &I : *cloned)
        llvm::RemapInstruction(&I, vmap,
                               llvm::RF_NoModuleLevelChanges |
                                   llvm::RF_IgnoreMissingLocals);
    }

    for (auto *cloned : cloned_blocks) {
      for (auto it = cloned->begin(); it != cloned->end();) {
        auto &I = *it++;
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (callee != &A && callee != &B)
          continue;

        llvm::IRBuilder<> Bld(call);
        llvm::SmallVector<llvm::Value *, 8> args;
        args.push_back(llvm::ConstantInt::get(llvm::Type::getInt1Ty(Ctx),
                                              callee == &B));
        for (unsigned i = 0; i < max_args; ++i) {
          if (i < call->arg_size()) {
            args.push_back(call->getArgOperand(i));
          } else {
            args.push_back(llvm::PoisonValue::get(union_arg_types[i]));
          }
        }

        auto *replacement = Bld.CreateCall(dispatcher, args);
        replacement->setCallingConv(dispatcher->getCallingConv());
        replacement->setTailCallKind(call->getTailCallKind());
        call->replaceAllUsesWith(replacement);
        call->eraseFromParent();
      }
    }

    (void)dispatch_to_b;
    return llvm::cast<llvm::BasicBlock>(vmap[&Src.getEntryBlock()]);
  };

  auto *a_entry = clone_into_dispatcher(A, false);
  auto *b_entry = clone_into_dispatcher(B, true);

  llvm::IRBuilder<> EntryBuilder(entry);
  EntryBuilder.CreateFreeze(dispatcher->getArg(0), "dispatch.seed");
  EntryBuilder.CreateBr(dispatch_entry);

  llvm::IRBuilder<> Bld(dispatch_entry);
  Bld.CreateCondBr(dispatcher->getArg(0), b_entry, a_entry);

  auto rewrite_external_calls = [&](llvm::Function &Src, bool dispatch_to_b) {
    llvm::SmallVector<llvm::CallBase *, 16> calls;
    for (auto *U : Src.users()) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(U);
      if (!CB || CB->getCalledFunction() != &Src)
        continue;
      calls.push_back(CB);
    }

    for (auto *CB : calls) {
      llvm::IRBuilder<> CallBuilder(CB);
      llvm::SmallVector<llvm::Value *, 8> args;
      args.push_back(
          llvm::ConstantInt::get(llvm::Type::getInt1Ty(Ctx), dispatch_to_b));
      for (unsigned i = 0; i < max_args; ++i) {
        if (i < CB->arg_size()) {
          args.push_back(CB->getArgOperand(i));
        } else {
          args.push_back(llvm::PoisonValue::get(union_arg_types[i]));
        }
      }

      auto *replacement = CallBuilder.CreateCall(dispatcher, args);
      replacement->setCallingConv(dispatcher->getCallingConv());
      if (auto *old_call = llvm::dyn_cast<llvm::CallInst>(CB))
        replacement->setTailCallKind(old_call->getTailCallKind());
      CB->replaceAllUsesWith(replacement);
      CB->eraseFromParent();
    }
  };

  rewrite_external_calls(A, false);
  rewrite_external_calls(B, true);

  if (!A.use_empty() || !B.use_empty()) {
    dispatcher->eraseFromParent();
    return nullptr;
  }

  if (debug)
    llvm::errs() << "[native-mutrec-loopify] canonicalized " << A.getName()
                 << " + " << B.getName() << " -> " << dispatcher->getName()
                 << "\n";

  A.eraseFromParent();
  B.eraseFromParent();
  return dispatcher;
}

static bool loopifyTailRecursiveNativeBlockHelper(llvm::Function &F,
                                                  bool debug = false) {
  if (F.isDeclaration() || F.hasFnAttribute("omill.output_root") ||
      !F.getName().ends_with("_native") ||
      !isSyntheticBlockLikeFunctionName(F.getName())) {
    return false;
  }

  llvm::SmallVector<llvm::CallInst *, 4> recursive_calls;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (call && call->getCalledFunction() == &F)
        recursive_calls.push_back(call);
    }
  }
  if (debug)
    llvm::errs() << "[native-selfrec-loopify] scan " << F.getName()
                 << " recursive_sites=" << recursive_calls.size() << "\n";
  if (recursive_calls.empty())
    return false;

  const auto loopified_terminal_pc = parseSyntheticBlockLikePC(F.getName());
  if (loopified_terminal_pc.has_value())
    F.addFnAttr(kLoopifiedTerminalPcAttr,
                llvm::utohexstr(*loopified_terminal_pc));

  llvm::SmallVector<llvm::CallInst *, 4> loopifiable_calls;
  for (auto *call : recursive_calls) {
    auto *term = call->getParent()->getTerminator();
    auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
    const bool terminal_tail =
        llvm::isa<llvm::ReturnInst>(term) || llvm::isa<llvm::UnreachableInst>(term);
    if ((!br || !br->isUnconditional()) && !terminal_tail) {
      if (debug)
        llvm::errs() << "[native-selfrec-loopify] skip " << F.getName()
                     << " reason=non-uncond-tail\n";
      return false;
    }

    bool safe_suffix = true;
    for (auto *I = call->getNextNode(); I; I = I->getNextNode()) {
      if (I == term)
        break;
      if (!isLoopifiableNativeRecursiveTailSuffixInst(*I, *call, F)) {
        safe_suffix = false;
        if (debug)
          llvm::errs() << "[native-selfrec-loopify] skip " << F.getName()
                       << " reason=unsafe-suffix inst=" << I->getOpcodeName()
                       << "\n";
        break;
      }
    }
    if (!safe_suffix)
      return false;

    auto *successor = br ? br->getSuccessor(0) : nullptr;
    for (auto *U : call->users()) {
      auto *user_inst = llvm::dyn_cast<llvm::Instruction>(U);
      auto *ev = llvm::dyn_cast<llvm::ExtractValueInst>(U);
      auto *phi = llvm::dyn_cast<llvm::PHINode>(U);
      const bool same_block_extract =
          user_inst && ev && user_inst->getParent() == call->getParent();
      const bool successor_phi =
          successor && phi && phi->getParent() == successor &&
          phi->getBasicBlockIndex(call->getParent()) >= 0 &&
          phi->getIncomingValueForBlock(call->getParent()) == call;
      if (!same_block_extract && !successor_phi) {
        if (debug)
          llvm::errs() << "[native-selfrec-loopify] skip " << F.getName()
                       << " reason=unsupported-call-user user=";
        if (debug) {
          if (user_inst) {
            llvm::errs() << user_inst->getOpcodeName()
                         << " block=" << user_inst->getParent()->getName();
          } else {
            llvm::errs() << "<non-inst>";
          }
          llvm::errs() << "\n";
          if (envEnabled("OMILL_DEBUG_SELFREC_LOOPIFY_DUMP"))
            F.print(llvm::errs());
        }
        return false;
      }
    }

    loopifiable_calls.push_back(call);
  }

  auto *loop_header = getOrCreateLoopHeaderAfterAllocas(F);
  if (!loop_header) {
    if (debug)
      llvm::errs() << "[native-selfrec-loopify] skip " << F.getName()
                   << " reason=no-loop-header\n";
    return false;
  }

  auto *entry = &F.getEntryBlock();
  llvm::IRBuilder<> HB(&*loop_header->getFirstInsertionPt());
  llvm::SmallVector<llvm::PHINode *, 8> arg_phis;
  llvm::SmallPtrSet<llvm::Instruction *, 8> phi_set;
  arg_phis.reserve(F.arg_size());
  for (auto &arg : F.args()) {
    auto *phi = HB.CreatePHI(arg.getType(),
                             static_cast<unsigned>(loopifiable_calls.size() + 1),
                             arg.getName() + ".loop");
    arg_phis.push_back(phi);
    phi_set.insert(phi);
  }
  unsigned arg_index = 0;
  for (auto &arg : F.args()) {
    arg_phis[arg_index]->addIncoming(&arg, entry);
    arg.replaceUsesWithIf(arg_phis[arg_index], [&](llvm::Use &U) {
      return !phi_set.contains(llvm::cast<llvm::Instruction>(U.getUser()));
    });
    ++arg_index;
  }

  bool changed = false;
  for (auto *call : loopifiable_calls) {
    auto *BB = call->getParent();
    auto *old_term = BB->getTerminator();
    if (auto *old_br = llvm::dyn_cast<llvm::BranchInst>(old_term)) {
      auto *succ = old_br->getSuccessor(0);
      succ->removePredecessor(BB);
    }

    llvm::SmallVector<llvm::Value *, 8> actuals(call->args());
    for (size_t i = 0; i < actuals.size() && i < arg_phis.size(); ++i)
      arg_phis[i]->addIncoming(actuals[i], BB);

    llvm::SmallVector<llvm::Instruction *, 16> erase_list;
    for (auto it = llvm::BasicBlock::iterator(call), end = BB->end();
         it != end; ++it) {
      erase_list.push_back(&*it);
    }
    for (auto it = erase_list.rbegin(); it != erase_list.rend(); ++it)
      (*it)->eraseFromParent();

    llvm::IRBuilder<> B(BB);
    auto *new_br = B.CreateBr(loop_header);
    if (loopified_terminal_pc.has_value())
      annotateLoopifiedTerminalBranch(*new_br, *loopified_terminal_pc);
    changed = true;
  }

  if (changed) {
    llvm::removeUnreachableBlocks(F);
    if (debug)
      llvm::errs() << "[native-selfrec-loopify] transformed " << F.getName()
                   << " recursive_sites=" << loopifiable_calls.size() << "\n";
  }

  return changed;
}

struct CanonicalizeMutualRecursiveNativeBlockHelpersPass
    : llvm::PassInfoMixin<CanonicalizeMutualRecursiveNativeBlockHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    const bool debug = envEnabled("OMILL_DEBUG_SELFREC_LOOPIFY");
    bool changed = false;

    llvm::SmallVector<llvm::Function *, 32> functions;
    for (auto &F : M)
      functions.push_back(&F);

    llvm::SmallPtrSet<llvm::Function *, 16> handled;
    for (auto *F : functions) {
      if (!F || handled.contains(F) ||
          !isCanonicalizableMutualNativeBlockHelper(*F)) {
        continue;
      }

      auto *G = getSingleSyntheticBlockLikeNativePeerCallee(*F);
      if (!G || G == F || handled.contains(G) ||
          !isCanonicalizableMutualNativeBlockHelper(*G)) {
        if (debug) {
          llvm::errs() << "[native-mutrec-loopify] skip " << F->getName()
                       << " reason=peer-candidate peer="
                       << (G ? G->getName() : llvm::StringRef("<none>"))
                       << "\n";
        }
        continue;
      }
      if (F->getName() >= G->getName())
        continue;

      if (getSingleSyntheticBlockLikeNativePeerCallee(*G) != F ||
          !hasOnlySelfAndPeerSyntheticBlockLikeNativeCallees(*F, *G) ||
          !hasOnlySelfAndPeerSyntheticBlockLikeNativeCallees(*G, *F)) {
        if (debug) {
          llvm::errs() << "[native-mutrec-loopify] skip " << F->getName()
                       << " + " << G->getName()
                       << " reason=callee-shape\n";
        }
        continue;
      }

      llvm::SmallVector<llvm::CallInst *, 8> fg_calls;
      llvm::SmallVector<llvm::CallInst *, 8> gf_calls;
      if (!collectTailLikeCallsToCallee(*F, *G, fg_calls, debug) ||
          !collectTailLikeCallsToCallee(*G, *F, gf_calls, debug)) {
        if (debug) {
          llvm::errs() << "[native-mutrec-loopify] skip " << F->getName()
                       << " + " << G->getName()
                       << " reason=tail-shape\n";
        }
        continue;
      }

      auto *dispatcher =
          canonicalizeMutualRecursiveNativeBlockHelperPair(*F, *G, debug);
      if (!dispatcher) {
        if (debug) {
          llvm::errs() << "[native-mutrec-loopify] skip " << F->getName()
                       << " + " << G->getName()
                       << " reason=canonicalize-failed\n";
        }
        continue;
      }

      handled.insert(F);
      handled.insert(G);
      handled.insert(dispatcher);
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct LoopifyClosedSliceSelfRecursiveBlockHelpersPass
    : llvm::PassInfoMixin<LoopifyClosedSliceSelfRecursiveBlockHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    if (!isClosedRootSliceScopedModule(M) || !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    const bool debug = envEnabled("OMILL_DEBUG_SELFREC_LOOPIFY");
    bool changed = false;
    for (auto &F : M)
      changed |= loopifyClosedSliceSelfRecursiveBlockHelper(F, debug);

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct LoopifySelfRecursiveNativeBlockHelpersPass
    : llvm::PassInfoMixin<LoopifySelfRecursiveNativeBlockHelpersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    const bool debug = envEnabled("OMILL_DEBUG_SELFREC_LOOPIFY");
    bool changed = false;
    for (auto &F : M)
      changed |= loopifyTailRecursiveNativeBlockHelper(F, debug);
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct CollapseSyntheticBlockContinuationCallsPass
    : llvm::PassInfoMixin<CollapseSyntheticBlockContinuationCallsPass> {
  bool rewrite_to_missing_block;
  bool only_when_noabi_mode;

  explicit CollapseSyntheticBlockContinuationCallsPass(
      bool rewrite_to_missing_block = false,
      bool only_when_noabi_mode = false)
      : rewrite_to_missing_block(rewrite_to_missing_block),
        only_when_noabi_mode(only_when_noabi_mode) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    if (only_when_noabi_mode && !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    bool changed = false;
    llvm::SmallVector<llvm::CallInst *, 16> calls_to_erase;
    const bool scoped = isClosedRootSliceScopedModule(M);
    const bool has_unresolved_dispatch =
        llvm::any_of(M, [](llvm::Function &F) {
          return isDispatchIntrinsicName(F.getName()) && !F.use_empty();
        });
    const bool allow_missing_block_rewrite =
        rewrite_to_missing_block && isNoABIModeModule(M) &&
        !has_unresolved_dispatch;
    auto getOrCreateMissingBlock = [&](llvm::FunctionType *FT)
        -> llvm::Function * {
      if (auto *F = M.getFunction("__remill_missing_block")) {
        if (F->getFunctionType() == FT)
          return F;
        return nullptr;
      }
      return llvm::Function::Create(FT, llvm::GlobalValue::ExternalLinkage,
                                    "__remill_missing_block", M);
    };

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (scoped && !isClosedRootSliceFunction(F))
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;

          auto *callee = call->getCalledFunction();
          if (!callee || !callee->isDeclaration())
            continue;

          auto continuation_pc = parseSyntheticBlockLikePC(callee->getName());
          if (!continuation_pc || call->arg_size() < 3)
            continue;

          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg || pc_arg->getZExtValue() != *continuation_pc)
            continue;

          // A declaration-only synthetic continuation call of the form
          //   call @blk_<pc>(state, <same pc>, null)
          // is a no-op on the memory value.
          if (!call->isMustTailCall()) {
            auto *mem_arg_const =
                llvm::dyn_cast<llvm::Constant>(call->getArgOperand(2));
            if (mem_arg_const && mem_arg_const->isNullValue() &&
                !call->getType()->isVoidTy() &&
                call->getType() == call->getArgOperand(2)->getType()) {
              call->replaceAllUsesWith(call->getArgOperand(2));
              calls_to_erase.push_back(call);
              changed = true;
              continue;
            }
          }

          // Otherwise, if the shape is compatible, retarget the unresolved
          // synthetic continuation call to the explicit Remill fallback.
          if (!allow_missing_block_rewrite)
            continue;

          auto *missing_block = getOrCreateMissingBlock(call->getFunctionType());
          if (!missing_block) {
            continue;
          }

          call->setCalledFunction(missing_block);
          changed = true;
        }
      }
    }

    for (auto *call : calls_to_erase)
      call->eraseFromParent();

    llvm::SmallVector<llvm::Function *, 16> dead_decls;
    for (auto &F : M) {
      if (!F.isDeclaration())
        continue;
      if (!parseSyntheticBlockLikePC(F.getName()))
        continue;
      if (F.use_empty())
        dead_decls.push_back(&F);
    }
    for (auto *F : dead_decls)
      F->eraseFromParent();

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct LiftConstantContinuationDeclarationTargetsPass
    : llvm::PassInfoMixin<LiftConstantContinuationDeclarationTargetsPass> {
  bool only_when_noabi_mode;

  explicit LiftConstantContinuationDeclarationTargetsPass(
      bool only_when_noabi_mode = false)
      : only_when_noabi_mode(only_when_noabi_mode) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    if (only_when_noabi_mode && !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    const bool debug_continuation_lifts =
        (std::getenv("OMILL_DEBUG_CONTINUATION_LIFTS") != nullptr);
    const bool scoped = isClosedRootSliceScopedModule(M);
    const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);
    struct PendingContinuationLift {
      uint64_t pc;
      std::string caller_name;
      std::string callee_name;
    };
    // `scheduled` doubles as the per-pass dedup set and the persistent
    // idempotency guard: callers that fail to lift get inserted, so they
    // are not retried even on later cleanup invocations within the same
    // run. We also remember the per-PC try via a module-level metadata
    // marker so the next pass invocation skips them too.
    std::set<uint64_t> scheduled;
    bool changed = false;

    auto shouldProcessFunction = [&](llvm::Function &F) {
      if (!scoped)
        return true;
      return isClosedRootSliceFunction(F) || isLiftedPipelineFunction(F);
    };

    auto session_result = MAM.getCachedResult<IterativeLiftingSessionAnalysis>(M);
    const auto *block_lift_result = MAM.getCachedResult<BlockLiftAnalysis>(M);
    const auto *trace_lift_result = MAM.getCachedResult<TraceLiftAnalysis>(M);
    const auto &block_lift =
        block_lift_result ? block_lift_result->lift_block : BlockLiftCallback{};
    const auto &trace_lift =
        trace_lift_result ? trace_lift_result->lift_trace : TraceLiftCallback{};
    if (!block_lift && !trace_lift)
      return llvm::PreservedAnalyses::all();

    // Bounded fixpoint: each lifted block can introduce new declared
    // blk_*<pc> calls (the next basic block in the chain), and those
    // should be discovered and lifted in the same cleanup invocation
    // rather than waiting for the next phase to find them. We cap both
    // the iteration count AND the total number of newly-lifted blocks
    // per invocation, so a deeply-chained binary cannot cause unbounded
    // work. Previously the defaults were single-shot because deeper
    // expansion exposed `omill_executable_target_*` placeholder calls
    // to the post-main `repairReachableDeclaredStructuralTargets` loop,
    // which would spawn one sub-process omill-lift run per placeholder
    // (tens of seconds per target). That loop is now skipped in the
    // large-noabi generic-static path, so we can safely iterate here
    // to pick up deeper continuation chains in a single cleanup call.
    constexpr unsigned kMaxFixpointIterations = 32;
    constexpr unsigned kMaxLiftsPerInvocation = 512;
    unsigned lifts_this_invocation = 0;
    for (unsigned iteration = 0; iteration < kMaxFixpointIterations;
         ++iteration) {
      if (lifts_this_invocation >= kMaxLiftsPerInvocation)
        break;
      std::vector<PendingContinuationLift> pending_lifts;

      // Pre-collect lift work so the lifter can freely mutate the module
      // without invalidating the iterators we're using to discover candidates.
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        if (!shouldProcessFunction(F))
          continue;

        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee = call->getCalledFunction();
            if (!callee || !callee->isDeclaration())
              continue;

            auto continuation_pc = parseSyntheticBlockLikePC(callee->getName());
            if (!continuation_pc)
              continue;

            auto *pc_arg =
                llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
            if (!pc_arg || pc_arg->getZExtValue() != *continuation_pc)
              continue;
            if (!binary_memory.isExecutable(*continuation_pc, 1)) {
              if (debug_continuation_lifts)
                llvm::errs() << "[continuation-lift] skip non-executable pc=0x"
                             << llvm::Twine::utohexstr(*continuation_pc)
                             << " in " << F.getName() << "\n";
              continue;
            }
            if (findSyntheticBlockLikeDefinition(M, *continuation_pc)) {
              if (debug_continuation_lifts)
                llvm::errs() << "[continuation-lift] already-defined pc=0x"
                             << llvm::Twine::utohexstr(*continuation_pc)
                             << "\n";
              continue;
            }
            if (!scheduled.insert(*continuation_pc).second)
              continue;

            pending_lifts.push_back(
                {*continuation_pc, F.getName().str(), callee->getName().str()});
          }
        }
      }

      if (pending_lifts.empty())
        break;

      bool any_lifted_this_round = false;
      for (const auto &pending : pending_lifts) {
        if (lifts_this_invocation >= kMaxLiftsPerInvocation)
          break;
        if (debug_continuation_lifts)
          llvm::errs() << "[continuation-lift] attempt iteration="
                       << iteration << " pc=0x"
                       << llvm::Twine::utohexstr(pending.pc)
                       << " caller=" << pending.caller_name
                       << " callee=" << pending.callee_name << "\n";

        bool lifted = false;
        if (session_result && session_result->session &&
            session_result->session->useBlockLifting() && block_lift) {
          lifted = block_lift(pending.pc);
        } else if (block_lift) {
          lifted = block_lift(pending.pc);
        } else if (trace_lift) {
          lifted = trace_lift(pending.pc);
        }

        if (lifted && session_result && session_result->session)
          session_result->session->noteLiftedTarget(pending.pc);
        auto *lifted_target =
            lifted ? findSyntheticBlockLikeDefinition(M, pending.pc) : nullptr;
        if (debug_continuation_lifts) {
          llvm::errs() << "[continuation-lift] result pc=0x"
                       << llvm::Twine::utohexstr(pending.pc)
                       << " lifted=" << lifted
                       << " defined=" << (lifted_target != nullptr);
          if (auto *blk = M.getFunction(
                  (llvm::Twine("blk_") + llvm::Twine::utohexstr(pending.pc))
                      .str())) {
            llvm::errs() << " blk_decl=" << blk->isDeclaration();
          }
          if (auto *sub = M.getFunction(
                  (llvm::Twine("sub_") + llvm::Twine::utohexstr(pending.pc))
                      .str())) {
            llvm::errs() << " sub_decl=" << sub->isDeclaration();
          }
          llvm::errs() << "\n";
        }
        if (lifted_target) {
          changed = true;
          any_lifted_this_round = true;
          ++lifts_this_invocation;
        }
      }

      // No forward progress this round → done. The persistent `scheduled`
      // set guarantees we don't replay the same failed targets next round.
      if (!any_lifted_this_round)
        break;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct LiftConstantMissingBlockTargetsPass
    : llvm::PassInfoMixin<LiftConstantMissingBlockTargetsPass> {
  bool only_when_noabi_mode;

  explicit LiftConstantMissingBlockTargetsPass(bool only_when_noabi_mode = false)
      : only_when_noabi_mode(only_when_noabi_mode) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    if (only_when_noabi_mode && !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    const bool debug_continuation_lifts =
        (std::getenv("OMILL_DEBUG_CONTINUATION_LIFTS") != nullptr);
    const bool scoped = isClosedRootSliceScopedModule(M);
    const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);
    struct PendingMissingBlockLift {
      uint64_t pc;
      std::string caller_name;
    };
    std::vector<PendingMissingBlockLift> pending_lifts;
    std::set<uint64_t> scheduled;
    bool changed = false;

    auto session_result = MAM.getCachedResult<IterativeLiftingSessionAnalysis>(M);
    const auto *block_lift_result = MAM.getCachedResult<BlockLiftAnalysis>(M);
    const auto *trace_lift_result = MAM.getCachedResult<TraceLiftAnalysis>(M);
    const auto &block_lift =
        block_lift_result ? block_lift_result->lift_block : BlockLiftCallback{};
    const auto &trace_lift =
        trace_lift_result ? trace_lift_result->lift_trace : TraceLiftCallback{};
    if (!block_lift && !trace_lift)
      return llvm::PreservedAnalyses::all();

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (scoped && !isClosedRootSliceFunction(F))
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;

          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg)
            continue;
          const uint64_t target_pc = pc_arg->getZExtValue();
          if (!target_pc)
            continue;
          if (!binary_memory.isExecutable(target_pc, 1)) {
            if (debug_continuation_lifts)
              llvm::errs() << "[missing-block-lift] skip non-executable pc=0x"
                           << llvm::Twine::utohexstr(target_pc) << " in "
                           << F.getName() << "\n";
            continue;
          }
          if (findSyntheticBlockLikeDefinition(M, target_pc)) {
            if (debug_continuation_lifts)
              llvm::errs() << "[missing-block-lift] already-defined pc=0x"
                           << llvm::Twine::utohexstr(target_pc) << "\n";
            continue;
          }
          if (!scheduled.insert(target_pc).second)
            continue;

          pending_lifts.push_back({target_pc, F.getName().str()});
        }
      }
    }

    for (const auto &pending : pending_lifts) {
      if (debug_continuation_lifts)
        llvm::errs() << "[missing-block-lift] attempt pc=0x"
                     << llvm::Twine::utohexstr(pending.pc)
                     << " caller=" << pending.caller_name << "\n";

      bool lifted = false;
      if (session_result && session_result->session &&
          session_result->session->useBlockLifting() && block_lift) {
        lifted = block_lift(pending.pc);
      } else if (block_lift) {
        lifted = block_lift(pending.pc);
      } else if (trace_lift) {
        lifted = trace_lift(pending.pc);
      }

      if (lifted && session_result && session_result->session)
        session_result->session->noteLiftedTarget(pending.pc);
      auto *lifted_target =
          lifted ? findSyntheticBlockLikeDefinition(M, pending.pc) : nullptr;
      if (debug_continuation_lifts) {
        llvm::errs() << "[missing-block-lift] result pc=0x"
                     << llvm::Twine::utohexstr(pending.pc)
                     << " lifted=" << lifted
                     << " defined=" << (lifted_target != nullptr);
        if (auto *blk = M.getFunction(
                (llvm::Twine("blk_") + llvm::Twine::utohexstr(pending.pc))
                    .str())) {
          llvm::errs() << " blk_decl=" << blk->isDeclaration();
        }
        if (auto *sub = M.getFunction(
                (llvm::Twine("sub_") + llvm::Twine::utohexstr(pending.pc))
                    .str())) {
          llvm::errs() << " sub_decl=" << sub->isDeclaration();
        }
        llvm::errs() << "\n";
      }
      if (lifted_target)
        changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct RewriteConstantMissingBlockCallsPass
    : llvm::PassInfoMixin<RewriteConstantMissingBlockCallsPass> {
  bool only_when_noabi_mode;

  explicit RewriteConstantMissingBlockCallsPass(bool only_when_noabi_mode = false)
      : only_when_noabi_mode(only_when_noabi_mode) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    if (only_when_noabi_mode && !isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    const bool scoped = isClosedRootSliceScopedModule(M);
    bool changed = false;

    auto shouldProcessFunction = [&](llvm::Function &F) {
      if (!scoped)
        return true;
      return isClosedRootSliceFunction(F) || isLiftedPipelineFunction(F);
    };

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (!shouldProcessFunction(F))
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;

          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg)
            continue;

          uint64_t resolved_pc = 0;
          auto *target = findExactOrNearbyDefinedLiftedOrBlockTarget(
              M, pc_arg->getZExtValue(), &resolved_pc);
          if (!target || target == &F || target->isDeclaration())
            continue;
          if (target->getFunctionType() != call->getFunctionType())
            continue;
          if (isTerminalMissingBlockStub(*target))
            continue;

          call->setCalledFunction(target);
          if (resolved_pc != 0 && resolved_pc != pc_arg->getZExtValue()) {
            call->setArgOperand(
                1, llvm::ConstantInt::get(pc_arg->getType(), resolved_pc));
          }
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass
    : llvm::PassInfoMixin<
          RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    if (isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    const bool scoped = isClosedRootSliceScopedModule(M);
    static const bool debug_terminal_synth_blocks =
        (std::getenv("OMILL_DEBUG_TERMINAL_SYNTH_BLOCKS") != nullptr);
    llvm::Function *missing_block_handler = nullptr;
    bool changed = false;

    auto getOrCreateMissingBlockHandler = [&]() -> llvm::Function * {
      if (missing_block_handler)
        return missing_block_handler;
      auto &ctx = M.getContext();
      auto *handler_ty = llvm::FunctionType::get(
          llvm::Type::getVoidTy(ctx), {llvm::Type::getInt64Ty(ctx)}, false);
      missing_block_handler = llvm::cast<llvm::Function>(
          M.getOrInsertFunction("__omill_missing_block_handler", handler_ty)
              .getCallee());
      return missing_block_handler;
    };

    auto nextNonDebug = [](llvm::Instruction *I) -> llvm::Instruction * {
      for (auto *next = I->getNextNode(); next; next = next->getNextNode()) {
        if (!llvm::isa<llvm::DbgInfoIntrinsic>(next))
          return next;
      }
      return nullptr;
    };

    auto isTerminalSyntheticLoopSuffix = [&](llvm::CallInst *call) {
      auto *BB = call->getParent();
      auto *term = BB->getTerminator();
      auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
      if (!br || !br->isUnconditional() || br->getSuccessor(0) != BB) {
        if (debug_terminal_synth_blocks) {
          llvm::errs() << "[term-synth] loop-suffix reject reason=terminator";
          if (term)
            llvm::errs() << " term=" << term->getOpcodeName();
          llvm::errs() << "\n";
        }
        return false;
      }

      llvm::SmallVector<llvm::Instruction *, 8> suffix_insts;
      llvm::DenseSet<const llvm::Instruction *> suffix_set;
      for (auto *next = call->getNextNode(); next; next = next->getNextNode()) {
        if (next == term)
          break;
        suffix_insts.push_back(next);
        suffix_set.insert(next);
      }

      auto isAllowedSuffixInst = [&](llvm::Instruction *inst) {
        std::function<bool(const llvm::Value *, unsigned)> isLocalSuffixInteger;
        std::function<bool(const llvm::Value *, unsigned)> isLocalSuffixPointer;

        isLocalSuffixPointer = [&](const llvm::Value *V, unsigned depth) {
          if (!V || depth > 8)
            return false;
          if (isEntryAllocaBackedPointer(V, *call->getFunction()))
            return true;
          auto *stripped = V->stripPointerCasts();
          if (auto *inst_v = llvm::dyn_cast<llvm::Instruction>(stripped);
              inst_v && suffix_set.contains(inst_v)) {
            return true;
          }
          if (auto *gep = llvm::dyn_cast<llvm::GEPOperator>(stripped))
            return isLocalSuffixPointer(gep->getPointerOperand(), depth + 1);
          if (auto *op = llvm::dyn_cast<llvm::Operator>(stripped)) {
            if (op->getOpcode() == llvm::Instruction::IntToPtr)
              return isLocalSuffixInteger(op->getOperand(0), depth + 1);
          }
          return false;
        };

        isLocalSuffixInteger = [&](const llvm::Value *V, unsigned depth) {
          if (!V || depth > 8)
            return false;
          if (llvm::isa<llvm::ConstantInt>(V))
            return true;
          auto *stripped = V->stripPointerCasts();
          if (auto *inst_v = llvm::dyn_cast<llvm::Instruction>(stripped);
              inst_v && suffix_set.contains(inst_v)) {
            return true;
          }
          if (auto *op = llvm::dyn_cast<llvm::Operator>(stripped)) {
            switch (op->getOpcode()) {
              case llvm::Instruction::PtrToInt:
                return isLocalSuffixPointer(op->getOperand(0), depth + 1);
              case llvm::Instruction::Add:
              case llvm::Instruction::Sub:
              case llvm::Instruction::Or:
                return isLocalSuffixInteger(op->getOperand(0), depth + 1) &&
                       isLocalSuffixInteger(op->getOperand(1), depth + 1);
              case llvm::Instruction::Trunc:
              case llvm::Instruction::ZExt:
              case llvm::Instruction::SExt:
              case llvm::Instruction::And:
                return isLocalSuffixInteger(op->getOperand(0), depth + 1) &&
                       (op->getNumOperands() == 1 ||
                        isLocalSuffixInteger(op->getOperand(1), depth + 1));
              default:
                break;
            }
          }
          return false;
        };

        if (isLoopifiableRecursiveTailSuffixInst(*inst, *call->getFunction()))
          return true;
        if (auto *store = llvm::dyn_cast<llvm::StoreInst>(inst))
          return isLocalSuffixPointer(store->getPointerOperand(), 0);
        if (inst->mayHaveSideEffects() || inst->isTerminator() ||
            llvm::isa<llvm::PHINode>(inst))
          return false;
        for (auto *user : inst->users()) {
          auto *user_inst = llvm::dyn_cast<llvm::Instruction>(user);
          if (!user_inst || !suffix_set.contains(user_inst))
            return false;
        }
        return true;
      };

      for (auto *next : suffix_insts) {
        const bool allowed = isAllowedSuffixInst(next);
        if (debug_terminal_synth_blocks) {
          llvm::errs() << "[term-synth] loop-suffix inspect opcode="
                       << next->getOpcodeName();
          if (auto *callee =
                  llvm::dyn_cast<llvm::CallBase>(next)
                      ? llvm::dyn_cast<llvm::CallBase>(next)->getCalledFunction()
                      : nullptr) {
            llvm::errs() << " callee=" << callee->getName();
          }
          if (auto *store = llvm::dyn_cast<llvm::StoreInst>(next)) {
            llvm::errs() << " ptr=";
            store->getPointerOperand()->printAsOperand(llvm::errs(), false);
            llvm::errs() << " entry_alloca_backed="
                         << isEntryAllocaBackedPointer(
                                store->getPointerOperand(),
                                *call->getFunction());
          }
          llvm::errs() << " allowed=" << allowed << "\n";
        }
        if (!allowed)
          return false;
      }
      return true;
    };

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (scoped && !isClosedRootSliceFunction(F))
        continue;

      for (auto &BB : F) {
        bool rewrote_block = false;
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          if (debug_terminal_synth_blocks && call->getCalledFunction() &&
              parseSyntheticBlockLikePC(call->getCalledFunction()->getName())) {
            llvm::errs() << "[term-synth] inspect caller=" << F.getName()
                         << " block=" << BB.getName()
                         << " callee=" << call->getCalledFunction()->getName()
                         << " args=" << call->arg_size()
                         << " use_empty=" << call->use_empty() << "\n";
          }
          if (call->arg_size() < 3 || !call->use_empty()) {
            if (debug_terminal_synth_blocks && call->getCalledFunction() &&
                parseSyntheticBlockLikePC(call->getCalledFunction()->getName())) {
              llvm::errs() << "[term-synth] skip reason=shape\n";
            }
            continue;
          }

          auto *callee = call->getCalledFunction();
          if (!callee || !callee->isDeclaration()) {
            if (debug_terminal_synth_blocks && callee &&
                parseSyntheticBlockLikePC(callee->getName())) {
              llvm::errs() << "[term-synth] skip reason=callee-not-decl\n";
            }
            continue;
          }

          auto continuation_pc = parseSyntheticBlockLikePC(callee->getName());
          if (!continuation_pc)
            continue;

          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg || pc_arg->getZExtValue() != *continuation_pc) {
            if (debug_terminal_synth_blocks) {
              llvm::errs() << "[term-synth] skip reason=pc-mismatch";
              if (pc_arg)
                llvm::errs() << " arg=0x"
                             << llvm::Twine::utohexstr(pc_arg->getZExtValue());
              llvm::errs() << " callee_pc=0x"
                           << llvm::Twine::utohexstr(*continuation_pc) << "\n";
            }
            continue;
          }
          if (!isTerminalSyntheticMemoryArgValue(call->getArgOperand(2))) {
            if (debug_terminal_synth_blocks) {
              llvm::errs() << "[term-synth] skip reason=memory-arg\n";
            }
            continue;
          }

          auto *next = nextNonDebug(call);
          const bool is_terminal_unreachable =
              next && llvm::isa<llvm::UnreachableInst>(next);
          const bool is_terminal_self_loop = isTerminalSyntheticLoopSuffix(call);
          if (!is_terminal_unreachable && !is_terminal_self_loop) {
            if (debug_terminal_synth_blocks) {
              llvm::errs() << "[term-synth] skip reason=terminal-shape";
              if (next)
                llvm::errs() << " next=" << next->getOpcodeName();
              else
                llvm::errs() << " next=<null>";
              llvm::errs() << "\n";
            }
            continue;
          }

          if (debug_terminal_synth_blocks) {
            llvm::errs() << "[term-synth] rewrite caller=" << F.getName()
                         << " block=" << BB.getName()
                         << " callee=" << callee->getName()
                         << " self_loop=" << is_terminal_self_loop
                         << " unreachable=" << is_terminal_unreachable << "\n";
          }

          llvm::IRBuilder<> B(call);
          B.CreateCall(getOrCreateMissingBlockHandler(),
                       {llvm::ConstantInt::get(
                           llvm::Type::getInt64Ty(M.getContext()),
                           *continuation_pc)});
          if (is_terminal_self_loop) {
            auto *call_bb = call->getParent();
            llvm::SmallVector<llvm::Instruction *, 8> erase_list;
            for (auto it = llvm::BasicBlock::iterator(call), end = call_bb->end();
                 it != end; ++it) {
              erase_list.push_back(&*it);
            }
            for (auto *inst : erase_list)
              inst->eraseFromParent();
            llvm::IRBuilder<> TailB(call_bb);
            TailB.CreateUnreachable();
            rewrote_block = true;
          } else {
            call->eraseFromParent();
          }
          changed = true;
          if (rewrote_block)
            break;
        }
        if (rewrote_block)
          continue;
      }
    }

    llvm::SmallVector<llvm::Function *, 16> dead_decls;
    for (auto &F : M) {
      if (!F.isDeclaration())
        continue;
      if (!parseSyntheticBlockLikePC(F.getName()))
        continue;
      if (F.use_empty())
        dead_decls.push_back(&F);
    }
    for (auto *F : dead_decls)
      F->eraseFromParent();

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct EraseIsolatedSyntheticBlockWrapperCallsPass
    : llvm::PassInfoMixin<EraseIsolatedSyntheticBlockWrapperCallsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    if (isNoABIModeModule(M))
      return llvm::PreservedAnalyses::all();

    static const bool debug_erase_synth_wrappers =
        (std::getenv("OMILL_DEBUG_ERASE_SYNTH_WRAPPERS") != nullptr);
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;

      for (auto &BB : F) {
        for (auto it = BB.begin(); it != BB.end();) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&*it++);
          if (!call || !call->use_empty() || call->arg_size() < 3)
            continue;

          auto *callee = call->getCalledFunction();
          if (!callee || !callee->isDeclaration() ||
              !parseSyntheticBlockLikePC(callee->getName()))
            continue;
          if (!isTerminalSyntheticMemoryArgValue(call->getArgOperand(2)))
            continue;
          if (!isEntryAllocaBackedPointer(call->getArgOperand(0), F))
            continue;

          if (debug_erase_synth_wrappers) {
            llvm::errs() << "[erase-synth] candidate caller=" << F.getName()
                         << " block=" << BB.getName()
                         << " callee=" << callee->getName() << "\n";
          }

          llvm::SmallVector<llvm::Instruction *, 8> erase_list;
          erase_list.push_back(call);
          bool only_wrapper_teardown = true;
          for (auto *next = call->getNextNode(); next; next = next->getNextNode()) {
            if (llvm::isa<llvm::DbgInfoIntrinsic>(next))
              continue;
            auto *intr = llvm::dyn_cast<llvm::IntrinsicInst>(next);
            if (!intr || intr->getIntrinsicID() != llvm::Intrinsic::lifetime_end)
              break;
            if (!isEntryAllocaBackedPointer(intr->getArgOperand(1), F)) {
              only_wrapper_teardown = false;
              break;
            }
            erase_list.push_back(next);
          }
          if (!only_wrapper_teardown)
            continue;

          if (debug_erase_synth_wrappers)
            llvm::errs() << "[erase-synth] erase_count=" << erase_list.size()
                         << "\n";
          auto *resume = erase_list.back()->getNextNode();
          for (auto *inst : erase_list)
            inst->eraseFromParent();
          if (resume)
            it = resume->getIterator();
          changed = true;
        }
      }
    }

    if (changed) {
      llvm::SmallVector<llvm::Function *, 16> dead_decls;
      for (auto &F : M) {
        if (!F.isDeclaration())
          continue;
        if (!parseSyntheticBlockLikePC(F.getName()))
          continue;
        if (F.use_empty())
          dead_decls.push_back(&F);
      }
      if (debug_erase_synth_wrappers)
        llvm::errs() << "[erase-synth] dead_decl_count=" << dead_decls.size()
                     << "\n";
      for (auto *F : dead_decls)
        F->eraseFromParent();
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct SeedTerminalSyntheticBoundaryCandidatesPass
    : llvm::PassInfoMixin<SeedTerminalSyntheticBoundaryCandidatesPass> {
  static std::optional<uint64_t> inferCandidatePc(const llvm::Function &F) {
    std::optional<uint64_t> candidate_pc;
    bool conflict = false;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || CB->arg_size() < 3)
          continue;
        auto *callee = CB->getCalledFunction();
        if (!callee || !callee->isDeclaration())
          continue;
        auto continuation_pc = parseSyntheticBlockLikePC(callee->getName());
        if (!continuation_pc)
          continue;
        auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(1));
        if (!pc_arg || pc_arg->getZExtValue() != *continuation_pc)
          continue;
        if (!isTerminalSyntheticMemoryArgValue(CB->getArgOperand(2)))
          continue;

        if (!candidate_pc.has_value()) {
          candidate_pc = *continuation_pc;
        } else if (*candidate_pc != *continuation_pc) {
          conflict = true;
          break;
        }
      }
      if (conflict)
        break;
    }

    if (conflict)
      return std::nullopt;
    return candidate_pc;
  }

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;

    for (auto &F : M) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      if (F.hasFnAttribute(kTerminalBoundaryCandidatePcAttr))
        continue;

      auto candidate_pc = inferCandidatePc(F);
      if (candidate_pc.has_value()) {
        F.addFnAttr(kTerminalBoundaryCandidatePcAttr,
                    llvm::utohexstr(*candidate_pc));
        changed = true;
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct PropagateLoopifiedTerminalBoundaryAttrsPass
    : llvm::PassInfoMixin<PropagateLoopifiedTerminalBoundaryAttrsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;
    bool local_change = true;

    while (local_change) {
      local_change = false;
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        std::optional<std::string> loopified_pc;
        std::optional<std::string> candidate_pc;
        bool loopified_conflict = false;
        bool candidate_conflict = false;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *callee = CB->getCalledFunction();
            if (!callee || callee->isDeclaration())
              continue;

            auto loopified_attr = callee->getFnAttribute(kLoopifiedTerminalPcAttr);
            if (loopified_attr.isValid()) {
              auto pc = loopified_attr.getValueAsString().str();
              if (!loopified_pc.has_value()) {
                loopified_pc = pc;
              } else if (*loopified_pc != pc) {
                loopified_conflict = true;
              }
            }

            auto candidate_attr =
                callee->getFnAttribute(kTerminalBoundaryCandidatePcAttr);
            if (!candidate_attr.isValid())
              candidate_attr = callee->getFnAttribute(kLoopifiedTerminalPcAttr);
            auto inferred_candidate_pc =
                SeedTerminalSyntheticBoundaryCandidatesPass::inferCandidatePc(
                    *callee);
            if (candidate_attr.isValid() || inferred_candidate_pc.has_value()) {
              auto pc = candidate_attr.isValid()
                            ? candidate_attr.getValueAsString().str()
                            : llvm::utohexstr(*inferred_candidate_pc);
              if (!candidate_pc.has_value()) {
                candidate_pc = pc;
              } else if (*candidate_pc != pc) {
                candidate_conflict = true;
              }
            }
          }
          if (loopified_conflict && candidate_conflict)
            break;
        }

        if (!F.hasFnAttribute(kLoopifiedTerminalPcAttr) &&
            !loopified_conflict && loopified_pc.has_value()) {
          F.addFnAttr(kLoopifiedTerminalPcAttr, *loopified_pc);
          local_change = true;
          changed = true;
        }

        if (!F.hasFnAttribute(kTerminalBoundaryCandidatePcAttr) &&
            !candidate_conflict && candidate_pc.has_value()) {
          F.addFnAttr(kTerminalBoundaryCandidatePcAttr, *candidate_pc);
          local_change = true;
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct PropagateTerminalBoundaryAttrsToNativeRootsPass
    : llvm::PassInfoMixin<PropagateTerminalBoundaryAttrsToNativeRootsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (!F.getName().ends_with("_native"))
        continue;
      if (F.hasFnAttribute(kTerminalBoundaryCandidatePcAttr))
        continue;

      auto lifted_name = F.getName().drop_back(7);
      auto *lifted = M.getFunction(lifted_name);
      if (!lifted || lifted->isDeclaration())
        continue;

      auto candidate_attr = lifted->getFnAttribute(kTerminalBoundaryCandidatePcAttr);
      if (candidate_attr.isValid()) {
        F.addFnAttr(kTerminalBoundaryCandidatePcAttr,
                    candidate_attr.getValueAsString());
        changed = true;
      }

      if (!F.hasFnAttribute(kLoopifiedTerminalPcAttr)) {
        auto loopified_attr = lifted->getFnAttribute(kLoopifiedTerminalPcAttr);
        if (loopified_attr.isValid()) {
          F.addFnAttr(kLoopifiedTerminalPcAttr,
                      loopified_attr.getValueAsString());
          changed = true;
        }
      }
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct RewriteLoopifiedTerminalBoundaryOutputRootsPass
    : llvm::PassInfoMixin<RewriteLoopifiedTerminalBoundaryOutputRootsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    static const bool debug_terminal_rewrite =
        (std::getenv("OMILL_DEBUG_TERMINAL_REWRITE") != nullptr);
    llvm::Function *missing_block_handler = nullptr;
    bool changed = false;

    auto isTrivialLoopifyBlock =
        [&](llvm::Function &F, llvm::BasicBlock &BB,
            std::optional<uint64_t> &target_pc) -> bool {
      auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
      if (!br || !br->isUnconditional() || br->getSuccessor(0) != &BB)
        return false;
      target_pc = getLoopifiedTerminalBranchPc(*br);

      for (auto &I : BB) {
        if (&I == br || llvm::isa<llvm::DbgInfoIntrinsic>(&I))
          continue;
        if (auto *phi = llvm::dyn_cast<llvm::PHINode>(&I)) {
          for (auto i = 0u; i < phi->getNumIncomingValues(); ++i) {
            if (phi->getIncomingBlock(i) == &BB)
              return false;
          }
          continue;
        }
        if (isLoopifiableRecursiveTailSuffixInst(I, F))
          continue;
        if (!I.mayHaveSideEffects() && !I.isTerminator())
          continue;
        return false;
      }
      return true;
    };

    for (auto &F : M) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      if (debug_terminal_rewrite)
        llvm::errs() << "[terminal-rewrite] inspect " << F.getName() << "\n";

      uint64_t target_pc = 0;
      llvm::BasicBlock *loop_block = nullptr;
      bool skip_function = false;
      for (auto &BB : F) {
        std::optional<uint64_t> block_pc;
        if (!isTrivialLoopifyBlock(F, BB, block_pc))
          continue;
        if (loop_block) {
          skip_function = true;
          if (debug_terminal_rewrite) {
            llvm::errs() << "[terminal-rewrite] skip " << F.getName()
                         << " multiple-loop-blocks\n";
          }
          break;
        }
        loop_block = &BB;
        if (block_pc.has_value())
          target_pc = *block_pc;
      }

      if (skip_function || !loop_block) {
        if (debug_terminal_rewrite && !loop_block && !skip_function) {
          llvm::errs() << "[terminal-rewrite] skip " << F.getName()
                       << " no-trivial-loop-block\n";
        }
        continue;
      }

      if (!target_pc) {
        if (auto candidate_pc = getTerminalBoundaryCandidatePc(F);
            candidate_pc.has_value()) {
          target_pc = *candidate_pc;
        }
      }

      if (!target_pc) {
        auto attr = F.getFnAttribute(kLoopifiedTerminalPcAttr);
        if (attr.isValid()) {
          uint64_t parsed_pc = 0;
          if (!attr.getValueAsString().getAsInteger(16, parsed_pc))
            target_pc = parsed_pc;
        }
      }

      if (!target_pc) {
        if (debug_terminal_rewrite) {
          llvm::errs() << "[terminal-rewrite] skip " << F.getName()
                       << " no-target-pc\n";
        }
        continue;
      }

      for (auto &BB : F) {
        if (&BB == loop_block)
          continue;
        for (auto &I : BB) {
          if (llvm::isa<llvm::DbgInfoIntrinsic>(&I))
            continue;
          if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
            if (&BB == &F.getEntryBlock() && AI->getParent() == &F.getEntryBlock())
              continue;
          }
          if (isLoopifiableRecursiveTailSuffixInst(I, F))
            continue;
          if (!I.mayHaveSideEffects() && !I.isTerminator())
            continue;
          auto *br = llvm::dyn_cast<llvm::BranchInst>(&I);
          if (br && br->isUnconditional() && br->getSuccessor(0) == loop_block)
            continue;
          skip_function = true;
          if (debug_terminal_rewrite) {
            llvm::errs() << "[terminal-rewrite] skip " << F.getName()
                         << " extra-body " << BB.getName() << "\n";
          }
          break;
        }
        if (skip_function)
          break;
      }

      if (skip_function)
        continue;

      if (debug_terminal_rewrite) {
        llvm::errs() << "[terminal-rewrite] rewrite " << F.getName()
                     << " target=0x" << llvm::utohexstr(target_pc) << "\n";
      }
      changed |= rewriteTerminalBoundaryOutputRoot(
          M, F, target_pc, missing_block_handler);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct RewriteIndirectCallTerminalBoundaryOutputRootsPass
    : llvm::PassInfoMixin<RewriteIndirectCallTerminalBoundaryOutputRootsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    llvm::Function *missing_block_handler = nullptr;
    bool changed = false;

    for (auto &F : M) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      bool saw_self_loop = false;
      bool saw_missing_block_handler = false;
      bool conflict = false;
      std::optional<uint64_t> target_pc;

      for (auto &BB : F) {
        if (auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator())) {
          if (br->isUnconditional() && br->getSuccessor(0) == &BB)
            saw_self_loop = true;
        }

        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;

          if (auto *callee = CB->getCalledFunction()) {
            if (callee->isIntrinsic())
              continue;
            if (callee->getName() == "__omill_missing_block_handler") {
              saw_missing_block_handler = true;
              continue;
            }
            conflict = true;
            break;
          }

          auto pc = getConstantIndirectCallTargetPc(*CB);
          if (!pc.has_value()) {
            conflict = true;
            break;
          }

          if (!target_pc.has_value()) {
            target_pc = *pc;
          } else if (*target_pc != *pc) {
            conflict = true;
            break;
          }
        }

        if (conflict)
          break;
      }

      if (conflict || saw_missing_block_handler || !saw_self_loop ||
          !target_pc.has_value()) {
        continue;
      }
      changed |= rewriteTerminalBoundaryOutputRoot(
          M, F, *target_pc, missing_block_handler);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct RewriteStateWrapperTerminalBoundaryOutputRootsPass
    : llvm::PassInfoMixin<RewriteStateWrapperTerminalBoundaryOutputRootsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    const bool debug =
        (std::getenv("OMILL_DEBUG_TERMINAL_BOUNDARY_REWRITE") != nullptr);
    llvm::Function *missing_block_handler = nullptr;
    bool changed = false;

    for (auto &F : M) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      if (!F.hasFnAttribute(kTerminalBoundaryCandidatePcAttr))
        continue;
      if (F.hasFnAttribute("omill.terminal_boundary_kind"))
        continue;

      auto target_pc = getTerminalBoundaryCandidatePc(F);
      if (!target_pc.has_value())
        continue;

      bool saw_missing_block_handler = false;
      llvm::CallBase *terminal_call = nullptr;
      bool conflict = false;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;
          auto *callee = CB->getCalledFunction();
          if (!callee) {
            conflict = true;
            break;
          }
          if (callee->isIntrinsic())
            continue;
          if (callee->getName() == "__omill_missing_block_handler") {
            saw_missing_block_handler = true;
            break;
          }
          if (terminal_call) {
            conflict = true;
            break;
          }
          terminal_call = CB;
        }

        if (saw_missing_block_handler || conflict)
          break;
      }

      if (debug) {
        llvm::errs() << "[terminal-boundary-rewrite] candidate "
                     << F.getName() << " target=0x"
                     << llvm::utohexstr(*target_pc)
                     << " saw_missing=" << saw_missing_block_handler
                     << " conflict=" << conflict
                     << " has_terminal_call=" << (terminal_call != nullptr)
                     << "\n";
      }

      if (saw_missing_block_handler || conflict || !terminal_call)
        continue;

      auto *callee = terminal_call->getCalledFunction();
      if (!callee || callee->isDeclaration()) {
        if (debug)
          llvm::errs() << "[terminal-boundary-rewrite] skip "
                       << F.getName() << " reason=callee_decl\n";
        continue;
      }
      if (!F.getName().ends_with("_native")) {
        if (debug)
          llvm::errs() << "[terminal-boundary-rewrite] skip "
                       << F.getName() << " reason=not_native\n";
        continue;
      }
      auto expected_lifted_name = F.getName().drop_back(strlen("_native"));
      if (callee->getName() != expected_lifted_name) {
        if (debug)
          llvm::errs() << "[terminal-boundary-rewrite] skip "
                       << F.getName() << " reason=name_mismatch callee="
                       << callee->getName() << " expected="
                       << expected_lifted_name << "\n";
        continue;
      }

      if (debug)
        llvm::errs() << "[terminal-boundary-rewrite] rewrite "
                     << F.getName() << "\n";
      changed |= rewriteTerminalBoundaryOutputRoot(M, F, *target_pc,
                                                   missing_block_handler);
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct CanonicalizeTerminalBoundaryOutputRootsToProbeCyclePass
    : llvm::PassInfoMixin<
          CanonicalizeTerminalBoundaryOutputRootsToProbeCyclePass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    static constexpr llvm::StringLiteral kProbeCycleCanonicalAttr =
        "omill.terminal_boundary_probe_cycle_canonical_target_va";
    static constexpr llvm::StringLiteral kOriginalTargetAttr =
        "omill.terminal_boundary_original_target_va";

    bool changed = false;

    for (auto &F : M) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      auto canonical_attr = F.getFnAttribute(kProbeCycleCanonicalAttr);
      if (!canonical_attr.isValid())
        continue;

      uint64_t canonical_pc = 0;
      if (canonical_attr.getValueAsString().getAsInteger(16, canonical_pc) ||
          canonical_pc == 0) {
        continue;
      }

      uint64_t current_pc = 0;
      bool has_current_pc = false;
      if (auto target_attr = F.getFnAttribute("omill.terminal_boundary_target_va");
          target_attr.isValid() &&
          !target_attr.getValueAsString().getAsInteger(16, current_pc) &&
          current_pc != 0) {
        has_current_pc = true;
      } else if (auto candidate_pc = getTerminalBoundaryCandidatePc(F);
                 candidate_pc.has_value()) {
        current_pc = *candidate_pc;
        has_current_pc = true;
      }

      if (has_current_pc && current_pc == canonical_pc)
        continue;

      llvm::CallInst *handler_call = nullptr;
      bool conflict = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI)
            continue;
          auto *callee = CI->getCalledFunction();
          if (!callee || callee->getName() != "__omill_missing_block_handler")
            continue;
          if (handler_call) {
            conflict = true;
            break;
          }
          handler_call = CI;
        }
        if (conflict)
          break;
      }

      if (conflict || !handler_call)
        continue;

      if (handler_call->arg_size() != 1)
        continue;

      auto *old_pc = llvm::dyn_cast<llvm::ConstantInt>(handler_call->getArgOperand(0));
      if (!old_pc)
        continue;

      if (!F.hasFnAttribute(kOriginalTargetAttr))
        F.addFnAttr(kOriginalTargetAttr, llvm::utohexstr(old_pc->getZExtValue()));

      handler_call->setArgOperand(
          0, llvm::ConstantInt::get(old_pc->getType(), canonical_pc));
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

struct AnnotateTerminalBoundaryHandlersPass
    : llvm::PassInfoMixin<AnnotateTerminalBoundaryHandlersPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    static const bool debug_terminal_boundaries =
        (std::getenv("OMILL_DEBUG_TERMINAL_BOUNDARIES") != nullptr);
    static constexpr llvm::StringLiteral kNamedMetadata =
        "omill.terminal_boundaries";
    static constexpr llvm::StringLiteral kCallMetadata =
        "omill.terminal_boundary";
    static constexpr llvm::StringLiteral kCountAttr =
        "omill.terminal_boundary_count";
    static constexpr llvm::StringLiteral kSummaryAttr =
        "omill.terminal_boundary_summary";
    static constexpr llvm::StringLiteral kKindAttr =
        "omill.terminal_boundary_kind";
    static constexpr llvm::StringLiteral kTargetAttr =
        "omill.terminal_boundary_target_va";
    static constexpr llvm::StringLiteral kNearbyAttr =
        "omill.terminal_boundary_nearby_entry_va";

    if (auto *old_md = M.getNamedMetadata(kNamedMetadata))
      M.eraseNamedMetadata(old_md);

    for (auto &F : M) {
      F.removeFnAttr(kCountAttr);
      F.removeFnAttr(kSummaryAttr);
      F.removeFnAttr(kKindAttr);
      F.removeFnAttr(kTargetAttr);
      F.removeFnAttr(kNearbyAttr);
    }

    const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);
    auto &ctx = M.getContext();
    auto *i1_ty = llvm::Type::getInt1Ty(ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto *named_md = M.getOrInsertNamedMetadata(kNamedMetadata);

    llvm::DenseMap<llvm::Function *,
                   llvm::SmallVector<TerminalBoundaryClassification, 4>>
        classifications_by_function;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__omill_missing_block_handler")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(0));
          if (!pc_arg)
            continue;

          auto info = classifyTerminalBoundaryTarget(M, binary_memory,
                                                     pc_arg->getZExtValue());
          classifications_by_function[&F].push_back(info);

          llvm::SmallVector<llvm::Metadata *, 12> fields;
          fields.push_back(llvm::MDString::get(ctx, "kind"));
          fields.push_back(llvm::MDString::get(ctx, info.kind));
          fields.push_back(llvm::MDString::get(ctx, "target_pc"));
          fields.push_back(llvm::ConstantAsMetadata::get(
              llvm::ConstantInt::get(i64_ty, info.target_pc)));
          fields.push_back(llvm::MDString::get(ctx, "in_image"));
          fields.push_back(llvm::ConstantAsMetadata::get(
              llvm::ConstantInt::get(i1_ty, info.in_image)));
          fields.push_back(llvm::MDString::get(ctx, "mapped"));
          fields.push_back(llvm::ConstantAsMetadata::get(
              llvm::ConstantInt::get(i1_ty, info.mapped)));
          fields.push_back(llvm::MDString::get(ctx, "executable"));
          fields.push_back(llvm::ConstantAsMetadata::get(
              llvm::ConstantInt::get(i1_ty, info.executable)));
          if (info.decodable_entry.has_value()) {
            fields.push_back(llvm::MDString::get(ctx, "decodable_entry"));
            fields.push_back(llvm::ConstantAsMetadata::get(
                llvm::ConstantInt::get(i1_ty, *info.decodable_entry)));
          }
          if (info.nearby_entry_pc.has_value()) {
            fields.push_back(llvm::MDString::get(ctx, "nearby_entry_pc"));
            fields.push_back(llvm::ConstantAsMetadata::get(
                llvm::ConstantInt::get(i64_ty, *info.nearby_entry_pc)));
          }

          auto *call_md = llvm::MDTuple::get(ctx, fields);
          call->setMetadata(kCallMetadata, call_md);

          named_md->addOperand(llvm::MDTuple::get(
              ctx, {llvm::MDString::get(ctx, F.getName()),
                    llvm::ConstantAsMetadata::get(
                        llvm::ConstantInt::get(i64_ty, info.target_pc)),
                    llvm::MDString::get(ctx, info.kind)}));

          if (debug_terminal_boundaries) {
            llvm::errs() << "[terminal-boundary] caller=" << F.getName()
                         << " target=0x" << llvm::Twine::utohexstr(info.target_pc)
                         << " kind=" << info.kind;
            if (info.nearby_entry_pc.has_value())
              llvm::errs() << " nearby=0x"
                           << llvm::Twine::utohexstr(*info.nearby_entry_pc);
            llvm::errs() << "\n";
          }
        }
      }
    }

    if (named_md->getNumOperands() == 0) {
      M.eraseNamedMetadata(named_md);
      return llvm::PreservedAnalyses::all();
    }

    for (auto &[F, infos] : classifications_by_function) {
      F->addFnAttr(kCountAttr, std::to_string(infos.size()));

      llvm::SmallVector<std::string, 4> summary_parts;
      summary_parts.reserve(infos.size());
      for (const auto &info : infos) {
        auto entry = std::string("0x") + llvm::utohexstr(info.target_pc) + ":" +
                     info.kind;
        if (info.nearby_entry_pc.has_value())
          entry += "@0x" + llvm::utohexstr(*info.nearby_entry_pc);
        summary_parts.push_back(std::move(entry));
      }
      F->addFnAttr(kSummaryAttr, llvm::join(summary_parts, ","));

      const auto &first = infos.front();
      const bool unique_target = llvm::all_of(
          infos, [&](const TerminalBoundaryClassification &info) {
            return info.target_pc == first.target_pc;
          });
      const bool uniform_kind = llvm::all_of(
          infos, [&](const TerminalBoundaryClassification &info) {
            return info.kind == first.kind;
          });
      const bool uniform_nearby = llvm::all_of(
          infos, [&](const TerminalBoundaryClassification &info) {
            return info.nearby_entry_pc == first.nearby_entry_pc;
          });

      if (unique_target) {
        F->addFnAttr(kTargetAttr, llvm::utohexstr(first.target_pc));
        if (uniform_kind)
          F->addFnAttr(kKindAttr, first.kind);
        if (uniform_nearby && first.nearby_entry_pc.has_value()) {
          F->addFnAttr(kNearbyAttr, llvm::utohexstr(*first.nearby_entry_pc));
        }
      }
    }

    return llvm::PreservedAnalyses::none();
  }

  static bool isRequired() { return true; }
};

static std::optional<uint64_t> parseTerminalBoundaryTargetAttr(
    const llvm::Function &F) {
  auto attr = F.getFnAttribute("omill.terminal_boundary_target_va");
  if (!attr.isValid())
    return std::nullopt;
  uint64_t target_pc = 0;
  if (attr.getValueAsString().getAsInteger(16, target_pc))
    return std::nullopt;
  return target_pc;
}

static std::optional<uint64_t> parseTerminalBoundaryFunctionPC(
    const llvm::Function &F) {
  if (uint64_t va = extractEntryVA(F.getName()))
    return va;
  if (auto pc = parseSyntheticBlockLikePC(F.getName()))
    return *pc;
  return std::nullopt;
}

static std::string joinTerminalBoundaryCyclePCs(
    llvm::ArrayRef<uint64_t> cycle_pcs) {
  llvm::SmallVector<std::string, 8> parts;
  parts.reserve(cycle_pcs.size());
  for (uint64_t pc : cycle_pcs)
    parts.push_back(llvm::utohexstr(pc));
  return llvm::join(parts, ",");
}

struct AnnotateTerminalBoundaryCyclesPass
    : llvm::PassInfoMixin<AnnotateTerminalBoundaryCyclesPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    static constexpr llvm::StringLiteral kNamedMetadata =
        "omill.terminal_boundary_cycles";
    static constexpr llvm::StringLiteral kCycleAttr =
        "omill.terminal_boundary_cycle";
    static constexpr llvm::StringLiteral kCycleLenAttr =
        "omill.terminal_boundary_cycle_len";
    static constexpr llvm::StringLiteral kCycleCanonicalAttr =
        "omill.terminal_boundary_cycle_canonical_target_va";

    if (auto *old_md = M.getNamedMetadata(kNamedMetadata))
      M.eraseNamedMetadata(old_md);

    for (auto &F : M) {
      F.removeFnAttr(kCycleAttr);
      F.removeFnAttr(kCycleLenAttr);
      F.removeFnAttr(kCycleCanonicalAttr);
    }

    struct NodeInfo {
      std::optional<uint64_t> target_pc;
      bool ambiguous = false;
      llvm::SmallVector<llvm::Function *, 4> funcs;
    };

    llvm::DenseMap<uint64_t, NodeInfo> nodes;
    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      auto entry_pc = parseTerminalBoundaryFunctionPC(F);
      auto target_pc = parseTerminalBoundaryTargetAttr(F);
      if (!entry_pc || !target_pc)
        continue;

      auto &node = nodes[*entry_pc];
      node.funcs.push_back(&F);
      if (!node.target_pc.has_value()) {
        node.target_pc = *target_pc;
      } else if (*node.target_pc != *target_pc) {
        node.ambiguous = true;
      }
    }

    llvm::DenseSet<uint64_t> annotated_cycle_nodes;
    auto *named_md = M.getOrInsertNamedMetadata(kNamedMetadata);
    auto &ctx = M.getContext();
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    bool changed = false;

    for (const auto &[start_pc, node] : nodes) {
      if (annotated_cycle_nodes.contains(start_pc) || node.ambiguous ||
          !node.target_pc.has_value())
        continue;

      llvm::SmallVector<uint64_t, 8> path;
      llvm::DenseMap<uint64_t, unsigned> path_index;
      uint64_t current_pc = start_pc;

      while (true) {
        if (annotated_cycle_nodes.contains(current_pc))
          break;

        auto it = nodes.find(current_pc);
        if (it == nodes.end() || it->second.ambiguous ||
            !it->second.target_pc.has_value()) {
          break;
        }

        auto [pos_it, inserted] = path_index.try_emplace(current_pc, path.size());
        if (!inserted) {
          llvm::SmallVector<uint64_t, 8> cycle_pcs;
          for (unsigned i = pos_it->second; i < path.size(); ++i)
            cycle_pcs.push_back(path[i]);
          if (cycle_pcs.empty())
            break;

          auto min_it = llvm::min_element(cycle_pcs);
          std::rotate(cycle_pcs.begin(), min_it, cycle_pcs.end());
          const std::string cycle_attr = joinTerminalBoundaryCyclePCs(cycle_pcs);
          const uint64_t canonical_pc = cycle_pcs.front();

          llvm::SmallVector<llvm::Metadata *, 12> md_fields;
          md_fields.push_back(
              llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(i64_ty,
                                                                   canonical_pc)));
          md_fields.push_back(
              llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(i64_ty,
                                                                   cycle_pcs.size())));
          for (uint64_t pc : cycle_pcs) {
            annotated_cycle_nodes.insert(pc);
            md_fields.push_back(llvm::ConstantAsMetadata::get(
                llvm::ConstantInt::get(i64_ty, pc)));
            auto cycle_node_it = nodes.find(pc);
            if (cycle_node_it == nodes.end())
              continue;
            for (auto *F : cycle_node_it->second.funcs) {
              F->addFnAttr(kCycleAttr, cycle_attr);
              F->addFnAttr(kCycleLenAttr, std::to_string(cycle_pcs.size()));
              F->addFnAttr(kCycleCanonicalAttr, llvm::utohexstr(canonical_pc));
            }
          }

          named_md->addOperand(llvm::MDTuple::get(ctx, md_fields));
          changed = true;
          break;
        }

        path.push_back(current_pc);
        current_pc = *it->second.target_pc;
      }
    }

    if (!changed) {
      M.eraseNamedMetadata(named_md);
      return llvm::PreservedAnalyses::all();
    }

    return llvm::PreservedAnalyses::none();
  }

  static bool isRequired() { return true; }
};

}  // namespace

void buildCleanupPipeline(llvm::FunctionPassManager &FPM,
                          CleanupProfile profile) {
  switch (profile) {
    case CleanupProfile::kLightScalar:
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::DCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      break;
    case CleanupProfile::kLightScalarNoInstCombine:
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

static bool useRecoveryFirstPipeline(const PipelineOptions &opts) {
  return opts.generic_static_devirtualize || opts.use_block_lifting ||
         opts.no_abi_mode;
}

static bool allowDestructiveCleanup(const PipelineOptions &opts,
                                    RecoveryPipelinePhase phase) {
  return !useRecoveryFirstPipeline(opts) ||
         phase == RecoveryPipelinePhase::kCollapse;
}

static void buildRecoveryAwareCleanupPipeline(llvm::FunctionPassManager &FPM,
                                              CleanupProfile profile,
                                              const PipelineOptions &opts,
                                              RecoveryPipelinePhase phase) {
  if (allowDestructiveCleanup(opts, phase)) {
    buildCleanupPipeline(FPM, profile);
    return;
  }

  switch (profile) {
    case CleanupProfile::kLightScalar:
    case CleanupProfile::kLightScalarNoInstCombine:
    case CleanupProfile::kBoundary:
      FPM.addPass(llvm::SimplifyCFGPass());
      break;
    case CleanupProfile::kStateToSSA:
      FPM.addPass(llvm::EarlyCSEPass());
      break;
    case CleanupProfile::kPostInline:
      FPM.addPass(RecoverAllocaPointersPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      break;
    case CleanupProfile::kFinal:
      break;
  }
}

static void addRecoveryAwareGlobalDCE(llvm::ModulePassManager &MPM,
                                      const PipelineOptions &opts,
                                      RecoveryPipelinePhase phase) {
  if (allowDestructiveCleanup(opts, phase))
    MPM.addPass(llvm::GlobalDCEPass());
}

void buildIntrinsicLoweringPipeline(llvm::FunctionPassManager &FPM,
                                    bool conservative_cleanup) {
  // Order matters: flags first (expose SSA values), barriers (unblock opts),
  // then memory (biggest IR change), atomics, hypercalls.
  FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase1));

  // Recovery-first default: keep only structural cleanup this early.
  (void)conservative_cleanup;
  FPM.addPass(llvm::SimplifyCFGPass());
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

  // Recovery-first default: expose simple redundancy without collapsing
  // State/VM evidence before continuation recovery converges.
  (void)deobfuscate;
  FPM.addPass(llvm::EarlyCSEPass());
}

void buildControlFlowPipeline(llvm::FunctionPassManager &FPM,
                              bool use_block_lifting) {
  if (!envDisabled("OMILL_SKIP_CF_PHASE3_LOWER")) {
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase3));
  }
  // GVN + InstCombine after LowerJump: GVN forwards stores to State GEP
  // loads (e.g. R10D base register in jump table patterns), enabling
  // RecoverTables to match dispatch_jump targets that reference State
  // registers.  InstCombine propagates the forwarded constants.
  // Recover table-based dispatch_jump targets while fallback blocks still
  // have the canonical unresolved-jump "call dispatcher; ret" shape produced by
  // Phase 3 lowering. Later CFG cleanup can obscure this pattern.
  if (!envDisabled("OMILL_SKIP_CF_EARLY_RESOLVE_TABLES")) {
    auto phases = ResolvePhases::RecoverTables | ResolvePhases::SymbolicSolve;
    if (!use_block_lifting)
      phases = phases | ResolvePhases::ResolveTargets;
    FPM.addPass(ResolveAndLowerControlFlowPass(phases));
  }
  if (!envDisabled("OMILL_SKIP_CF_CFG_RECOVERY")) {
    FPM.addPass(CFGRecoveryPass());
  }

  if (!envDisabled("OMILL_SKIP_ELIMINATE_DEAD_PATHS")) {
    FPM.addPass(EliminateDeadPathsPass());
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

struct MarkReachableClosedRootSliceFunctionsPass
    : llvm::PassInfoMixin<MarkReachableClosedRootSliceFunctionsPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    if (!isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();
    bool changed = markReachableClosedRootSliceFunctions(M);
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

struct RebuildClosedRootSliceCodeScopePass
    : llvm::PassInfoMixin<RebuildClosedRootSliceCodeScopePass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = rebuildClosedRootSliceCodeScope(M);
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

struct RebuildOutputRootClosureCodeScopePass
    : llvm::PassInfoMixin<RebuildOutputRootClosureCodeScopePass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = rebuildOutputRootClosureCodeScope(M);
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};


struct RebuildLargeNoAbiStateOptimizationScopePass
    : llvm::PassInfoMixin<RebuildLargeNoAbiStateOptimizationScopePass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = rebuildLargeNoAbiStateOptimizationScope(M);
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};


struct LargeNoAbiScopedAlwaysInlinerPass
    : llvm::PassInfoMixin<LargeNoAbiScopedAlwaysInlinerPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    constexpr unsigned kLargeLiftedFunctionThreshold = 512;
    if (!isNoABIModeModule(M) ||
        countLiftedPipelineFunctions(M) < kLargeLiftedFunctionThreshold) {
      return llvm::AlwaysInlinerPass().run(M, MAM);
    }

    llvm::SmallVector<llvm::Function *, 16> reachable_list;
    collectReachableOutputRootFunctions(M, reachable_list);
    if (reachable_list.empty())
      return llvm::PreservedAnalyses::all();

    llvm::DenseSet<llvm::Function *> reachable(reachable_list.begin(),
                                               reachable_list.end());
    bool changed = false;
    bool did_inline = true;
    while (did_inline) {
      did_inline = false;
      for (auto *F : reachable_list) {
        if (!F || F->isDeclaration() || !reachable.contains(F))
          continue;

        llvm::SmallVector<llvm::CallInst *, 16> calls_to_inline;
        for (auto &BB : *F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = CI->getCalledFunction();
            if (!callee || callee->isDeclaration() || callee == F)
              continue;
            const bool callee_always_inline =
                callee->hasFnAttribute(llvm::Attribute::AlwaysInline);
            const bool site_always_inline =
                CI->hasFnAttr(llvm::Attribute::AlwaysInline);
            if (!callee_always_inline && !site_always_inline)
              continue;
            calls_to_inline.push_back(CI);
          }
        }

        for (auto *CI : calls_to_inline) {
          llvm::InlineFunctionInfo IFI;
          auto result = llvm::InlineFunction(*CI, IFI);
          if (result.isSuccess()) {
            did_inline = true;
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


struct NoAbiPostCleanupMaterializationPass
    : llvm::PassInfoMixin<NoAbiPostCleanupMaterializationPass> {
  explicit NoAbiPostCleanupMaterializationPass(bool verify = false)
      : verify_materialization(verify) {}

  bool verify_materialization = false;

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    if (!hasClosedRootSlicePostCleanupMaterializationWork(M))
      return llvm::PreservedAnalyses::all();

    llvm::ModulePassManager PM;
    PM.addPass(RebuildClosedRootSliceCodeScopePass{});
    PM.addPass(
        llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(ConstantMemoryFoldingPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::InstCombinePass());
      PM.addPass(createScopedFPM(std::move(FPM),
                                 shouldRunClosedRootSliceCodeBearingPass));
    }
    if (verify_materialization)
      PM.addPass(VerifiedVirtualCFGMaterializationPass());
    else
      PM.addPass(VirtualCFGMaterializationPass());
    PM.addPass(RebuildClosedRootSliceCodeScopePass{});
    PM.addPass(CollapseSyntheticBlockContinuationCallsPass(
        /*rewrite_to_missing_block=*/true,
        /*only_when_noabi_mode=*/true));
    PM.addPass(
        RewriteConstantMissingBlockCallsPass(/*only_when_noabi_mode=*/true));
    PM.addPass(llvm::GlobalDCEPass());
    PM.addPass(RebuildClosedRootSliceCodeScopePass{});
    PM.run(M, MAM);
    return llvm::PreservedAnalyses::none();
  }
  static bool isRequired() { return true; }
};

bool runClosedRootSliceContinuationCollapse(llvm::Module &M,
                                            llvm::ModuleAnalysisManager &MAM,
                                            bool debug_late_closure) {
  if (!isClosedRootSliceScopedModule(M))
    return false;

  const unsigned before_remaining =
      countClosedRootSliceDeclaredContinuationCalls(M);

  llvm::ModulePassManager CollapseMPM;
  CollapseMPM.addPass(MergeBlockFunctionsPass());
  CollapseMPM.addPass(llvm::GlobalDCEPass());
  CollapseMPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
  CollapseMPM.addPass(MarkClosedRootSliceHelpersForInliningPass());
  CollapseMPM.addPass(RepairBeforeInlinePass{});
  if (alwaysInlinerEnabled())
    CollapseMPM.addPass(llvm::AlwaysInlinerPass());
  CollapseMPM.addPass(llvm::GlobalDCEPass());
  {
    llvm::FunctionPassManager FPM;
    buildCleanupPipeline(FPM, CleanupProfile::kBoundary);
    CollapseMPM.addPass(createScopedFPM(std::move(FPM),
                                        shouldRunClosedRootSliceScopedPass));
  }
  CollapseMPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
  CollapseMPM.addPass(llvm::GlobalDCEPass());
  CollapseMPM.run(M, MAM);

  const unsigned after_remaining =
      countClosedRootSliceDeclaredContinuationCalls(M);
  if (debug_late_closure)
    llvm::errs() << "[late-closure] collapse remaining_calls "
                 << before_remaining << " -> " << after_remaining << "\n";
  return before_remaining != after_remaining;
}

struct LateClosedRootSliceContinuationClosurePass
    : llvm::PassInfoMixin<LateClosedRootSliceContinuationClosurePass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM) {
    const bool debug_late_closure =
        (std::getenv("OMILL_DEBUG_LATE_CLOSED_SLICE_CONTINUATION") != nullptr);
    if (debug_late_closure)
      llvm::errs() << "[late-closure] entered\n";
    if (debug_late_closure) {
      for (auto &F : M) {
        if (!F.getName().ends_with("_native"))
          continue;
        llvm::errs() << "[late-closure] native fn " << F.getName()
                     << " decl=" << F.isDeclaration()
                     << " closed=" << isClosedRootSliceFunction(F) << "\n";
      }
    }
    if (!isClosedRootSliceScopedModule(M))
      return llvm::PreservedAnalyses::all();

    auto lift_block = MAM.getResult<BlockLiftAnalysis>(M).lift_block;
    if (debug_late_closure)
      llvm::errs() << "[late-closure] has_lift_block="
                   << static_cast<bool>(lift_block) << "\n";
    if (!lift_block)
      return llvm::PreservedAnalyses::all();

    bool changed = markReachableClosedRootSliceFunctions(M);
    unsigned remaining_calls =
        countClosedRootSliceDeclaredContinuationCalls(M);
    constexpr unsigned kMaxSeedContinuationCalls = 32;
    if (debug_late_closure)
      llvm::errs() << "[late-closure] remaining_calls=" << remaining_calls
                   << "\n";
    if (remaining_calls == 0)
      return llvm::PreservedAnalyses::all();
    if (remaining_calls > kMaxSeedContinuationCalls) {
      if (debug_late_closure) {
        llvm::errs() << "[late-closure] skipping: continuation frontier "
                     << remaining_calls << " exceeds seed budget "
                     << kMaxSeedContinuationCalls << "\n";
      }
      return changed ? llvm::PreservedAnalyses::none()
                     : llvm::PreservedAnalyses::all();
    }

    unsigned total_lifted = 0;
    constexpr unsigned kMaxRounds = 8;
    constexpr unsigned kMaxContinuationBlocks = 128;

    for (unsigned round = 0;
         round < kMaxRounds && remaining_calls != 0; ++round) {
      llvm::SmallVector<uint64_t, 16> pcs;
      collectClosedRootSliceContinuationPCs(M, pcs);
      if (debug_late_closure) {
        llvm::errs() << "[late-closure] round=" << round
                     << " pcs=" << pcs.size() << "\n";
      }
      if (pcs.empty())
        break;

      bool round_changed = false;
      bool lifted_any = false;

      for (uint64_t pc : pcs) {
        auto *target = findSyntheticBlockLikeDefinition(M, pc);
        if (!target) {
          if (debug_late_closure)
            llvm::errs() << "[late-closure] lifting pc=0x"
                         << llvm::utohexstr(pc) << "\n";
          if (total_lifted >= kMaxContinuationBlocks)
            break;
          if (!lift_block(pc))
            continue;
          ++total_lifted;
          lifted_any = true;
          target = findSyntheticBlockLikeDefinition(M, pc);
        }

        if (!target)
          continue;
        round_changed |= markClosedRootSliceContinuationFunction(*target);
      }

      round_changed |= markReachableClosedRootSliceFunctions(M);
      if (round_changed || lifted_any) {
        round_changed |= runClosedRootSliceContinuationCollapse(
            M, MAM, debug_late_closure);
      }

      if (!round_changed && !lifted_any)
        break;

      changed = true;
      unsigned next_remaining =
          countClosedRootSliceDeclaredContinuationCalls(M);
      if (next_remaining >= remaining_calls && !lifted_any)
        break;
      remaining_calls = next_remaining;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};

}  // namespace

bool moduleHasGenericStaticDevirtualizationCandidates(const llvm::Module &M) {
  return moduleHasGenericStaticDevirtualizationCandidatesImpl(M);
}

bool moduleHasRootLocalGenericStaticDevirtualizationShape(
    const llvm::Module &M) {
  return moduleHasRootLocalGenericStaticDevirtualizationShapeImpl(M);
}

bool shouldAutoSkipGenericStaticDevirtualizationForRoot(
    const llvm::Module &M, bool vm_mode, bool requested_root_is_export,
    bool force_generic_static_devirtualize,
    bool root_local_generic_static_devirtualization_shape) {
  if (vm_mode || force_generic_static_devirtualize ||
      root_local_generic_static_devirtualization_shape) {
    if (force_generic_static_devirtualize ||
        root_local_generic_static_devirtualization_shape) {
      return false;
    }
  }
  if (requested_root_is_export)
    return true;
  return !moduleHasGenericStaticDevirtualizationCandidatesImpl(M);
}

bool shouldUseStableNoGsdExportRootFallback(
    bool vm_mode, bool requested_root_is_export, bool use_block_lifting,
    bool generic_static_devirtualize_requested,
    bool force_generic_static_devirtualize,
    uint64_t largest_executable_section_size) {
  constexpr uint64_t kLargeExecutableSectionBytes = 1ull << 20;
  return !vm_mode && requested_root_is_export && use_block_lifting &&
         generic_static_devirtualize_requested &&
         !force_generic_static_devirtualize &&
         largest_executable_section_size >= kLargeExecutableSectionBytes;
}

bool shouldUseFastPlainExportRootFallback(
    bool vm_mode, bool requested_root_is_export, bool use_block_lifting,
    bool generic_static_devirtualize_requested,
    bool force_generic_static_devirtualize,
    uint64_t largest_executable_section_size,
    uint64_t executable_section_count) {
  constexpr uint64_t kSmallExecutableSectionBytes = 256ull << 10;
  return !vm_mode && requested_root_is_export && use_block_lifting &&
         generic_static_devirtualize_requested &&
         !force_generic_static_devirtualize &&
         executable_section_count <= 1 &&
         largest_executable_section_size <= kSmallExecutableSectionBytes;
}

bool shouldAutoSkipAlwaysInlineForRoot(
    bool vm_mode, bool requested_root_is_export,
    bool generic_static_devirtualize_requested,
    bool generic_static_devirtualize_enabled,
    bool root_local_generic_static_devirtualization_shape) {
  return !vm_mode &&
         !requested_root_is_export &&
         !root_local_generic_static_devirtualization_shape &&
         generic_static_devirtualize_requested &&
         !generic_static_devirtualize_enabled;
}

llvm::StringRef terminalBoundaryRecoveryStatusName(
    TerminalBoundaryRecoveryStatus status) {
  switch (status) {
    case TerminalBoundaryRecoveryStatus::kClosedCandidate:
      return "closed_candidate";
    case TerminalBoundaryRecoveryStatus::kVmLikeOpen:
      return "vm_like_open";
    case TerminalBoundaryRecoveryStatus::kLargeOpen:
      return "large_open";
    case TerminalBoundaryRecoveryStatus::kTimeout:
      return "timeout";
    case TerminalBoundaryRecoveryStatus::kImported:
      return "imported";
  }
  return "unknown";
}

TerminalBoundaryRecoveryStatus classifyTerminalBoundaryRecoveryMetrics(
    const TerminalBoundaryRecoveryMetrics &metrics) {
  const uint32_t dispatch_total =
      metrics.dispatch_jump + metrics.dispatch_call;
  if (metrics.declare_blk == 0 && dispatch_total == 0 &&
      metrics.missing_block_handler == 0) {
    return TerminalBoundaryRecoveryStatus::kClosedCandidate;
  }

  if (metrics.define_blk > 2048 || metrics.declare_blk > 512 ||
      metrics.call_blk > 8192 || dispatch_total > 128) {
    return TerminalBoundaryRecoveryStatus::kLargeOpen;
  }

  return TerminalBoundaryRecoveryStatus::kVmLikeOpen;
}

std::string summarizeTerminalBoundaryRecoveryMetrics(
    const TerminalBoundaryRecoveryMetrics &metrics) {
  return ("define_blk=" + llvm::Twine(metrics.define_blk) +
          ",declare_blk=" + llvm::Twine(metrics.declare_blk) +
          ",call_blk=" + llvm::Twine(metrics.call_blk) +
          ",dispatch_jump=" + llvm::Twine(metrics.dispatch_jump) +
          ",dispatch_call=" + llvm::Twine(metrics.dispatch_call) +
          ",missing_block_handler=" +
          llvm::Twine(metrics.missing_block_handler))
      .str();
}

void refreshTerminalBoundaryRecoveryMetadata(llvm::Module &M) {
  static constexpr llvm::StringLiteral kNamedMetadata =
      "omill.terminal_boundary_recoveries";
  static constexpr llvm::StringLiteral kStatusAttr =
      "omill.terminal_boundary_recovery_status";
  static constexpr llvm::StringLiteral kTargetAttr =
      "omill.terminal_boundary_recovery_target_va";
  static constexpr llvm::StringLiteral kSummaryAttr =
      "omill.terminal_boundary_recovery_summary";

  if (auto *old_md = M.getNamedMetadata(kNamedMetadata))
    M.eraseNamedMetadata(old_md);

  auto *named_md = M.getOrInsertNamedMetadata(kNamedMetadata);
  auto &ctx = M.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;

    auto status_attr = F.getFnAttribute(kStatusAttr);
    if (!status_attr.isValid())
      continue;

    llvm::SmallVector<llvm::Metadata *, 4> fields;
    fields.push_back(llvm::MDString::get(ctx, F.getName()));
    fields.push_back(
        llvm::MDString::get(ctx, status_attr.getValueAsString()));

    uint64_t target_pc = 0;
    auto target_attr = F.getFnAttribute(kTargetAttr);
    if (target_attr.isValid() &&
        !target_attr.getValueAsString().getAsInteger(16, target_pc) &&
        target_pc != 0) {
      fields.push_back(llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(i64_ty, target_pc)));
    } else {
      fields.push_back(llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(i64_ty, 0)));
    }

    auto summary_attr = F.getFnAttribute(kSummaryAttr);
    fields.push_back(llvm::MDString::get(
        ctx, summary_attr.isValid() ? summary_attr.getValueAsString() : ""));
    named_md->addOperand(llvm::MDTuple::get(ctx, fields));
  }

  if (named_md->getNumOperands() == 0)
    M.eraseNamedMetadata(named_md);
}

void buildABIRecoveryPipeline(llvm::ModulePassManager &MPM,
                              const PipelineOptions &) {
  addPhaseMarker(MPM, "ABI: start");
  MPM.addPass(EraseDeadTrivialSelfLoopPlaceholderCallsPass());
  addPhaseMarker(MPM, "ABI: direct canonical export shaping");
  MPM.addPass(DirectABIShapingPass());
  MPM.addPass(CanonicalizeABIBoundaryDeclarationsPass());
  MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass());
  MPM.addPass(MarkClosedRootSliceSemanticHelpersForInliningPass());
  MPM.addPass(MarkClosedRootSliceHelpersForInliningPass());
  MPM.addPass(RepairBeforeInlinePass{});
  MPM.addPass(llvm::AlwaysInlinerPass());
  llvm::InlineParams abi_inline_params = llvm::getInlineParams(100);
  MPM.addPass(llvm::ModuleInlinerWrapperPass(abi_inline_params));
  MPM.addPass(NeutralizeInlinedFunctionReturnsPass{});
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(LowerRemillIntrinsicsPass(
        LowerCategories::Phase1 | LowerCategories::ResolvedDispatch));
    FPM.addPass(CombinedFixedPointDevirtPass());
    FPM.addPass(MemoryPointerEliminationPass());
    FPM.addPass(RecoverStackFramePass());
    FPM.addPass(RecoverStackFrameTypesPass());
    FPM.addPass(TypeRecoveryPass());
    buildCleanupPipeline(FPM, CleanupProfile::kPostInline);
    FPM.addPass(EliminateDeadTraceCountersPass());
    FPM.addPass(CombinedFixedPointDevirtPass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(
        createScopedFPM(std::move(FPM), shouldRunClosedRootSliceScopedPass));
  }
  MPM.addPass(CanonicalizeABIBoundaryDeclarationsPass());
  // ABI shaping can still leave helper-closure missing-block handlers around
  // internal output-root helpers. Rewrite those to stable executable targets
  // first, then run one more helper cleanup epoch over the now-stable closure.
  MPM.addPass(RewriteExecutableBoundaryHandlerCallsPass{});
  MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass());
  MPM.addPass(MarkClosedRootSliceSemanticHelpersForInliningPass());
  MPM.addPass(RepairBeforeInlinePass{});
  MPM.addPass(llvm::AlwaysInlinerPass());
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(LowerRemillIntrinsicsPass(
        LowerCategories::Phase1 | LowerCategories::ResolvedDispatch));
    FPM.addPass(CombinedFixedPointDevirtPass());
    buildCleanupPipeline(FPM, CleanupProfile::kPostInline);
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(
        createScopedFPM(std::move(FPM), shouldRunClosedRootSliceScopedPass));
  }
  MPM.addPass(InternalizeDeadLiftedHelpersPass());
  MPM.addPass(llvm::GlobalDCEPass());
  addClosedSliceShapeProbe(MPM, "abi-direct-post-gdce");
}

#if 0  // Legacy _native ABI pipeline removed in favor of direct canonical ABI shaping.
namespace {

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

    MPM.addPass(SeedTerminalSyntheticBoundaryCandidatesPass{});

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
            if (shouldPreserveOutlinedWrapper(F, &virtual_callees)) {
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
      MPM.addPass(CanonicalizeMutualRecursiveNativeBlockHelpersPass{});
      MPM.addPass(ForceInlineSingleCallerCommonContinuationNativeHelpersPass{});
      MPM.addPass(LoopifySelfRecursiveNativeBlockHelpersPass{});
      MPM.addPass(PropagateLoopifiedTerminalBoundaryAttrsPass{});
      MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
      MPM.addPass(EraseIsolatedSyntheticBlockWrapperCallsPass{});
      MPM.addPass(MarkOutputRootNativeHelpersForInliningPass());
      MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass());
      MPM.addPass(MarkClosedRootSliceNativeHelpersForInliningPass());
      MPM.addPass(MarkClosedRootSliceSemanticHelpersForInliningPass());
      MPM.addPass(RepairBeforeInlinePass{});
      if (abiAlwaysInlinerEnabled())
        MPM.addPass(llvm::AlwaysInlinerPass());
      if (moduleInlinerEnabled()) {
        llvm::InlineParams params = llvm::getInlineParams(50);
        MPM.addPass(llvm::ModuleInlinerWrapperPass(params));
      }
      MPM.addPass(NeutralizeInlinedFunctionReturnsPass{});
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      }
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(LowerRemillIntrinsicsPass(
            LowerCategories::Flags | LowerCategories::Barriers |
            LowerCategories::Memory | LowerCategories::Atomics |
            LowerCategories::HyperCalls | LowerCategories::ErrorMissing |
            LowerCategories::Undefined));
        if (!envDisabled("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE"))
          FPM.addPass(DeadStateStoreDSEPass());
        if (!envDisabled("OMILL_SKIP_ABI_SROA"))
          FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        MPM.addPass(createScopedFPM(std::move(FPM),
                                    shouldRunClosedRootSliceScopedPass));
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
      if (!envDisabled("OMILL_SKIP_INTERNALIZE_DEAD_NATIVE_HELPERS"))
        MPM.addPass(InternalizeDeadNativeHelpersPass{});
      MPM.addPass(llvm::GlobalDCEPass());

      // A first inline/cleanup round can expose one more shared blk_*_native
      // helper that was not materialized until the earlier wrappers
      // collapsed. Run one bounded second round to flatten that last layer for
      // ordinary output-root cleanup without reopening the full ABI pipeline.
      MPM.addPass(CanonicalizeMutualRecursiveNativeBlockHelpersPass{});
      MPM.addPass(ForceInlineSingleCallerCommonContinuationNativeHelpersPass{});
      MPM.addPass(LoopifySelfRecursiveNativeBlockHelpersPass{});
      MPM.addPass(PropagateLoopifiedTerminalBoundaryAttrsPass{});
      MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
      MPM.addPass(EraseIsolatedSyntheticBlockWrapperCallsPass{});
      MPM.addPass(MarkOutputRootNativeHelpersForInliningPass());
      MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass());
      MPM.addPass(RepairBeforeInlinePass{});
      if (abiAlwaysInlinerEnabled())
        MPM.addPass(llvm::AlwaysInlinerPass());
      if (moduleInlinerEnabled()) {
        llvm::InlineParams second_params = llvm::getInlineParams(50);
        MPM.addPass(llvm::ModuleInlinerWrapperPass(second_params));
      }
      MPM.addPass(NeutralizeInlinedFunctionReturnsPass{});
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(LowerRemillIntrinsicsPass(
            LowerCategories::Flags | LowerCategories::Barriers |
            LowerCategories::Memory | LowerCategories::Atomics |
            LowerCategories::HyperCalls | LowerCategories::ErrorMissing |
            LowerCategories::Undefined));
        if (!envDisabled("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE"))
          FPM.addPass(DeadStateStoreDSEPass());
        if (!envDisabled("OMILL_SKIP_ABI_SROA"))
          FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(llvm::ADCEPass());
        FPM.addPass(llvm::SimplifyCFGPass());
        MPM.addPass(createScopedFPM(std::move(FPM),
                                    shouldRunClosedRootSliceScopedPass));
      }
      if (!envDisabled("OMILL_SKIP_INTERNALIZE_DEAD_NATIVE_HELPERS"))
        MPM.addPass(InternalizeDeadNativeHelpersPass{});
      MPM.addPass(llvm::GlobalDCEPass());
    }

    if (!envDisabled("OMILL_SKIP_RESOLVE_INTTOPTR_CALLS")) {
      MPM.addPass(llvm::RequireAnalysisPass<LiftedFunctionAnalysis,
                                            llvm::Module>());
      MPM.addPass(ResolveIntToPtrCallsPass{});
    }
    addPhaseMarker(MPM, "ABI: collapse null-memory blk continuations (late)");
    MPM.addPass(CollapseSyntheticBlockContinuationCallsPass(false));
    addPhaseMarker(
        MPM, "ABI: terminalize unresolved blk continuations (late)");
    MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
    MPM.addPass(EraseIsolatedSyntheticBlockWrapperCallsPass{});
    MPM.addPass(CanonicalizeMutualRecursiveNativeBlockHelpersPass{});
    MPM.addPass(ForceInlineSingleCallerCommonContinuationNativeHelpersPass{});
    MPM.addPass(LoopifySelfRecursiveNativeBlockHelpersPass{});
    MPM.addPass(PropagateLoopifiedTerminalBoundaryAttrsPass{});
    MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
    MPM.addPass(MarkOutputRootNativeHelpersForInliningPass());
    MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass());
    MPM.addPass(RepairBeforeInlinePass{});
    if (abiAlwaysInlinerEnabled())
      MPM.addPass(llvm::AlwaysInlinerPass());
    if (moduleInlinerEnabled()) {
      llvm::InlineParams late_output_root_params = llvm::getInlineParams(50);
      MPM.addPass(llvm::ModuleInlinerWrapperPass(late_output_root_params));
    }
    MPM.addPass(NeutralizeInlinedFunctionReturnsPass{});
    {
      llvm::FunctionPassManager FPM;
      if (!envDisabled("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE"))
        FPM.addPass(DeadStateStoreDSEPass());
      if (!envDisabled("OMILL_SKIP_ABI_SROA"))
        FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      MPM.addPass(createScopedFPM(std::move(FPM),
                                  shouldRunClosedRootSliceScopedPass));
    }
    MPM.addPass(llvm::GlobalDCEPass());

    addPhaseMarker(MPM, "ABI: final native helper collapse sweep");
    MPM.addPass(CanonicalizeMutualRecursiveNativeBlockHelpersPass{});
    MPM.addPass(ForceInlineSingleCallerCommonContinuationNativeHelpersPass{});
    MPM.addPass(LoopifySelfRecursiveNativeBlockHelpersPass{});
    MPM.addPass(PropagateLoopifiedTerminalBoundaryAttrsPass{});
    MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
    MPM.addPass(EraseIsolatedSyntheticBlockWrapperCallsPass{});
    MPM.addPass(MarkOutputRootNativeHelpersForInliningPass());
    MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass());
    MPM.addPass(RepairBeforeInlinePass{});
    if (abiAlwaysInlinerEnabled())
      MPM.addPass(llvm::AlwaysInlinerPass());
    if (moduleInlinerEnabled()) {
      llvm::InlineParams final_native_cleanup_params = llvm::getInlineParams(50);
      MPM.addPass(llvm::ModuleInlinerWrapperPass(final_native_cleanup_params));
    }
    MPM.addPass(NeutralizeInlinedFunctionReturnsPass{});
    {
      llvm::FunctionPassManager FPM;
      if (!envDisabled("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE"))
        FPM.addPass(DeadStateStoreDSEPass());
      if (!envDisabled("OMILL_SKIP_ABI_SROA"))
        FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      MPM.addPass(createScopedFPM(std::move(FPM),
                                  shouldRunClosedRootSliceScopedPass));
    }
    MPM.addPass(CanonicalizeMutualRecursiveNativeBlockHelpersPass{});
    MPM.addPass(ForceInlineSingleCallerCommonContinuationNativeHelpersPass{});
    MPM.addPass(LoopifySelfRecursiveNativeBlockHelpersPass{});
    MPM.addPass(PropagateLoopifiedTerminalBoundaryAttrsPass{});
    MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
    MPM.addPass(EraseIsolatedSyntheticBlockWrapperCallsPass{});
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      MPM.addPass(createScopedFPM(std::move(FPM),
                                  shouldRunClosedRootSliceScopedPass));
    }
    MPM.addPass(RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass{});
    MPM.addPass(EraseIsolatedSyntheticBlockWrapperCallsPass{});
    if (!envDisabled("OMILL_SKIP_INTERNALIZE_DEAD_NATIVE_HELPERS"))
      MPM.addPass(InternalizeDeadNativeHelpersPass{});
    MPM.addPass(llvm::GlobalDCEPass());
    MPM.addPass(PropagateTerminalBoundaryAttrsToNativeRootsPass{});
    MPM.addPass(RewriteLoopifiedTerminalBoundaryOutputRootsPass{});
    MPM.addPass(RewriteIndirectCallTerminalBoundaryOutputRootsPass{});
    MPM.addPass(RewriteStateWrapperTerminalBoundaryOutputRootsPass{});
    MPM.addPass(AnnotateTerminalBoundaryHandlersPass{});
    addClosedSliceShapeProbe(MPM, "abi-final");
  }
}

#endif

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
          isSyntheticBlockLikeFunctionName(name) ||
          isSyntheticBlockLikeNativeHelperName(name) ||
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
          isSyntheticBlockLikeFunctionName(name) ||
          isSyntheticBlockLikeNativeHelperName(name) ||
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
          isSyntheticBlockLikeFunctionName(name) ||
          isSyntheticBlockLikeNativeHelperName(name) ||
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
      // Keep lifted/output-root code and remill intrinsics. Late block lifting
      // and generic devirtualization produce real executable helpers under
      // blk_/block_/sub_ and related lifted-function shapes; those are not
      // dead semantics and must survive the semantics cleanup sweep.
      if (isLiftedPipelineFunction(F) || name.starts_with("__remill_") ||
          name.starts_with("vm_entry_") ||
          F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.protection_boundary"))
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
      bool raw_dispatch = false;
      StampTargetArchPass(TargetArch a, std::string o, bool raw_dispatch_names)
          : arch(a), os(std::move(o)), raw_dispatch(raw_dispatch_names) {}
      llvm::PreservedAnalyses run(llvm::Module &M,
                                  llvm::ModuleAnalysisManager &) {
        setTargetArchMetadata(M, arch, os);
        auto *existing = M.getModuleFlag("omill.raw_remill_dispatch");
        auto *existing_ci =
            llvm::mdconst::dyn_extract_or_null<llvm::ConstantInt>(existing);
        const uint32_t desired = raw_dispatch ? 1u : 0u;
        if (!existing_ci || existing_ci->getZExtValue() != desired) {
          M.addModuleFlag(llvm::Module::Override, "omill.raw_remill_dispatch",
                          desired);
        }
        return llvm::PreservedAnalyses::all();
      }
      static llvm::StringRef name() { return "StampTargetArchPass"; }
    };
    MPM.addPass(StampTargetArchPass(arch, os, opts.prefer_raw_remill_dispatch));
  }

  // Phase 0: Strip remill intrinsic bodies to prevent AlwaysInlinerPass from
  // inlining them via call-site alwaysinline attributes.  Their bodies contain
  // switch/unreachable patterns that poison the entire function's control flow.
  MPM.addPass(StripRemillIntrinsicBodiesPass());

  auto addLiftedScopedFPM = [&](llvm::FunctionPassManager FPM) {
    auto lifted_scope = [](llvm::Function &F) {
      if (!isLiftedPipelineFunction(F))
        return false;
      if (isLargeNoAbiGenericStaticScopeModule(*F.getParent())) {
        return F.hasFnAttribute("omill.output_root") ||
               F.hasFnAttribute("omill.internal_output_root") ||
               F.hasFnAttribute("omill.closed_root_slice_root");
      }
      if (isOutputRootClosureScopedModule(*F.getParent()))
        return F.hasFnAttribute("omill.output_root_closure");
      return true;
    };
    if (opts.scope_predicate) {
      auto user_scope = opts.scope_predicate;
      MPM.addPass(createScopedFPM(
          std::move(FPM),
          [lifted_scope, user_scope = std::move(user_scope)](
              llvm::Function &F) mutable {
            return lifted_scope(F) && user_scope(F);
          }));
    } else {
      MPM.addPass(createScopedFPM(std::move(FPM), lifted_scope));
    }
  };

  auto addLiftedStateScopedFPM = [&](llvm::FunctionPassManager FPM) {
    auto state_scope = [](llvm::Function &F) {
      if (!isLiftedPipelineFunction(F))
        return false;
      if (isLargeNoAbiGenericStaticScopeModule(*F.getParent())) {
        return F.hasFnAttribute("omill.output_root") ||
               F.hasFnAttribute("omill.internal_output_root") ||
               F.hasFnAttribute("omill.closed_root_slice_root");
      }
      if (isLargeNoAbiStateOptimizationScopeModule(*F.getParent())) {
        return F.hasFnAttribute("omill.output_root") ||
               F.hasFnAttribute("omill.internal_output_root") ||
               F.hasFnAttribute("omill.closed_root_slice_root");
      }
      if (isOutputRootClosureScopedModule(*F.getParent()))
        return F.hasFnAttribute("omill.output_root_closure");
      return true;
    };
    if (opts.scope_predicate) {
      auto user_scope = opts.scope_predicate;
      MPM.addPass(createScopedFPM(
          std::move(FPM),
          [state_scope, user_scope = std::move(user_scope)](
              llvm::Function &F) mutable {
            return state_scope(F) && user_scope(F);
          }));
    } else {
      MPM.addPass(createScopedFPM(std::move(FPM), state_scope));
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

  // Phase 0.5: Resolve trace stubs and connect jump-table targets discovered
  // during lifting before AlwaysInliner can erase/disconnect named lifted
  // target blocks. This preserves block_<hex> identities long enough to rewrite
  // __remill_jump / __omill_dispatch_jump into local control flow.
  if (!opts.use_block_lifting &&
      !envDisabled("OMILL_SKIP_INLINE_JUMP_TARGETS")) {
    MPM.addPass(InlineJumpTargetsPass());
  }


  // Phase 0: Inline remill's alwaysinline semantic functions so that
  // subsequent passes can see through them.
  MPM.addPass(RepairBeforeInlinePass{});
  if (alwaysInlinerEnabled())
    MPM.addPass(LargeNoAbiScopedAlwaysInlinerPass());

  // Protect semantic function bodies from Phase 2 function-pass optimizations.
  // Phase 3.6 Step 2b restores alwaysinline before inlining into VM handlers.
  MPM.addPass(ProtectRemillSemanticsPass());

  MPM.addPass(RebuildOutputRootClosureCodeScopePass());
  MPM.addPass(RebuildLargeNoAbiStateOptimizationScopePass());


  addPhaseMarker(MPM, "Phase 1: intrinsic lowering");
  // Phase 1: Intrinsic Lowering
  if (opts.lower_intrinsics) {
    llvm::FunctionPassManager FPM;
    buildIntrinsicLoweringPipeline(FPM, opts.use_block_lifting);
    addLiftedScopedFPM(std::move(FPM));
  }

  addPhaseMarker(MPM, "Phase 2: state optimization");
  // Phase 2: State Optimization
  if (opts.optimize_state) {
    if (opts.deobfuscate && !envDisabled("OMILL_SKIP_STATE_MODULE_INLINER")) {
       if (moduleInlinerEnabled()) {
         llvm::InlineParams Params = llvm::getInlineParams(2000); // Aggressive threshold
         MPM.addPass(llvm::ModuleInlinerWrapperPass(Params));
       }
    }

    llvm::FunctionPassManager FPM;
    buildStateOptimizationPipeline(FPM, opts.deobfuscate);
    addLiftedStateScopedFPM(std::move(FPM));
  }

  if (opts.require_remill_normalization) {
    RemillNormalizationOrchestrator normalization;
    normalization.appendToPipeline(
        MPM, RemillNormalizationRequest{
                 RemillNormalizationEpoch::kInitialLift,
                 opts.no_abi_mode,
                 /*aggressive_folding=*/false,
                 opts.scope_predicate});
  }

  // Synthesize flag patterns: after SROA/mem2reg promotes flag values to
  // SSA, recognize xor(SF, OF) patterns and fold to icmp slt.  Follow
  // with InstCombine to fold compound patterns (JGE, JLE, JG).
  if (!envDisabled("OMILL_SKIP_SYNTHESIZE_FLAGS")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(SynthesizeFlagsPass());
    FPM.addPass(llvm::InstCombinePass());
    addLiftedScopedFPM(std::move(FPM));
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
    addLiftedScopedFPM(std::move(FPM));

    // Inline exception handlers into their callers.  This is critical:
    // CFF handlers are trampolines that call resolvers.  Without inlining,
    // ABI recovery creates a native wrapper for the handler that drops XMM
    // values (the handler doesn't use XMMs directly), so the resolver's SSE
    // computation gets all-zero XMM inputs and folds to ret 0.
    // Inlining merges the handler body into the caller (which HAS XMM values),
    // preserving the full State across the call chain.
    if (!envDisabled("OMILL_SKIP_CF_HANDLER_INLINE")) {
      MPM.addPass(RepairBeforeInlinePass{});
      if (alwaysInlinerEnabled())
        MPM.addPass(llvm::AlwaysInlinerPass());
    }
    // Remove inlined handler functions so they don't appear as callers in
    // the call graph, which would prevent InterProceduralConstProp from
    // propagating R9 (synthetic DC address) to the resolver.
    if (!envDisabled("OMILL_SKIP_CF_HANDLER_GDCE")) {
      addRecoveryAwareGlobalDCE(MPM, opts, RecoveryPipelinePhase::kResolve);
    }
  }
  // Phase 3b: Remaining control flow recovery.
  if (opts.lower_control_flow) {
    llvm::FunctionPassManager FPM;
    buildControlFlowPipeline(FPM, opts.use_block_lifting);
    addLiftedScopedFPM(std::move(FPM));
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
    // Default no-ABI/file-backed lifts should resolve constant stack-/state-
    // carried dispatch targets here, not only behind later IPCP epochs.
    if (!opts.use_block_lifting) {
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(IndirectCallResolverPass());
      FPM.addPass(
          ResolveAndLowerControlFlowPass(ResolvePhases::ResolveTargets));
      FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    }
    addLiftedScopedFPM(std::move(FPM));
  }

  // Phase 3.55: Proactive jump table concretization.
  // Runs after Phase 3.5 has folded program_counter and resolved IAT calls,
  // but before iterative target resolution.  Converts dispatch_jump sites
  // with jump table patterns (base + idx * stride loads from binary memory)
  // into switch instructions.
  if (opts.resolve_indirect_targets || opts.use_block_lifting) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(JumpTableConcretizerPass());
    addLiftedScopedFPM(std::move(FPM));
  }

  addPhaseMarker(MPM, "Phase 3.56: VM devirtualization");
  // Phase 3.56: VM Devirtualization.
  // Resolve handler dispatch targets from the emulator-derived flat trace map.
  // Must run after Phase 3 has canonicalized unresolved jump intrinsics
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
  FPM.addPass(CombinedFixedPointDevirtPass());
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
            if (isDispatchIntrinsicName(name))
              return true;
          }
    return false;
  }));
}

static void buildIterativeResolutionEpoch(llvm::ModulePassManager &MPM,
                                          const PipelineOptions &opts) {
  auto addLiftedResolutionScopedFPM = [&](llvm::FunctionPassManager FPM) {
    auto lifted_scope = [](llvm::Function &F) {
      return isLiftedPipelineFunction(F);
    };
    if (opts.scope_predicate) {
      auto user_scope = opts.scope_predicate;
      MPM.addPass(createScopedFPM(
          std::move(FPM),
          [lifted_scope, user_scope = std::move(user_scope)](
              llvm::Function &F) mutable {
            return lifted_scope(F) && user_scope(F);
          }));
    } else {
      MPM.addPass(createScopedFPM(std::move(FPM), lifted_scope));
    }
  };

  addPhaseMarker(MPM, "Phase 3.6: iterative target resolution");
  if (opts.use_block_lifting) {
    MPM.addPass(IterativeBlockDiscoveryPass(opts.max_resolution_iterations));
    // Early non-executable missing-block rewrite: if a
    // __remill_missing_block call targets a constant address in a
    // non-executable section (e.g. .rdata import names from a
    // VMProtect thunk token), convert it to `ret ptr %memory` now —
    // before later passes collapse the enclosing function body to
    // `unreachable` and cascade that upward through the call chain.
    if (!envDisabled("OMILL_SKIP_NONEXEC_MISSING_BLOCK_TO_RET")) {
      MPM.addPass(
          llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
      MPM.addPass(RewriteNonExecutableMissingBlockToRetPass{});
    }
    if (opts.merge_block_functions_after_fixpoint) {
      MPM.addPass(MergeBlockFunctionsPass());
      addRecoveryAwareGlobalDCE(MPM, opts, RecoveryPipelinePhase::kResolve);
      // A first merge can expose additional constant dispatch targets from
      // the merged sub_* bodies that were not visible as stand-alone blocks.
      // Run one more discovery epoch over that merged representation before
      // boundary lowering.
      MPM.addPass(IterativeBlockDiscoveryPass(opts.max_resolution_iterations));
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

  if (opts.require_remill_normalization) {
    RemillNormalizationOrchestrator normalization;
    normalization.appendToPipeline(
        MPM, RemillNormalizationRequest{
                 RemillNormalizationEpoch::kIncrementalRound,
                 opts.no_abi_mode,
                 /*aggressive_folding=*/true,
                 opts.scope_predicate});
  }

  if (opts.generic_static_devirtualize) {
    auto add_closed_root_slice_cleanup = [&](llvm::StringRef phase_name) {
      addPhaseMarker(MPM, phase_name);
      if (opts.no_abi_mode) {
        MPM.addPass(SanitizeModeledBoundaryPoisonMemoryArgsPass{});
        MPM.addPass(RelaxClosedSliceMustTailMissingBlockPass{});
        MPM.addPass(LoopifyClosedSliceSelfRecursiveBlockHelpersPass{});
      }
      MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      if (!envDisabled("OMILL_SKIP_PREINLINE_REWRITE_CONST_MISSING_BLOCK_CALLS"))
        MPM.addPass(RewriteConstantMissingBlockCallsPass(
            /*only_when_noabi_mode=*/opts.no_abi_mode));
      // Mark remill instruction-semantics templates (ADDI/MOVI/CALLI/...) that
      // are reachable from closed-root-slice block helpers as alwaysinline so
      // the upcoming AlwaysInlinerPass can inline them. Late VirtualCFG lifts
      // create new blk_ bodies whose semantic callees are still protected
      // (optnone+noinline) by ProtectRemillSemantics from Phase 0; without
      // this marking step they would survive into the final IR.
      // MarkClosedRootSliceSemanticHelpersForInlining handles small templates
      // (<=96 instrs); MarkLateBlockReachableSemanticHelpers handles the
      // remaining larger ones with no size limit. Both passes are idempotent
      // and skip functions already marked.
      MPM.addPass(MarkClosedRootSliceSemanticHelpersForInliningPass());
      MPM.addPass(MarkLateBlockReachableSemanticHelpersPass());
      MPM.addPass(MarkClosedRootSliceHelpersForInliningPass());
      MPM.addPass(RepairBeforeInlinePass{});
      if (alwaysInlinerEnabled())
        MPM.addPass(llvm::AlwaysInlinerPass());
      // Lower remill memory/flag/atomic/hyper intrinsics that the new
      // semantic-template inlines just exposed in late-lifted blocks.
      // Phase 1 only ran on the initial set of lifted functions; blocks
      // discovered during VirtualCFG materialization (or any later lift)
      // never went through it. Scope to lifted code only and use a
      // function attribute as an idempotency guard so functions already
      // processed are skipped on subsequent invocations.
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(LowerRemillIntrinsicsPass(
            LowerCategories::Phase1 | LowerCategories::ResolvedDispatch));
        FPM.addPass(llvm::SimplifyCFGPass());
        MPM.addPass(createScopedFPM(
            std::move(FPM), [](llvm::Function &F) {
              if (F.isDeclaration())
                return false;
              if (!isLiftedPipelineFunction(F))
                return false;
              if (F.hasFnAttribute("omill.late_intrinsics_lowered"))
                return false;
              // Cheap pre-check: only run when there is at least one
              // remill intrinsic call left in the body. Avoids walking
              // every lifted function on every cleanup invocation.
              for (auto &BB : F) {
                for (auto &I : BB) {
                  auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
                  if (!call)
                    continue;
                  auto *callee = call->getCalledFunction();
                  if (!callee)
                    continue;
                  auto name = callee->getName();
                  if (name.starts_with("__remill_") &&
                      name != "__remill_function_return" &&
                      name != "__remill_function_call" &&
                      name != "__remill_jump" &&
                      name != "__remill_missing_block" &&
                      name != "__remill_error") {
                    F.addFnAttr("omill.late_intrinsics_lowered");
                    return true;
                  }
                }
              }
              return false;
            }));
      }
      // Late dispatch resolution for blocks lifted during Phase 3.8/3.86/3.95.
      // Phase 3.5 already ran FoldProgramCounter + ResolveIATCalls on the
      // initial lifted set, but late-lifted blocks (e.g. created by
      // VirtualCFGMaterializationPass) still carry raw
      //   `%t = add %program_counter, const; %p = inttoptr; %v = load %p;
      //    dispatch_call(state, %v, memory)`
      // patterns for IAT-indirect calls, plus constant dispatch_call/jump
      // targets that would resolve given InstCombine+GVN. Run a scoped
      // equivalent of Phase 3.5 here so those get lowered before
      // CollapseSyntheticBlockContinuationCalls rewrites them into
      // missing-block handlers. Attribute-guarded for idempotency.
      if (!envDisabled("OMILL_SKIP_LATE_BLOCK_DISPATCH_RESOLUTION")) {
        const bool is_windows = isWindowsTargetOS(opts.target_os);
        MPM.addPass(
            llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
        llvm::FunctionPassManager FPM;
        FPM.addPass(FoldProgramCounterPass());
        FPM.addPass(llvm::InstCombinePass());
        if (is_windows)
          FPM.addPass(ResolveIATCallsPass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(IndirectCallResolverPass());
        FPM.addPass(
            ResolveAndLowerControlFlowPass(ResolvePhases::ResolveTargets));
        FPM.addPass(
            LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
        MPM.addPass(createScopedFPM(
            std::move(FPM), [](llvm::Function &F) {
              if (F.isDeclaration())
                return false;
              if (!isLiftedPipelineFunction(F))
                return false;
              if (F.hasFnAttribute("omill.late_dispatch_resolved"))
                return false;
              for (auto &BB : F) {
                for (auto &I : BB) {
                  auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
                  if (!call)
                    continue;
                  auto *callee = call->getCalledFunction();
                  if (!callee)
                    continue;
                  if (isDispatchIntrinsicName(callee->getName())) {
                    F.addFnAttr("omill.late_dispatch_resolved");
                    return true;
                  }
                }
              }
              return false;
            }));
      }
      MPM.addPass(llvm::GlobalDCEPass());
      if (!envDisabled("OMILL_SKIP_POST_CLOSED_SLICE_REACHABILITY_MARK_1"))
        MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      llvm::FunctionPassManager FPM;
      buildRecoveryAwareCleanupPipeline(
          FPM, CleanupProfile::kBoundary, opts,
          RecoveryPipelinePhase::kResolve);
      MPM.addPass(createScopedFPM(std::move(FPM),
                                  shouldRunClosedRootSliceScopedPassOnlyWhenScoped));
      if (!envDisabled("OMILL_SKIP_POST_CLOSED_SLICE_REACHABILITY_MARK_2"))
        MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      if (!envDisabled("OMILL_SKIP_LIFT_CONST_CONTINUATION_DECL_TARGETS"))
        MPM.addPass(LiftConstantContinuationDeclarationTargetsPass());
      if (!opts.skip_closed_slice_missing_block_lift) {
        if (!envDisabled("OMILL_SKIP_LIFT_CONST_MISSING_BLOCK_TARGETS"))
          MPM.addPass(LiftConstantMissingBlockTargetsPass());
      }
      if (!envDisabled("OMILL_SKIP_REWRITE_CONST_MISSING_BLOCK_CALLS"))
        MPM.addPass(RewriteConstantMissingBlockCallsPass());
      if (!envDisabled("OMILL_SKIP_POST_CLOSED_SLICE_REACHABILITY_MARK_3"))
        MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      if (opts.no_abi_mode && enableNoAbiClosedSliceContinuationRelift()) {
        if (opts.verify_generic_static_devirtualization)
          MPM.addPass(
              VerifiedVirtualCFGMaterializationPass(opts.session_graph));
        else
          MPM.addPass(VirtualCFGMaterializationPass(opts.session_graph));
        // After the relift pass materializes new blk_/sub_ bodies, run
        // LiftConstantContinuationDeclarationTargetsPass once more so the
        // direct musttail calls those new bodies make to declared blk_*<pc>
        // continuations get lifted before the rest of the cleanup runs.
        // The pass's per-PC `scheduled` set is local to the pass invocation,
        // so this re-run only attempts targets that were not already in the
        // first pass's view, and the post-main repair loop picks up anything
        // that still cannot be lifted.
        if (!envDisabled("OMILL_SKIP_LIFT_CONST_CONTINUATION_DECL_TARGETS"))
          MPM.addPass(LiftConstantContinuationDeclarationTargetsPass());
      }
      if (!envDisabled("OMILL_SKIP_POST_CLOSED_SLICE_REACHABILITY_MARK_4"))
        MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      MPM.addPass(CollapseSyntheticBlockContinuationCallsPass(
          /*rewrite_to_missing_block=*/true,
          /*only_when_noabi_mode=*/true));
      if (!envDisabled("OMILL_SKIP_REWRITE_CONST_MISSING_BLOCK_CALLS_NOABI"))
        MPM.addPass(
            RewriteConstantMissingBlockCallsPass(/*only_when_noabi_mode=*/true));
      addRecoveryAwareGlobalDCE(MPM, opts, RecoveryPipelinePhase::kResolve);
      if (!envDisabled("OMILL_SKIP_POST_CLOSED_SLICE_REACHABILITY_MARK_5"))
        MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
    };

    addPhaseMarker(MPM, "Phase 3.75: pre-materialization constant memory fold");
    MPM.addPass(
        llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(CombinedFixedPointDevirtPass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::InstCombinePass());
      addLiftedResolutionScopedFPM(std::move(FPM));
    }

    addPhaseMarker(MPM, "Phase 3.8: generic static devirtualization");
    if (opts.require_remill_normalization) {
      RemillNormalizationOrchestrator normalization;
      normalization.appendToPipeline(
          MPM, RemillNormalizationRequest{
                   RemillNormalizationEpoch::kPreMaterialization,
                   opts.no_abi_mode,
                   /*aggressive_folding=*/true,
                   opts.scope_predicate});
    }
    if (!envDisabled("OMILL_SKIP_GENERIC_STATIC_MATERIALIZATION")) {
      if (opts.verify_generic_static_devirtualization)
        MPM.addPass(
            VerifiedVirtualCFGMaterializationPass(opts.session_graph));
      else
        MPM.addPass(VirtualCFGMaterializationPass(opts.session_graph));
    }
    MPM.addPass(DebugPrintSelectedFunctionsPass{});
    addClosedSliceShapeProbe(MPM, "phase3.8");

    if (enableClosedSliceContinuationDiscovery()) {
      addPhaseMarker(MPM, "Phase 3.85: closed root-slice continuation discovery");
      MPM.addPass(LateClosedRootSliceContinuationClosurePass{});
      addClosedSliceShapeProbe(MPM, "phase3.85");

      // Continuation discovery can lift new blk_*/sub_* bodies after the
      // first generic materialization round. In no-ABI mode, run one more
      // materialization pass so those continuation bodies get dispatch/callsite
      // rewrites before readability cleanup.
      if (opts.no_abi_mode) {
        addPhaseMarker(MPM, "Phase 3.86: post-continuation materialization");
        if (opts.verify_generic_static_devirtualization)
          MPM.addPass(
              VerifiedVirtualCFGMaterializationPass(opts.session_graph));
        else
          MPM.addPass(VirtualCFGMaterializationPass(opts.session_graph));
        addClosedSliceShapeProbe(MPM, "phase3.86");
      }
    }

    add_closed_root_slice_cleanup("Phase 3.9: closed root-slice cleanup");
    addClosedSliceShapeProbe(MPM, "phase3.9");

    // Phase 3.9 can define new closed-slice blk_* continuations late via
    // LiftConstantContinuationDeclarationTargetsPass and missing-block
    // rewrites. Run one final bounded materialization sweep in no-ABI mode so
    // those newly reachable continuations get a last generic devirtualization
    // pass before emission, without re-entering continuation discovery.
    if (opts.no_abi_mode &&
        !envDisabled("OMILL_SKIP_NOABI_POST_CLEANUP_MATERIALIZATION")) {
      addPhaseMarker(MPM,
                     "Phase 3.95: no-ABI post-cleanup materialization");
      MPM.addPass(RebuildClosedRootSliceCodeScopePass{});
      MPM.addPass(
          llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
      {
        llvm::FunctionPassManager FPM;
        FPM.addPass(ConstantMemoryFoldingPass());
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(llvm::InstCombinePass());
        MPM.addPass(createScopedFPM(std::move(FPM),
                                    shouldRunClosedRootSliceCodeBearingPass));
      }
      if (opts.verify_generic_static_devirtualization)
        MPM.addPass(
            VerifiedVirtualCFGMaterializationPass(opts.session_graph));
      else
        MPM.addPass(VirtualCFGMaterializationPass(opts.session_graph));
      // The Phase 3.95 materialization run introduces new blk_/sub_
      // bodies. Walk their direct musttail calls to declared blk_*<pc>
      // continuations and lift them before the collapse pass rewrites
      // stragglers to __remill_missing_block. Per-PC `scheduled` set and
      // bounded fixpoint caps keep this step fast.
      if (!envDisabled("OMILL_SKIP_LIFT_CONST_CONTINUATION_DECL_TARGETS"))
        MPM.addPass(LiftConstantContinuationDeclarationTargetsPass(
            /*only_when_noabi_mode=*/true));
      MPM.addPass(RebuildClosedRootSliceCodeScopePass{});
      MPM.addPass(CollapseSyntheticBlockContinuationCallsPass(
          /*rewrite_to_missing_block=*/true,
          /*only_when_noabi_mode=*/true));
      MPM.addPass(
          RewriteConstantMissingBlockCallsPass(/*only_when_noabi_mode=*/true));
      addRecoveryAwareGlobalDCE(MPM, opts, RecoveryPipelinePhase::kResolve);
      MPM.addPass(RebuildClosedRootSliceCodeScopePass{});
      addClosedSliceShapeProbe(MPM, "phase3.95");
    }

    if (opts.no_abi_mode) {
      addPhaseMarker(MPM, "Phase 3.97: final closed root-slice collapse sweep");
      MPM.addPass(SanitizeModeledBoundaryPoisonMemoryArgsPass{});
      MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      MPM.addPass(RelaxClosedSliceMustTailMissingBlockPass{});
      MPM.addPass(LoopifyClosedSliceSelfRecursiveBlockHelpersPass{});
      if (!envDisabled("OMILL_SKIP_PREINLINE_REWRITE_CONST_MISSING_BLOCK_CALLS"))
        MPM.addPass(RewriteConstantMissingBlockCallsPass(
            /*only_when_noabi_mode=*/true));
      // Final inline+lower sweep for any blocks lifted after Phase 3.9
      // (e.g. by the Phase 3.95 post-cleanup materialization or by the
      // late LiftConstantContinuationDeclarationTargets above). The
      // omill.late_intrinsics_lowered and omill.late_block_semantics_marked
      // guards make these passes no-ops for blocks already processed by
      // Phase 3.9 cleanup.
      MPM.addPass(MarkClosedRootSliceSemanticHelpersForInliningPass());
      MPM.addPass(MarkLateBlockReachableSemanticHelpersPass());
      MPM.addPass(MarkClosedRootSliceHelpersForInliningPass());
      MPM.addPass(RepairBeforeInlinePass{});
      if (alwaysInlinerEnabled())
        MPM.addPass(llvm::AlwaysInlinerPass());
      {
        llvm::FunctionPassManager FPM;
        // Also lower `__remill_undefined_*` here (Category 10): the default
        // `buildFinalCleanupPipeline` lowers them later, but that means our
        // SROA+DSE sweep below never sees the resulting `freeze(poison)`
        // stores. Lowering them in this pass puts the dead stores in
        // reach of the cleanup.
        // Include Return so __remill_function_return is lowered to `ret`
        // BEFORE the late block inline. If left un-lowered, AlwaysInliner
        // inlines the callee body containing the raw intrinsic call into
        // the output root, and the kPreFinalize normalization then lowers
        // it to a `ret` mid-body — terminating the root function early
        // and making all continuation blocks unreachable.
        FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::Phase1 |
                                              LowerCategories::ResolvedDispatch |
                                              LowerCategories::Undefined |
                                              LowerCategories::Return));
        FPM.addPass(llvm::SimplifyCFGPass());
        MPM.addPass(createScopedFPM(
            std::move(FPM), [](llvm::Function &F) {
              if (F.isDeclaration())
                return false;
              if (!isLiftedPipelineFunction(F))
                return false;
              if (F.hasFnAttribute("omill.late_intrinsics_lowered"))
                return false;
              for (auto &BB : F) {
                for (auto &I : BB) {
                  auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
                  if (!call)
                    continue;
                  auto *callee = call->getCalledFunction();
                  if (!callee)
                    continue;
                  auto name = callee->getName();
                  if (name.starts_with("__remill_") &&
                      name != "__remill_function_call" &&
                      name != "__remill_jump" &&
                      name != "__remill_missing_block" &&
                      name != "__remill_error") {
                    F.addFnAttr("omill.late_intrinsics_lowered");
                    return true;
                  }
                }
              }
              return false;
            }));
      }
      addRecoveryAwareGlobalDCE(MPM, opts, RecoveryPipelinePhase::kResolve);
      // Aggressive final cleanup for late-lifted blocks. The Phase 2 state
      // optimization pipeline (PromoteStateToSSA, SROA, DSE) never ran on
      // blocks discovered during Phase 3.8/3.86/3.95 materialization, so
      // their bodies still carry the raw lifter state-store pattern:
      //   - dead NEXT_PC/RETURN_PC allocas (stored, never loaded)
      //   - state flush/reload round-trips (load X; ... ; store X back)
      //   - repeated GEPs to the same State field
      //   - parity-flag ctpop computations whose results are never read
      // Running a tight SROA + InstCombine + GVN + DSE + ADCE + SimplifyCFG
      // sweep collapses all of these. Idempotency is natural: the passes
      // are no-ops on IR that's already been cleaned, and the scope
      // predicate targets lifted functions only.
      {
        llvm::FunctionPassManager FPM;
        // Pass 1: get state into SSA form and do the first cleanup round.
        FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
        FPM.addPass(llvm::EarlyCSEPass(/*UseMemorySSA=*/true));
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(llvm::DSEPass());
        FPM.addPass(llvm::ADCEPass());
        // Pass 2: after DSE, more InstCombine opportunities open up;
        // run one more round to catch them, then finish with the final
        // structural simplification. This brings the result within
        // noise of what `opt -O2` would produce externally.
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(llvm::DSEPass());
        FPM.addPass(llvm::ADCEPass());
        FPM.addPass(llvm::SimplifyCFGPass());
        MPM.addPass(
            llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      }
      if (!envDisabled("OMILL_SKIP_IPDSE"))
        MPM.addPass(InterProceduralDeadStateStorePass());
      // Fold program_counter to its entry VA for late-lifted blocks and
      // resolve PC-relative IAT loads into concrete dispatch_call targets.
      // Phase 3.5 runs the same pair but only on the initial lifted set;
      // blocks that first appear during Phase 3.8/3.86/3.95 never see it.
      // The SROA + InstCombine + GVN sweep above just exposed the canonical
      // `%x = add %program_counter, const; %p = inttoptr; %v = load %p;
      // dispatch_call(state, %v, memory)` pattern out of the raw lifter form,
      // so this is the right point to run dispatch resolution. Scope to
      // lifted functions containing a dispatch intrinsic; attribute-guarded
      // for idempotency.
      if (!envDisabled("OMILL_SKIP_PHASE397_DISPATCH_RESOLUTION")) {
        const bool is_windows = isWindowsTargetOS(opts.target_os);
        MPM.addPass(
            llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
        llvm::FunctionPassManager FPM;
        FPM.addPass(FoldProgramCounterPass());
        FPM.addPass(llvm::InstCombinePass());
        if (is_windows)
          FPM.addPass(ResolveIATCallsPass());
        FPM.addPass(llvm::GVNPass());
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(IndirectCallResolverPass());
        FPM.addPass(
            ResolveAndLowerControlFlowPass(ResolvePhases::ResolveTargets));
        FPM.addPass(
            LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
        MPM.addPass(createScopedFPM(
            std::move(FPM), [](llvm::Function &F) {
              if (F.isDeclaration())
                return false;
              if (!isLiftedPipelineFunction(F))
                return false;
              if (F.hasFnAttribute("omill.phase397_dispatch_resolved"))
                return false;
              for (auto &BB : F) {
                for (auto &I : BB) {
                  auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
                  if (!call)
                    continue;
                  auto *callee = call->getCalledFunction();
                  if (!callee)
                    continue;
                  if (isDispatchIntrinsicName(callee->getName())) {
                    F.addFnAttr("omill.phase397_dispatch_resolved");
                    return true;
                  }
                }
              }
              return false;
            }));
      }
      MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});
      MPM.addPass(CollapseSyntheticBlockContinuationCallsPass(
          /*rewrite_to_missing_block=*/true,
          /*only_when_noabi_mode=*/true));
      MPM.addPass(
          RewriteConstantMissingBlockCallsPass(/*only_when_noabi_mode=*/true));
      addRecoveryAwareGlobalDCE(MPM, opts, RecoveryPipelinePhase::kResolve);
      MPM.addPass(MarkReachableClosedRootSliceFunctionsPass{});

      // When a block's only successor is a constant non-executable
      // Catch any remaining non-executable missing-block targets that
      // survived into Phase 3.97 (e.g. from late materialization).
      if (!envDisabled("OMILL_SKIP_NONEXEC_MISSING_BLOCK_TO_RET")) {
        MPM.addPass(
            llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
        MPM.addPass(RewriteNonExecutableMissingBlockToRetPass{});
      }

      // Late block-inlining: BlockLifter emits one function per basic
      // block (`blk_<pc>`) plus `sub_<pc>` for direct call targets.
      // After every normalization, resolution, and cleanup pass has
      // operated on that per-block representation, tag *every*
      // BlockLifter output (both `blk_<pc>` and non-root `sub_<pc>`)
      // as `alwaysinline` and run the always-inliner so the full
      // call graph collapses into the single `omill.output_root`
      // entry.  Cyclic back-edges that survive inlining (self-
      // recursive musttail after SCC collapse) are converted into
      // natural loops by a TailCallElim sweep afterwards.  Only
      // functions carrying the `omill.block_lifter` attribute are
      // touched — TraceLifter-produced `sub_<pc>` and the output
      // root itself stay where they are.
      if (!envDisabled("OMILL_SKIP_LATE_BLOCK_INLINE")) {
        struct MarkBlockLifterBlocksAlwaysInlinePass
            : llvm::PassInfoMixin<MarkBlockLifterBlocksAlwaysInlinePass> {
          static bool isBlockLifterBlock(const llvm::Function &F) {
            if (F.isDeclaration())
              return false;
            if (!F.hasFnAttribute("omill.block_lifter"))
              return false;
            // Protect the output root — it is the function we are
            // inlining *into*, not one we want to collapse away.
            if (F.hasFnAttribute("omill.output_root"))
              return false;
            auto name = F.getName();
            return name.starts_with("blk_") || name.starts_with("sub_");
          }

          llvm::PreservedAnalyses run(llvm::Module &M,
                                       llvm::ModuleAnalysisManager &) {
            bool changed = false;
            unsigned tagged_blk = 0;
            unsigned tagged_sub = 0;
            for (auto &F : M) {
              if (!isBlockLifterBlock(F))
                continue;
              if (F.hasFnAttribute(llvm::Attribute::NoInline))
                F.removeFnAttr(llvm::Attribute::NoInline);
              if (F.hasFnAttribute(llvm::Attribute::OptimizeNone))
                F.removeFnAttr(llvm::Attribute::OptimizeNone);
              if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
                F.addFnAttr(llvm::Attribute::AlwaysInline);
                changed = true;
                if (F.getName().starts_with("blk_"))
                  ++tagged_blk;
                else
                  ++tagged_sub;
              }
              if (!F.hasLocalLinkage()) {
                F.setLinkage(llvm::GlobalValue::InternalLinkage);
                changed = true;
              }
            }
            if (std::getenv("OMILL_DEBUG_LATE_BLOCK_INLINE") != nullptr)
              llvm::errs() << "[late-block-inline] tagged "
                           << tagged_blk << " blk_<pc> + "
                           << tagged_sub << " sub_<pc> alwaysinline "
                           << "(force, protect output_root)\n";
            return changed ? llvm::PreservedAnalyses::none()
                           : llvm::PreservedAnalyses::all();
          }
          static bool isRequired() { return true; }
        };
        MPM.addPass(MarkBlockLifterBlocksAlwaysInlinePass{});
        if (alwaysInlinerEnabled())
          MPM.addPass(llvm::AlwaysInlinerPass());
        // After forcing every acyclic blk_<pc> + sub_<pc> chain into
        // the output root, any SCC that could not be inlined further
        // collapses into a self-recursive musttail — convert those
        // into natural loops so the final IR has no infinite-tail-
        // recursion patterns left.
        {
          llvm::FunctionPassManager FPM;
          FPM.addPass(llvm::TailCallElimPass());
          FPM.addPass(llvm::SimplifyCFGPass());
          MPM.addPass(
              llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
        }
        MPM.addPass(llvm::GlobalDCEPass());
      }

      addClosedSliceShapeProbe(MPM, "phase3.97");
    }

  }
}

static void buildBoundaryLoweringPipeline(llvm::ModulePassManager &MPM,
                                          const PipelineOptions &opts) {
  addPhaseMarker(MPM, "Phase 4: ABI recovery");
  if (opts.require_remill_normalization) {
    RemillNormalizationOrchestrator normalization;
    normalization.appendToPipeline(
        MPM, RemillNormalizationRequest{
                 RemillNormalizationEpoch::kPreFinalize,
                 opts.no_abi_mode,
                 /*aggressive_folding=*/true,
                 opts.scope_predicate});
  }
  if (opts.recover_abi) {
    buildABIRecoveryPipeline(MPM, opts);
  }
}

struct CanonicalizeTerminalErrorHandlerCallsPass
    : llvm::PassInfoMixin<CanonicalizeTerminalErrorHandlerCallsPass> {
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &) {
    auto *M = F.getParent();
    if (!M)
      return llvm::PreservedAnalyses::all();

    llvm::SmallVector<llvm::CallInst *, 4> terminal_calls;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->getName() != "__omill_error_handler")
          continue;
        auto *next = call->getNextNonDebugInstruction();
        if (!next || !llvm::isa<llvm::ReturnInst>(next))
          continue;
        terminal_calls.push_back(call);
      }
    }

    if (terminal_calls.empty())
      return llvm::PreservedAnalyses::all();

    auto *trap = llvm::Intrinsic::getOrInsertDeclaration(
        M, llvm::Intrinsic::trap);
    bool changed = false;
    for (auto *call : terminal_calls) {
      auto *BB = call->getParent();
      llvm::IRBuilder<> Builder(call);
      Builder.CreateCall(trap);
      auto *new_term = Builder.CreateUnreachable();
      while (&BB->back() != new_term) {
        auto &dead = BB->back();
        if (!dead.use_empty())
          dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
        dead.eraseFromParent();
      }
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

struct CanonicalizeTerminalMissingBlockHandlerCallsPass
    : llvm::PassInfoMixin<CanonicalizeTerminalMissingBlockHandlerCallsPass> {
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &) {
    auto *M = F.getParent();
    if (!M || !isNoABIModeModule(*M))
      return llvm::PreservedAnalyses::all();

    llvm::SmallVector<llvm::CallInst *, 4> terminal_calls;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->getName() != "__omill_missing_block_handler")
          continue;

        bool saw_terminal_dispatch = false;
        bool conflict = false;
        for (llvm::Instruction *next = call->getNextNonDebugInstruction(); next;
             next = next->getNextNonDebugInstruction()) {
          if (llvm::isa<llvm::ReturnInst>(next)) {
            break;
          }
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(next)) {
            auto *next_callee = CB->getCalledFunction();
            if (!next_callee) {
              conflict = true;
              break;
            }
            if (next_callee->isIntrinsic())
              continue;
            if (next_callee->getName() == "__remill_jump" ||
                omill::isDispatchJumpName(next_callee->getName())) {
              saw_terminal_dispatch = true;
              continue;
            }
            if (next_callee->getName() == "__omill_missing_block_handler")
              continue;
            conflict = true;
            break;
          }
        }

        if (!conflict && saw_terminal_dispatch)
          terminal_calls.push_back(call);
      }
    }

    if (terminal_calls.empty())
      return llvm::PreservedAnalyses::all();

    auto *trap = llvm::Intrinsic::getOrInsertDeclaration(
        M, llvm::Intrinsic::trap);
    bool changed = false;
    for (auto *call : terminal_calls) {
      auto *BB = call->getParent();
      llvm::IRBuilder<> Builder(call);
      Builder.CreateCall(trap);
      auto *new_term = Builder.CreateUnreachable();
      while (&BB->back() != new_term) {
        auto &dead = BB->back();
        if (!dead.use_empty() && !dead.getType()->isVoidTy()) {
          dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
        }
        dead.eraseFromParent();
      }
      changed = true;
    }

    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

static void buildFinalCleanupPipeline(llvm::ModulePassManager &MPM,
                                      const PipelineOptions &opts) {
  addPhaseMarker(MPM, "Phase 5: deobfuscation");
  if (opts.deobfuscate) {
    MPM.addPass(llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    buildDeobfuscationPipeline(FPM, opts);
    MPM.addPass(createScopedFPM(std::move(FPM),
                                shouldRunClosedRootSliceNativePass));
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
    FPM.addPass(CanonicalizeTerminalMissingBlockHandlerCallsPass{});
    FPM.addPass(CanonicalizeTerminalErrorHandlerCallsPass{});
    if (opts.run_cleanup_passes && !envDisabled("OMILL_SKIP_LATE_CLEANUP")) {
      if (!opts.use_block_lifting) {
        FPM.addPass(llvm::InstCombinePass());
      }
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
    }
    MPM.addPass(createScopedFPM(std::move(FPM),
                                shouldRunClosedRootSliceScopedPass));
  }

  if (opts.require_remill_normalization) {
    RemillNormalizationOrchestrator normalization;
    normalization.appendToPipeline(
        MPM, RemillNormalizationRequest{
                 RemillNormalizationEpoch::kFinalVerification,
                 opts.no_abi_mode,
                 /*aggressive_folding=*/true,
                 opts.scope_predicate});
  }

  // Fold known Windows API opaque predicates.  VMProtect calls
  // IsProcessorFeaturePresent(PF_FASTFAIL_AVAILABLE=23) and branches
  // on the result: the always-true path leads to int $41 (fastfail) +
  // unreachable.  The IAT resolver creates these calls during
  // normalization; by this point they're fully materialized in the
  // output root.  Folding to constant 1 + cleanup eliminates the dead
  // branches, their associated int $1/int $41 traps, and any native
  // boundary placeholders that were only reachable from dead paths.
  if (!envDisabled("OMILL_SKIP_FOLD_KNOWN_IMPORT_CALLS")) {
    struct FoldKnownImportCallsPass
        : llvm::PassInfoMixin<FoldKnownImportCallsPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                   llvm::ModuleAnalysisManager &) {
        auto &Ctx = M.getContext();
        auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
        bool changed = false;

        llvm::SmallVector<llvm::CallInst *, 8> to_fold;
        for (auto &F : M) {
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->arg_size() < 1)
                continue;
              if (call->getCalledOperand()->getName() !=
                  "IsProcessorFeaturePresent")
                continue;
              auto *fid = llvm::dyn_cast<llvm::ConstantInt>(
                  call->getArgOperand(0));
              if (fid && fid->getZExtValue() == 23)
                to_fold.push_back(call);
            }
          }
        }

        for (auto *call : to_fold) {
          call->replaceAllUsesWith(llvm::ConstantInt::get(i64_ty, 1));
          call->eraseFromParent();
          changed = true;
        }
        return changed ? llvm::PreservedAnalyses::none()
                       : llvm::PreservedAnalyses::all();
      }
      static bool isRequired() { return true; }
    };
    MPM.addPass(FoldKnownImportCallsPass{});

    // Eliminate VMP opaque predicate branches.  VMP inserts conditional
    // branches where one side (the dead path) contains an `int 1` or
    // `int 3` debug/breakpoint trap, while the other side is the real
    // continuation.  Detect this pattern and fold the branch to always
    // take the non-trap side, then let ADCE + SimplifyCFG clean up.
    if (opts.deobfuscate) {
      struct EliminateVMPOpaquePredicatesPass
          : llvm::PassInfoMixin<EliminateVMPOpaquePredicatesPass> {

        static bool hasDebugTrap(llvm::BasicBlock &BB) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || !call->isInlineAsm())
              continue;
            auto *asm_val =
                llvm::dyn_cast<llvm::InlineAsm>(call->getCalledOperand());
            if (!asm_val)
              continue;
            auto s = asm_val->getAsmString();
            if (s == "int $$1" || s == "int $$3")
              return true;
          }
          return false;
        }

        /// BFS from BB looking for an `int $1`/`int $3` trap within the
        /// reachable subgraph, bounded to 64 blocks to avoid runaway
        /// traversal.  Stops at the other_side block (the non-trap
        /// branch target) to avoid crossing the merge point.
        static bool subgraphContainsTrap(llvm::BasicBlock *BB,
                                          llvm::BasicBlock *other_side) {
          llvm::SmallPtrSet<llvm::BasicBlock *, 32> visited;
          llvm::SmallVector<llvm::BasicBlock *, 16> worklist;
          worklist.push_back(BB);
          while (!worklist.empty() && visited.size() < 64) {
            auto *cur = worklist.pop_back_val();
            if (!visited.insert(cur).second)
              continue;
            if (cur == other_side)
              continue;  // don't cross into the real side
            if (hasDebugTrap(*cur))
              return true;
            for (auto *succ : llvm::successors(cur))
              worklist.push_back(succ);
          }
          return false;
        }

        llvm::PreservedAnalyses run(llvm::Module &M,
                                     llvm::ModuleAnalysisManager &) {
          bool changed = false;
          for (auto &F : M) {
            for (auto &BB : F) {
              auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
              if (!br || !br->isConditional())
                continue;
              auto *true_bb = br->getSuccessor(0);
              auto *false_bb = br->getSuccessor(1);
              bool true_trap = subgraphContainsTrap(true_bb, false_bb);
              bool false_trap = subgraphContainsTrap(false_bb, true_bb);
              // Only fold when exactly one side has a trap.
              if (true_trap == false_trap)
                continue;
              auto *keep = true_trap ? false_bb : true_bb;
              auto *dead = true_trap ? true_bb : false_bb;
              llvm::BranchInst::Create(keep, br->getIterator());
              dead->removePredecessor(&BB);
              br->eraseFromParent();
              changed = true;
            }
          }
          return changed ? llvm::PreservedAnalyses::none()
                         : llvm::PreservedAnalyses::all();
        }
        static bool isRequired() { return true; }
      };
      MPM.addPass(EliminateVMPOpaquePredicatesPass{});

      // Remove anti-debug and anti-VM inline asm artifacts.
      //
      // - `int $1` / `int $3`: debug/breakpoint traps that VMP's exception
      //   handler catches and skips at runtime.  Without the handler they'd
      //   crash, but the lifted control flow already has the correct
      //   continuation (the branch after the trap).  Safe to erase.
      //
      // - `inl` / `inb`: port I/O used for VM-environment detection.
      //   Results are stored to State but never used for real computation
      //   (only as opaque predicate inputs).  Replace with constant 0 so
      //   ADCE can eliminate downstream dead code.
      struct RemoveAntiAnalysisAsmPass
          : llvm::PassInfoMixin<RemoveAntiAnalysisAsmPass> {
        llvm::PreservedAnalyses run(llvm::Module &M,
                                     llvm::ModuleAnalysisManager &) {
          bool changed = false;
          auto &Ctx = M.getContext();
          llvm::SmallVector<llvm::CallInst *, 16> to_erase;
          llvm::SmallVector<std::pair<llvm::CallInst *, llvm::Value *>, 8>
              to_replace;

          for (auto &F : M) {
            for (auto &BB : F) {
              for (auto &I : BB) {
                auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
                if (!call || !call->isInlineAsm())
                  continue;
                auto *asm_val = llvm::dyn_cast<llvm::InlineAsm>(
                    call->getCalledOperand());
                if (!asm_val)
                  continue;
                auto s = asm_val->getAsmString();
                if (s == "int $$1" || s == "int $$3") {
                  to_erase.push_back(call);
                } else if (s.starts_with("inl ") || s.starts_with("inb ")) {
                  auto *zero =
                      llvm::Constant::getNullValue(call->getType());
                  to_replace.push_back({call, zero});
                }
              }
            }
          }

          for (auto *call : to_erase) {
            call->eraseFromParent();
            changed = true;
          }
          for (auto &[call, repl] : to_replace) {
            call->replaceAllUsesWith(repl);
            call->eraseFromParent();
            changed = true;
          }
          return changed ? llvm::PreservedAnalyses::none()
                         : llvm::PreservedAnalyses::all();
        }
        static bool isRequired() { return true; }
      };
      MPM.addPass(RemoveAntiAnalysisAsmPass{});
    }

    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      MPM.addPass(createScopedFPM(std::move(FPM),
                                  shouldRunClosedRootSliceScopedPass));
    }
  }

  // After deobfuscation and all inlining, promote remaining State struct
  // field accesses (GEP+load/store through arg0) to local allocas, then
  // SROA to SSA.  This eliminates the remill State pointer threading and
  // produces clean scalar variables for register values.
  if (opts.no_abi_mode && opts.use_block_lifting) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(OptimizeStatePass(OptimizePhases::Promote));
    FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::DSEPass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(createScopedFPM(std::move(FPM),
                                shouldRunClosedRootSliceScopedPass));
  }

  if (!opts.preserve_lifted_semantics)
    buildLiftInfrastructureCleanupPipeline(MPM);

  addPhaseMarker(MPM, "Final: cleanup");
  MPM.addPass(llvm::GlobalDCEPass());
  MPM.addPass(DebugPrintSelectedFunctionsPass{});
}

void buildPipeline(llvm::ModulePassManager &MPM, const PipelineOptions &opts) {
  buildPreResolutionPipeline(MPM, opts);
  if (opts.stop_after_state_optimization)
    return;
  buildIterativeResolutionEpoch(MPM, opts);
  buildBoundaryLoweringPipeline(MPM, opts);
  buildFinalCleanupPipeline(MPM, opts);
}

void buildLateCleanupPipeline(llvm::ModulePassManager &MPM,
                              const PipelineOptions &opts) {
  MPM.addPass(RewriteIndirectCallTerminalBoundaryOutputRootsPass{});
  MPM.addPass(CanonicalizeTerminalBoundaryOutputRootsToProbeCyclePass{});
  MPM.addPass(RewriteExecutableBoundaryHandlerCallsPass{});
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(CanonicalizeTerminalMissingBlockHandlerCallsPass{});
    FPM.addPass(CanonicalizeTerminalErrorHandlerCallsPass{});
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  // In no-ABI mode, generic materialization can still introduce fresh
  // semantic-helper callsites (e.g. CALLI/PUSHI helpers) after the main
  // normalization epochs. Re-inline those helpers, run one more remill-aware
  // normalization sweep, then strip the compiler-used pinning so GlobalDCE can
  // actually drop the now-dead semantic/runtime scaffolding.
  if (opts.no_abi_mode && !opts.preserve_lifted_semantics &&
      !envDisabled("OMILL_SKIP_NOABI_LATE_SEMANTIC_NORMALIZATION")) {
    MPM.addPass(SanitizeModeledBoundaryPoisonMemoryArgsPass{});
    MPM.addPass(MarkOutputRootNativeHelpersForInliningPass{});
    MPM.addPass(MarkOutputRootSemanticHelpersForInliningPass{});
    MPM.addPass(UnprotectReachableClosedRootSliceHelpersPass{});
    MPM.addPass(UnprotectRemillSemanticsPass{});
    MPM.addPass(RepairBeforeInlinePass{});
    if (alwaysInlinerEnabled())
      MPM.addPass(llvm::AlwaysInlinerPass());
    if (opts.require_remill_normalization) {
      RemillNormalizationOrchestrator normalization;
      normalization.appendToPipeline(
          MPM, RemillNormalizationRequest{
                   RemillNormalizationEpoch::kFinalVerification,
                   opts.no_abi_mode,
                   /*aggressive_folding=*/true,
                   opts.scope_predicate,
                   /*include_semantic_helpers=*/true});
    }
    MPM.addPass(StripCompilerUsedPass{});
    buildLiftInfrastructureCleanupPipeline(MPM);
  }

  // Final standalone outputs can still carry direct loads from read-only image
  // data (for example kRoundConstants in compact wrappers). Re-run binary-aware
  // constant folding here so final output cleanup can materialize those loads
  // even after earlier passes have reshaped the output-root closure.
  if (!envDisabled("OMILL_SKIP_LATE_CONST_MEMORY_FOLD")) {
    MPM.addPass(
        llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(CombinedFixedPointDevirtPass());
    FPM.addPass(RecoverGlobalTypesPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::InstCombinePass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }

  if (!envDisabled("OMILL_SKIP_LATE_DISPATCH_RESOLUTION")) {
    const bool is_windows = isWindowsTargetOS(opts.target_os);
    MPM.addPass(
        llvm::RequireAnalysisPass<BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(FoldProgramCounterPass());
    FPM.addPass(llvm::InstCombinePass());
    if (is_windows)
      FPM.addPass(ResolveIATCallsPass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::InstCombinePass());
    FPM.addPass(IndirectCallResolverPass());
    FPM.addPass(ResolveAndLowerControlFlowPass(
        ResolvePhases::ResolveTargets | ResolvePhases::RecoverTables));
    FPM.addPass(LowerRemillIntrinsicsPass(LowerCategories::ResolvedDispatch));
    MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
            if (auto *Callee = CI->getCalledFunction())
              if (isDispatchIntrinsicName(Callee->getName()))
                return true;
      return false;
    }));
  }
  if (!envDisabled("OMILL_SKIP_LATE_DISPATCH_DCE")) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    MPM.addPass(createScopedFPM(std::move(FPM), [](llvm::Function &F) {
      return isLiftedPipelineFunction(F);
    }));
    MPM.addPass(llvm::GlobalDCEPass());
  }




  if (!envDisabled("OMILL_SKIP_DEFINED_TARGET_PATCH"))
    MPM.addPass(PatchDefinedControlTargetsPass{});

  // Eliminate calls to unresolved remill-signature semantic functions.
  // After the full pipeline + ABI recovery, any remaining
  //   declare ptr @sub_*(ptr noalias, i64, ptr noalias)
  // can be either:
  //   * a genuinely dead unresolved semantic target, or
  //   * a still-unlifted direct helper/root that points at real in-image code.
  // Only the first case is safe to rewrite to unreachable.
  if (!envDisabled("OMILL_SKIP_DEAD_SEMANTIC_ELIM")) {
    struct DeadSemanticCallEliminationPass
        : llvm::PassInfoMixin<DeadSemanticCallEliminationPass> {
      llvm::PreservedAnalyses run(llvm::Module &M,
                                  llvm::ModuleAnalysisManager &MAM) {
        // Identify unresolved remill-signature declarations:
        //   declare ptr @sub_*(ptr noalias, i64, ptr noalias)
        llvm::SmallVector<llvm::Function *, 16> dead_semantics;
        auto *ptr_ty = llvm::PointerType::getUnqual(M.getContext());
        auto *i64_ty = llvm::Type::getInt64Ty(M.getContext());
        auto *binary_memory = MAM.getCachedResult<BinaryMemoryAnalysis>(M);
        const bool has_image =
            binary_memory && binary_memory->imageBase() && binary_memory->imageSize();
        for (auto &F : M) {
          if (!F.isDeclaration())
            continue;
          if (!F.getName().starts_with("sub_"))
            continue;
          auto *FT = F.getFunctionType();
          if (FT->getNumParams() != 3)
            continue;
          if (FT->getReturnType() != ptr_ty)
            continue;
          if (FT->getParamType(0) != ptr_ty)
            continue;
          if (FT->getParamType(1) != i64_ty)
            continue;
          if (FT->getParamType(2) != ptr_ty)
            continue;

          // Fail closed when we do not have usable binary-image information.
          if (!has_image)
            continue;

          const uint64_t target_pc = extractEntryVA(F.getName());
          if (target_pc == 0)
            continue;

          // Keep in-image executable targets. Those are still-unresolved
          // helper roots, not dead semantics.
          if (isInImageRange(*binary_memory, target_pc) &&
              isTargetExecutable(*binary_memory, target_pc)) {
            continue;
          }

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
      static bool isInOutputRootNativeClosure(llvm::Function &Target) {
        if (Target.isDeclaration() || !Target.getName().ends_with("_native"))
          return false;

        auto *M = Target.getParent();
        llvm::SmallVector<llvm::Function *, 16> worklist;
        llvm::SmallPtrSet<llvm::Function *, 32> seen;
        for (auto &F : *M) {
          if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
              !F.getName().ends_with("_native")) {
            continue;
          }
          if (seen.insert(&F).second)
            worklist.push_back(&F);
        }

        while (!worklist.empty()) {
          auto *F = worklist.pop_back_val();
          if (F == &Target)
            return true;
          for (auto &BB : *F) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              auto *Callee = CB ? CB->getCalledFunction() : nullptr;
              if (!Callee || Callee->isDeclaration() ||
                  !Callee->getName().ends_with("_native")) {
                continue;
              }
              if (seen.insert(Callee).second)
                worklist.push_back(Callee);
            }
          }
        }

        return false;
      }

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
          if (F.getFnAttribute("omill.param_state_offsets").isValid() &&
              isInOutputRootNativeClosure(F)) {
            continue;
          }
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

  MPM.addPass(llvm::GlobalDCEPass());
  MPM.addPass(RewriteLoopifiedTerminalBoundaryOutputRootsPass{});
  MPM.addPass(RewriteIndirectCallTerminalBoundaryOutputRootsPass{});
  MPM.addPass(CanonicalizeTerminalBoundaryOutputRootsToProbeCyclePass{});
  MPM.addPass(RewriteExecutableBoundaryHandlerCallsPass{});
  MPM.addPass(AnnotateTerminalBoundaryHandlersPass{});
  MPM.addPass(AnnotateTerminalBoundaryCyclesPass{});
}

void buildLateCleanupPipeline(llvm::ModulePassManager &MPM) {
  buildLateCleanupPipeline(MPM, PipelineOptions{});
}

unsigned eliminateBodyUnreachableFunctions(llvm::Module &M) {
  // Find every `define` whose body is exactly one `unreachable` (which
  // would compile to an orphaned `ud2` in the final binary), and rewrite
  // the body into a no-op pass-through that returns its `memory`
  // argument.  That matches the remill lifted-function calling
  // convention — callers continue to thread the memory token through
  // and observe a clean return instead of a trap.  We never erase the
  // functions or touch their callers, so this cannot cascade into
  // upstream functions or break the output-root closure.
  //
  // Only signatures matching `ptr (ptr, i64, ptr) -> ptr` (i.e. the
  // remill lifted convention) are rewritten; anything else is left
  // alone.
  auto &Ctx = M.getContext();
  auto *ptr_ty = llvm::PointerType::getUnqual(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto hasLiftedRemillSignature = [&](llvm::Function &F) -> bool {
    auto *FT = F.getFunctionType();
    if (FT->getNumParams() != 3)
      return false;
    if (FT->getReturnType() != ptr_ty)
      return false;
    if (FT->getParamType(0) != ptr_ty)
      return false;
    if (FT->getParamType(1) != i64_ty)
      return false;
    if (FT->getParamType(2) != ptr_ty)
      return false;
    return true;
  };

  auto isBodyUnreachable = [](const llvm::Function &F) -> bool {
    if (F.isDeclaration() || F.empty())
      return false;
    if (F.size() != 1)
      return false;
    const auto &entry = F.getEntryBlock();
    return entry.size() == 1 &&
           llvm::isa<llvm::UnreachableInst>(entry.front());
  };

  unsigned rewritten = 0;
  for (auto &F : M) {
    if (!isBodyUnreachable(F))
      continue;
    if (!hasLiftedRemillSignature(F))
      continue;
    // `deleteBody()` strips every attribute on the function and its
    // arguments, so remember the caller-observable ones we care about
    // before we rebuild the body.
    F.deleteBody();
    auto *entry = llvm::BasicBlock::Create(Ctx, "body", &F);
    llvm::IRBuilder<> Builder(entry);
    Builder.CreateRet(F.getArg(2));
    if (F.hasFnAttribute(llvm::Attribute::NoReturn))
      F.removeFnAttr(llvm::Attribute::NoReturn);
    if (F.hasFnAttribute(llvm::Attribute::NoInline))
      F.removeFnAttr(llvm::Attribute::NoInline);
    if (F.hasFnAttribute(llvm::Attribute::OptimizeNone))
      F.removeFnAttr(llvm::Attribute::OptimizeNone);
    // Tag the now-trivial stub as alwaysinline so a subsequent
    // AlwaysInlinerPass can fold it directly into every caller.
    // Output roots stay external and retain their body so callers
    // from outside the module can still target them.
    if (!F.hasFnAttribute("omill.output_root")) {
      if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline))
        F.addFnAttr(llvm::Attribute::AlwaysInline);
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
    }
    ++rewritten;
  }

  if (rewritten > 0 &&
      std::getenv("OMILL_DEBUG_DEAD_PROPAGATE") != nullptr) {
    llvm::errs() << "[dead-propagate] rewrote " << rewritten
                 << " body:unreachable functions to ret memory\n";
  }
  return rewritten;
}

void buildPostPatchCleanupPipeline(llvm::ModulePassManager &MPM,
                                   unsigned inline_threshold) {
  if (moduleInlinerEnabled()) {
    llvm::InlineParams params = llvm::getInlineParams(inline_threshold);
    MPM.addPass(llvm::ModuleInlinerWrapperPass(params));
  }
  buildCleanupPipeline(MPM, CleanupProfile::kBoundary);
  MPM.addPass(llvm::GlobalDCEPass());
}

void buildLateClosureCanonicalizationPipeline(llvm::ModulePassManager &MPM) {
  llvm::FunctionPassManager FPM;
  FPM.addPass(CombinedFixedPointDevirtPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::InstCombinePass());
  MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  MPM.addPass(CanonicalizeABIBoundaryDeclarationsPass());
  MPM.addPass(llvm::GlobalDCEPass());
}

void buildLateClosurePatchPipeline(llvm::ModulePassManager &MPM,
                                   unsigned inline_threshold) {
  llvm::FunctionPassManager FPM;
  FPM.addPass(CombinedFixedPointDevirtPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::GVNPass());
  FPM.addPass(llvm::InstCombinePass());
  MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  if (!envDisabled("OMILL_SKIP_DEFINED_TARGET_PATCH"))
    MPM.addPass(PatchDefinedControlTargetsPass{});
  MPM.addPass(CanonicalizeABIBoundaryDeclarationsPass());
  buildPostPatchCleanupPipeline(MPM, inline_threshold);
}

void buildLiftInfrastructureCleanupPipeline(llvm::ModulePassManager &MPM) {
  auto add_debug_probe = [&](llvm::StringRef label) {
    if (std::getenv("OMILL_DEBUG_LIFT_CLEANUP_FUNCTIONS"))
      MPM.addPass(DebugPrintSelectedFunctionsWithLabelPass(label.str()));
  };

  add_debug_probe("before_strip_compiler_used");
  MPM.addPass(StripCompilerUsedPass());
  add_debug_probe("after_strip_compiler_used");
  MPM.addPass(InternalizeDeadLiftedHelpersPass());
  add_debug_probe("after_internalize_dead_lifted_helpers");
  MPM.addPass(InternalizeRemillSemanticsPass());
  add_debug_probe("after_internalize_remill_semantics");
  MPM.addPass(llvm::GlobalDCEPass());
  add_debug_probe("after_first_globaldce");
  MPM.addPass(StripCompilerUsedPass());
  add_debug_probe("after_second_strip_compiler_used");
  MPM.addPass(llvm::GlobalDCEPass());
  add_debug_probe("after_second_globaldce");
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
  MAM.registerPass([&] { return VirtualMachineModelAnalysis(); });
}

void registerRemainingModuleAnalyses(llvm::ModuleAnalysisManager &MAM) {
  MAM.registerPass([&] { return TargetArchAnalysis(); });
  MAM.registerPass([&] { return CallGraphAnalysis(); });
  MAM.registerPass([&] { return CallingConventionAnalysis(); });
  MAM.registerPass([&] { return LiftedFunctionAnalysis(); });
  MAM.registerPass([&] { return VirtualCalleeRegistryAnalysis(); });
  MAM.registerPass([&] { return VirtualMachineModelAnalysis(); });
}

void registerAAWithManager(llvm::AAManager &AAM) {
  AAM.registerFunctionAnalysis<SegmentsAA>();
}

}  // namespace omill

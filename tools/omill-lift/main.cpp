#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/PassTimingInfo.h>
#include <llvm/IR/ValueHandle.h>
#include <llvm/IR/Verifier.h>
#include <llvm/AsmParser/Parser.h>
#include <llvm/BinaryFormat/COFF.h>
#include <llvm/BinaryFormat/Magic.h>
#include <llvm/BinaryFormat/MachO.h>
#include <llvm/Object/COFF.h>
#include <llvm/Object/MachO.h>
#include <llvm/Object/MachOUniversal.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/StandardInstrumentations.h>
#include <llvm/Linker/Linker.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>
#include <llvm/Transforms/IPO/Inliner.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/SCCP.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/Process.h>
#include <llvm/Support/Program.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include <remill/Arch/Arch.h>
#include <remill/Arch/Instruction.h>
#include <remill/Arch/Name.h>
#include <remill/BC/IntrinsicTable.h>
#include "omill/BC/LiftTargetPolicy.h"
#include "omill/BC/TraceLifter.h"
#include "omill/BC/BlockLifter.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/BC/TraceLiftAnalysis.h"
#include <remill/BC/Util.h>
#include <remill/OS/OS.h>

#include <llvm/Support/Win64EH.h>

#include "omill/Support/MemoryLimit.h"
#include "omill/Arch/ArchABI.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/TargetArchAnalysis.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Analysis/VirtualMachineModel.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/OutputRootClosure.h"
#include "omill/Devirtualization/Runtime.h"
#include "omill/Omill.h"
#include "omill/Remill/Normalization.h"
#include "omill/Passes/JumpTableConcretizer.h"
#include "omill/Passes/InterProceduralConstProp.h"
#include "omill/Passes/CombinedFixedPointDevirt.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Passes/ResolveAndLowerControlFlow.h"
#include "omill/Tools/LiftRunContract.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/ProtectedBoundaryUtils.h"
#include "omill/Utils/StateFieldMap.h"
#include "RuntimeAdapters.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <deque>
#include <memory>
#include <optional>
#include <vector>

#if __has_include(<glog/logging.h>)
#include <glog/logging.h>
#define OMILL_LIFT_HAS_GLOG 1
#else
#define OMILL_LIFT_HAS_GLOG 0
#endif

using namespace llvm;

/// Repair malformed PHI nodes in a module so it can be written as valid LL.
/// Handles two cases:
/// 1. Incoming values from blocks that are not predecessors (stale entries).
/// 2. Missing duplicate entries for multi-edge predecessors (e.g. switch
///    with two cases branching to the same block needs two PHI entries).
static void repairMalformedPHIs(Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    for (auto &BB : F) {
      // Count how many edges each predecessor has to this block.
      DenseMap<BasicBlock *, unsigned> pred_edge_count;
      for (auto *P : predecessors(&BB))
        ++pred_edge_count[P];

      for (auto &I : make_early_inc_range(BB)) {
        auto *phi = dyn_cast<PHINode>(&I);
        if (!phi) break;

        // Remove entries from non-predecessors.
        for (unsigned i = phi->getNumIncomingValues(); i-- > 0;) {
          if (!pred_edge_count.count(phi->getIncomingBlock(i))) {
            phi->removeIncomingValue(i, /*DeletePHIIfEmpty=*/false);
          }
        }

        // Count current entries per predecessor.
        DenseMap<BasicBlock *, unsigned> phi_count;
        for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i)
          ++phi_count[phi->getIncomingBlock(i)];

        // Add missing duplicate entries for multi-edge predecessors.
        for (auto &[pred, needed] : pred_edge_count) {
          unsigned have = phi_count.lookup(pred);
          if (have == 0) continue;  // No entry at all — can't invent a value.
          for (unsigned j = have; j < needed; ++j) {
            // Find the existing value for this predecessor.
            Value *val = phi->getIncomingValueForBlock(pred);
            phi->addIncoming(val, pred);
          }
        }

        if (phi->getNumIncomingValues() == 0) {
          phi->replaceAllUsesWith(PoisonValue::get(phi->getType()));
          phi->eraseFromParent();
        }
      }
    }
  }
}

static bool wantIterativeSessionReport() {
  const char *env = std::getenv("OMILL_REPORT_ITERATIVE_SESSION");
  if (!env || env[0] == '\0')
    return false;
  return !(env[0] == '0' && env[1] == '\0');
}

static const char *edgeKindName(omill::LiftEdgeKind kind) {
  switch (kind) {
    case omill::LiftEdgeKind::kDirectBranch:
      return "direct-branch";
    case omill::LiftEdgeKind::kDirectCall:
      return "direct-call";
    case omill::LiftEdgeKind::kIndirectBranch:
      return "indirect-branch";
    case omill::LiftEdgeKind::kIndirectCall:
      return "indirect-call";
    case omill::LiftEdgeKind::kReturn:
      return "return";
    case omill::LiftEdgeKind::kVmTrace:
      return "vm-trace";
  }
  return "unknown";
}

static void emitIterativeSessionReport(
    const std::shared_ptr<omill::IterativeLiftingSession> &session) {
  if (!session || !wantIterativeSessionReport())
    return;

  errs() << "Iterative session report [" << session->name() << "]\n";
  errs() << "  nodes=" << session->graph().nodeCount()
         << " edges=" << session->graph().edgeCount()
         << " unresolved_edges=" << session->graph().unresolvedEdgeCount()
         << " dirty_nodes=" << session->graph().dirtyNodes().size() << "\n";

  for (const auto &round : session->roundSummaries()) {
    errs() << "  round[" << round.pipeline << "#" << round.iteration << "] "
           << "dirty=" << round.dirty_functions
           << "->" << round.dirty_functions_after
           << " affected=" << round.affected_functions
           << " optimized=" << round.optimized_functions
           << " unresolved=" << round.unresolved_before << "->"
           << round.unresolved_after
           << " new_targets=" << round.new_targets
           << " pending=" << round.pending_targets
           << " total=" << round.total_ms << "ms"
           << " opt=" << round.optimize_ms << "ms"
           << " resolve=" << round.resolve_ms << "ms"
           << " ipcp=" << round.ipcp_ms << "ms"
           << " lift=" << round.lift_ms << "ms"
           << " lower=" << round.lower_ms << "ms"
           << " inline=" << round.inline_ms << "ms"
           << " reverse_inline=" << round.reverse_inline_ms << "ms"
           << " ipcp=" << (round.ipcp_changed ? "yes" : "no")
           << " lifted=" << (round.lifted_new ? "yes" : "no");
    if (round.stalled) {
      errs() << " stalled(dynamic=" << round.dynamic_unresolved
             << ", missing=" << round.missing_targets
             << ", blocked=" << round.blocked_unresolved << ")";
    }
    errs() << "\n";
  }

  auto unresolved = session->graph().unresolvedEdges();
  if (!unresolved.empty()) {
    errs() << "  unresolved edges:\n";
    for (const auto *edge : unresolved) {
      errs() << "    0x" << Twine::utohexstr(edge->source_pc) << " -> ";
      if (edge->target_pc != 0)
        errs() << "0x" << Twine::utohexstr(edge->target_pc);
      else
        errs() << "<dynamic>";
      errs() << " [" << edgeKindName(edge->kind) << "]\n";
    }
  }
}

static cl::opt<std::string> InputFilename(cl::Positional,
                                           cl::desc("<input binary (PE/Mach-O)>"),
                                           cl::Required);

static cl::opt<std::string> FuncVA("va",
                                    cl::desc("Function virtual address (hex)"));

static cl::opt<bool> RawBinary(
    "raw",
    cl::desc("Treat input as a raw (headerless) code binary"),
    cl::init(false));

static cl::opt<uint64_t> BaseAddress(
    "base",
    cl::desc("Base address for raw binary loading (default: 0)"),
    cl::init(0));

static cl::opt<std::string> OutputFilename("o", cl::desc("Output .ll file"),
                                            cl::value_desc("filename"),
                                            cl::init("-"));

static cl::opt<bool> NoABI("no-abi",
                            cl::desc("Skip ABI recovery"),
                            cl::init(false));

static cl::opt<bool> Deobfuscate("deobfuscate",
                                  cl::desc("Enable deobfuscation passes"),
                                  cl::init(false));

static cl::opt<bool> Devirtualize(
    "devirtualize",
    cl::desc("Force the library-owned devirtualization orchestrator"),
    cl::init(false));

static cl::opt<bool> ResolveTargets(
    "resolve-targets",
    cl::desc("Enable iterative indirect target resolution"),
    cl::init(false));

static cl::opt<unsigned> MaxIterations(
    "max-iterations",
    cl::desc("Max iterations for target resolution (default 10)"),
    cl::init(10));

static cl::opt<bool> IPCP(
    "ipcp",
    cl::desc("Enable interprocedural constant propagation"),
    cl::init(false));

static cl::opt<bool> ResolveExceptions(
    "resolve-exceptions",
    cl::desc("Resolve forced exceptions (ud2/int3) via .pdata SEH handlers"),
    cl::init(false));

static cl::opt<bool> BlockLift(
    "block-lift",
    cl::desc("Use blocks-as-functions architecture for iterative discovery"),
    cl::init(false));

static cl::opt<bool> DumpIR(
    "dump-ir",
    cl::desc("Dump before/after IR to before.ll, after.ll, after_abi.ll"),
    cl::init(false));

static cl::opt<std::string> VMEntry(
    "vm-entry",
    cl::desc("VM entry (vmenter) function VA for VM devirtualization (hex)"));

static cl::opt<std::string> VMExit(
    "vm-exit",
    cl::desc("VM exit (vmexit) function VA for VM devirtualization (hex)"));

static cl::opt<std::string> VMWrapper(
    "vm-wrapper",
    cl::desc("VM entry wrapper VA (hex).  If omitted, defaults to --va.  "
             "Specify this when --va points to an outer function (e.g. "
             "DriverEntry) that calls the wrapper through a thunk."));

static cl::opt<std::string> VMTraceJSON(
    "vm-trace-json",
    cl::desc("Path to an external VMTraceRecord JSON file (e.g. from "
             "eac_vm_tracer.py).  Populates the VMTraceMap analysis from "
             "pre-computed trace data instead of running the built-in emulator."));

static cl::opt<bool> OmillTimePasses(
    "omill-time-passes",
    cl::desc("Time each omill pass, printing elapsed time on exit"),
    cl::init(false));

static cl::opt<bool> VerifyEach(
    "verify-each",
    cl::desc("Run module verifier after every pass (slow, for debugging)"),
    cl::init(false));

static cl::opt<std::string> TraceFunc(
    "trace-func",
    cl::desc("Print block/instruction counts for a named function after each "
             "omill pass (e.g. sub_1800444a0)"));

static cl::opt<bool> DumpFuncPhases(
    "dump-func-phases",
    cl::desc("With --trace-func, dump the function's IR to files at each "
             "phase marker and on large instruction drops (>30%)"),
    cl::init(false));

static cl::opt<std::string> ScanSection(
    "scan-section",
    cl::desc("Scan a PE section and output function classification as JSON"));

static cl::opt<std::string> ScanOutput(
    "scan-output",
    cl::desc("Output file for --scan-section (default: stdout)"),
    cl::init("-"));

static cl::opt<bool> ScanAll(
    "scan-all",
    cl::desc("Include all functions in scan output (default: >=64B only)"),
    cl::init(false));

static cl::opt<std::string> DeobfTargets(
    "deobf-targets",
    cl::desc("JSON file with function VAs to batch-deobfuscate"));

static cl::opt<std::string> DeobfSection(
    "deobf-section",
    cl::desc("Scan section and deobfuscate all qualifying functions"));

static cl::opt<bool> AllFunctions(
    "all-functions",
    cl::desc("Batch-lift all discovered functions in executable sections"),
    cl::init(false));

static cl::opt<unsigned> MinFuncSize(
    "min-func-size",
    cl::desc("Minimum function size in bytes for scan/deobf (default: 64)"),
    cl::init(64));

static cl::opt<std::string> EventJSONL(
    "event-jsonl",
    cl::desc("Emit structured run events as JSONL to file path or '-'"),
    cl::init(""));

static cl::opt<std::string> EventDetail(
    "event-detail",
    cl::desc("Event granularity: basic|detailed"),
    cl::init("basic"));

static cl::opt<bool> VerboseRemillLogs(
    "verbose-remill-logs",
    cl::desc("Keep verbose Remill/GLOG startup diagnostics enabled"),
    cl::init(false));

static cl::opt<bool> GenericStaticDevirtualize(
    "generic-static-devirtualize",
    cl::desc("Enable generic static devirtualization materialization"),
    cl::init(false));

static cl::opt<bool> VerifyGenericStaticDevirtualization(
    "verify-generic-static-devirtualization",
    cl::desc("Validate generic static devirtualization rewrites when supported"),
    cl::init(false));

static cl::opt<std::string> DumpVirtualModel(
    "dump-virtual-model",
    cl::desc("Dump generic virtual-machine model/materialization diagnostics"),
    cl::init(""));

namespace {

std::optional<bool> parseBoolEnv(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return std::nullopt;
  if ((v[0] == '1' && v[1] == '\0') ||
      (v[0] == 't' && v[1] == '\0') ||
      (v[0] == 'T' && v[1] == '\0'))
    return true;
  if ((v[0] == '0' && v[1] == '\0') ||
      (v[0] == 'f' && v[1] == '\0') ||
      (v[0] == 'F' && v[1] == '\0'))
    return false;
  return std::nullopt;
}

std::optional<unsigned> parseUnsignedEnv(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return std::nullopt;
  unsigned value = 0;
  if (llvm::StringRef(v).getAsInteger(10, value) || value == 0)
    return std::nullopt;
  return value;
}

void dumpModuleIfEnvEnabled(llvm::Module &M, const char *env_name,
                            llvm::StringRef path) {
  if (!parseBoolEnv(env_name).value_or(false))
    return;
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec, llvm::sys::fs::OF_Text);
  if (!ec)
    M.print(os, nullptr);
}

void dumpTextIfEnvEnabled(llvm::StringRef text, const char *env_name,
                          llvm::StringRef path) {
  if (!parseBoolEnv(env_name).value_or(false))
    return;
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec, llvm::sys::fs::OF_Text);
  if (!ec)
    os << text;
}

void appendDebugMarker(const char *message) {
  const char *path = std::getenv("OMILL_DEBUG_MARKER_FILE");
  if (!path || path[0] == '\0')
    return;
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec,
                          llvm::sys::fs::OF_Append | llvm::sys::fs::OF_Text);
  if (!ec)
    os << message << "\n";
}

void setEnvIfUnset(const char *name, const char *value) {
  const char *cur = std::getenv(name);
  if (cur && cur[0] != '\0')
    return;
#if defined(_WIN32)
  _putenv_s(name, value);
#else
  setenv(name, value, 0);
#endif
}

class ScopedEnvOverride {
 public:
  ScopedEnvOverride(const char *name, const char *value)
      : name_(name) {
    const char *cur = std::getenv(name_);
    if (cur)
      old_value_ = std::string(cur);
    had_old_value_ = cur != nullptr;
#if defined(_WIN32)
    _putenv_s(name_, value);
#else
    setenv(name_, value, 1);
#endif
  }

  ~ScopedEnvOverride() {
    if (had_old_value_) {
#if defined(_WIN32)
      _putenv_s(name_, old_value_->c_str());
#else
      setenv(name_, old_value_->c_str(), 1);
#endif
      return;
    }
#if defined(_WIN32)
    _putenv_s(name_, "");
#else
    unsetenv(name_);
#endif
  }

 private:
  const char *name_ = nullptr;
  bool had_old_value_ = false;
  std::optional<std::string> old_value_;
};

struct TerminalBoundaryProbeResult {
  uint64_t target_pc = 0;
  uint64_t next_target_pc = 0;
  std::optional<std::string> cycle;
  std::optional<uint64_t> canonical_cycle_pc;
};

struct TerminalBoundaryProbeChain {
  llvm::SmallVector<uint64_t, 8> chain_pcs;
  std::optional<std::string> cycle;
  std::optional<uint64_t> canonical_cycle_pc;
};

struct TerminalBoundaryRecoveryIRSummary {
  omill::TerminalBoundaryRecoveryMetrics metrics;
  bool has_output_root = false;
};

struct TerminalBoundaryRecoveryModelSummary {
  struct Frontier {
    std::string reason;
    std::optional<uint64_t> target_pc;
    std::optional<uint64_t> canonical_target_va;
  };
  bool found_root = false;
  bool closed = false;
  unsigned reachable = 0;
  unsigned frontier = 0;
  llvm::SmallVector<Frontier, 8> frontiers;
};

struct TerminalBoundaryRecoveryAttempt {
  uint64_t target_pc = 0;
  omill::TerminalBoundaryRecoveryStatus status =
      omill::TerminalBoundaryRecoveryStatus::kTimeout;
  omill::TerminalBoundaryRecoveryMetrics metrics;
  std::string summary;
  bool imported = false;
  std::string import_rejection_reason;
};

std::optional<uint64_t> parseHexAttrValueFromLine(llvm::StringRef line,
                                                  llvm::StringRef key) {
  std::string pattern = ("\"" + key + "\"=\"").str();
  size_t pos = line.find(pattern);
  if (pos == llvm::StringRef::npos)
    return std::nullopt;
  pos += pattern.size();
  size_t end = pos;
  while (end < line.size() && llvm::isHexDigit(line[end]))
    ++end;
  if (end == pos)
    return std::nullopt;
  uint64_t value = 0;
  if (line.slice(pos, end).getAsInteger(16, value))
    return std::nullopt;
  return value;
}

std::optional<std::string> parseQuotedAttrValueFromLine(llvm::StringRef line,
                                                        llvm::StringRef key) {
  std::string pattern = ("\"" + key + "\"=\"").str();
  size_t pos = line.find(pattern);
  if (pos == llvm::StringRef::npos)
    return std::nullopt;
  pos += pattern.size();
  size_t end = line.find('"', pos);
  if (end == llvm::StringRef::npos || end <= pos)
    return std::nullopt;
  return line.slice(pos, end).str();
}

std::optional<unsigned> parseUnsignedFieldFromLine(llvm::StringRef line,
                                                   llvm::StringRef key) {
  std::string pattern = (key + "=").str();
  size_t pos = line.find(pattern);
  if (pos == llvm::StringRef::npos)
    return std::nullopt;
  pos += pattern.size();
  size_t end = pos;
  while (end < line.size() && llvm::isDigit(line[end]))
    ++end;
  if (end == pos)
    return std::nullopt;
  unsigned value = 0;
  if (line.slice(pos, end).getAsInteger(10, value))
    return std::nullopt;
  return value;
}

std::optional<uint64_t> parseHexFieldFromLine(llvm::StringRef line,
                                              llvm::StringRef key) {
  std::string pattern = (key + "=0x").str();
  size_t pos = line.find(pattern);
  if (pos == llvm::StringRef::npos)
    return std::nullopt;
  pos += pattern.size();
  size_t end = pos;
  while (end < line.size() && llvm::isHexDigit(line[end]))
    ++end;
  if (end == pos)
    return std::nullopt;
  uint64_t value = 0;
  if (line.slice(pos, end).getAsInteger(16, value))
    return std::nullopt;
  return value;
}

bool hasUnresolvedOutputRootPcCall(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;

  for (const auto &BB : F) {
    for (const auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call || call->getCalledFunction())
        continue;

      auto *called = call->getCalledOperand()->stripPointerCasts();
      auto *i2p = llvm::dyn_cast<llvm::IntToPtrInst>(called);
      if (!i2p)
        continue;

      auto *pc_like = i2p->getOperand(0)->stripPointerCasts();
      if (!pc_like->hasName())
        continue;

      auto name = pc_like->getName();
      if (name.contains("pc.canonical") || name.contains("pc.norm"))
        return true;
    }
  }

  return false;
}

bool hasUnresolvedLiftedControlTransferInFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;

  for (const auto &BB : F) {
    for (const auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;

      if (auto *callee = call->getCalledFunction()) {
        auto name = callee->getName();
        if (omill::isDispatchIntrinsicName(name) ||
            name == "__remill_function_return") {
          return true;
        }
      }

      if (!call->getCalledFunction()) {
        auto *called = call->getCalledOperand()->stripPointerCasts();
        auto *i2p = llvm::dyn_cast<llvm::IntToPtrInst>(called);
        if (!i2p)
          continue;

        auto *pc_like = i2p->getOperand(0)->stripPointerCasts();
        if (!pc_like->hasName())
          continue;

        auto name = pc_like->getName();
        if (name.contains("pc.canonical") || name.contains("pc.norm"))
          return true;
      }
    }
  }

  return false;
}

bool hasUnresolvedLiftedControlTransferInClosure(const llvm::Function &Root) {
  if (Root.isDeclaration())
    return false;

  llvm::SmallVector<const llvm::Function *, 16> worklist;
  llvm::DenseSet<const llvm::Function *> seen;
  worklist.push_back(&Root);
  seen.insert(&Root);

  while (!worklist.empty()) {
    auto *F = worklist.pop_back_val();
    if (hasUnresolvedLiftedControlTransferInFunction(*F))
      return true;

    for (const auto &BB : *F) {
      for (const auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        auto *callee = call ? call->getCalledFunction() : nullptr;
        if (!callee || callee->isDeclaration())
          continue;
        if (callee->getParent() != Root.getParent())
          continue;
        if (seen.insert(callee).second)
          worklist.push_back(callee);
      }
    }
  }

  return false;
}

std::optional<TerminalBoundaryProbeResult>
parseTerminalBoundaryProbeIR(StringRef ir_text, uint64_t target_pc) {
  llvm::SmallVector<llvm::StringRef, 64> lines;
  ir_text.split(lines, '\n');
  for (auto line : lines) {
    if (!line.starts_with("attributes #"))
      continue;
    if (line.find("\"omill.output_root\"") == llvm::StringRef::npos)
      continue;
    auto next_pc =
        parseHexAttrValueFromLine(line, "omill.terminal_boundary_target_va");
    if (!next_pc)
      next_pc =
          parseHexAttrValueFromLine(line, "omill.terminal_boundary_candidate_pc");
    if (!next_pc)
      continue;

    TerminalBoundaryProbeResult result;
    result.target_pc = target_pc;
    result.next_target_pc = *next_pc;
    result.cycle =
        parseQuotedAttrValueFromLine(line, "omill.terminal_boundary_cycle");
    result.canonical_cycle_pc = parseHexAttrValueFromLine(
        line, "omill.terminal_boundary_cycle_canonical_target_va");
    return result;
  }

  return std::nullopt;
}

std::string joinHexPCChain(llvm::ArrayRef<uint64_t> pcs) {
  llvm::SmallVector<std::string, 8> parts;
  parts.reserve(pcs.size());
  for (uint64_t pc : pcs)
    parts.push_back(llvm::utohexstr(pc));
  return llvm::join(parts, ",");
}

TerminalBoundaryRecoveryIRSummary
parseTerminalBoundaryRecoveryIRSummary(llvm::StringRef ir_text) {
  TerminalBoundaryRecoveryIRSummary summary;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  ir_text.split(lines, '\n');
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (trimmed.starts_with("define ")) {
      if (trimmed.contains("@blk_") || trimmed.contains("@block_"))
        ++summary.metrics.define_blk;
      if (trimmed.contains("\"omill.output_root\""))
        summary.has_output_root = true;
    } else if (trimmed.starts_with("declare ")) {
      if (trimmed.contains("@blk_") || trimmed.contains("@block_"))
        ++summary.metrics.declare_blk;
    }

    if (trimmed.contains("call") || trimmed.contains("musttail call")) {
      if (trimmed.contains("@blk_") || trimmed.contains("@block_"))
        ++summary.metrics.call_blk;
      if (trimmed.contains("@__omill_dispatch_jump") ||
          trimmed.contains("@__remill_jump"))
        ++summary.metrics.dispatch_jump;
      if (trimmed.contains("@__omill_dispatch_call") ||
          trimmed.contains("@__remill_function_call"))
        ++summary.metrics.dispatch_call;
      if (trimmed.contains("@__omill_missing_block_handler"))
        ++summary.metrics.missing_block_handler;
    }
  }
  return summary;
}

TerminalBoundaryRecoveryModelSummary parseTerminalBoundaryRecoveryModelSummary(
    llvm::StringRef model_text, uint64_t root_pc) {
  TerminalBoundaryRecoveryModelSummary summary;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');
  const std::string prefix =
      (llvm::Twine("root-slice root=0x") + llvm::utohexstr(root_pc)).str();
  bool in_root_block = false;
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (trimmed.starts_with(prefix)) {
      summary.found_root = true;
      in_root_block = true;
      if (auto reachable = parseUnsignedFieldFromLine(trimmed, "reachable"))
        summary.reachable = *reachable;
      if (auto frontier = parseUnsignedFieldFromLine(trimmed, "frontier"))
        summary.frontier = *frontier;
      summary.closed = trimmed.contains("closed=true");
      continue;
    }
    if (!in_root_block)
      continue;
    if (!trimmed.starts_with("frontier ")) {
      if (trimmed.starts_with("region ") || trimmed.starts_with("root-slice ") ||
          trimmed.starts_with("slot ") || trimmed.starts_with("handler ") ||
          trimmed.empty()) {
        if (!trimmed.starts_with("frontier "))
          in_root_block = false;
      }
      continue;
    }

    TerminalBoundaryRecoveryModelSummary::Frontier frontier;
    if (auto reason = parseQuotedAttrValueFromLine(trimmed, "reason")) {
      frontier.reason = *reason;
    } else {
      std::string pattern = "reason=";
      size_t pos = trimmed.find(pattern);
      if (pos != llvm::StringRef::npos) {
        pos += pattern.size();
        size_t end = pos;
        while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
          ++end;
        frontier.reason = trimmed.slice(pos, end).str();
      }
    }
    frontier.target_pc = parseHexFieldFromLine(trimmed, "target");
    frontier.canonical_target_va = parseHexFieldFromLine(trimmed, "canonical");
    summary.frontiers.push_back(std::move(frontier));
  }
  return summary;
}

static llvm::SmallVector<std::string, 16>
parseClosedRootSliceHandlerNames(llvm::StringRef model_text, uint64_t root_pc) {
  llvm::SmallVector<std::string, 16> handler_names;
  llvm::StringSet<> seen_names;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');
  const std::string prefix =
      (llvm::Twine("root-slice root=0x") + llvm::utohexstr(root_pc)).str();
  bool saw_matching_root = false;
  auto add_name = [&](llvm::StringRef name) {
    auto trimmed_name = name.trim();
    if (trimmed_name.empty())
      return;
    if (!seen_names.insert(trimmed_name).second)
      return;
    handler_names.push_back(trimmed_name.str());
  };
  bool in_root_block = false;
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (trimmed.starts_with(prefix)) {
      in_root_block = true;
      saw_matching_root = true;
      continue;
    }
    if (in_root_block && trimmed.starts_with("slice-handler ")) {
      add_name(trimmed.drop_front(strlen("slice-handler ")));
      continue;
    }
    if (saw_matching_root &&
        trimmed.starts_with("diag localized-continuation-shim ")) {
      if (auto fn = parseQuotedAttrValueFromLine(trimmed, "fn")) {
        add_name(*fn);
        continue;
      }
      constexpr llvm::StringLiteral pattern = "fn=";
      size_t pos = trimmed.find(pattern);
      if (pos != llvm::StringRef::npos) {
        pos += pattern.size();
        size_t end = pos;
        while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
          ++end;
        add_name(trimmed.slice(pos, end));
      }
      continue;
    }
    if (saw_matching_root &&
        trimmed.starts_with("diag localized-continuation-call-edge ")) {
      for (llvm::StringRef attr : {"caller", "callee"}) {
        if (auto name = parseQuotedAttrValueFromLine(trimmed, attr)) {
          add_name(*name);
          continue;
        }
        std::string pattern = (llvm::Twine(attr) + "=").str();
        size_t pos = trimmed.find(pattern);
        if (pos == llvm::StringRef::npos)
          continue;
        pos += pattern.size();
        size_t end = pos;
        while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
          ++end;
        add_name(trimmed.slice(pos, end));
      }
      continue;
    }
    if (saw_matching_root && trimmed.starts_with("diag lifted target=")) {
      size_t arrow = trimmed.rfind("->");
      if (arrow != llvm::StringRef::npos) {
        add_name(trimmed.drop_front(arrow + 2));
      }
      continue;
    }
    if (!in_root_block)
      continue;
    if (trimmed.starts_with("frontier ")) {
      continue;
    }
    if (trimmed.starts_with("region ") || trimmed.starts_with("root-slice ") ||
        trimmed.starts_with("slot ") || trimmed.starts_with("handler ") ||
        trimmed.empty()) {
      in_root_block = false;
    }
  }
  return handler_names;
}

static std::optional<uint64_t>
parseSyntheticBlockLikePcFromName(llvm::StringRef name) {
  if (auto pc = omill::extractEntryVA(name))
    return pc;
  for (llvm::StringRef prefix : {"blk_", "sub_", "block_", "vm_entry_"}) {
    if (!name.starts_with(prefix))
      continue;
    llvm::StringRef suffix = name.drop_front(prefix.size());
    size_t end = 0;
    while (end < suffix.size() && llvm::isHexDigit(suffix[end]))
      ++end;
    if (end == 0)
      continue;
    uint64_t pc = 0;
    if (!suffix.take_front(end).getAsInteger(16, pc))
      return pc;
  }
  return std::nullopt;
}

static llvm::SmallVector<uint64_t, 16>
parseLocalizedContinuationCalleePcs(llvm::StringRef model_text,
                                    uint64_t root_pc) {
  llvm::SmallVector<uint64_t, 16> callee_pcs;
  llvm::DenseSet<uint64_t> seen_pcs;
  llvm::StringSet<> slice_handlers;
  for (const auto &name : parseClosedRootSliceHandlerNames(model_text, root_pc))
    slice_handlers.insert(name);
  if (slice_handlers.empty())
    return callee_pcs;

  auto parseBareAttr = [&](llvm::StringRef line,
                           llvm::StringRef attr) -> llvm::StringRef {
    if (auto quoted = parseQuotedAttrValueFromLine(line, attr))
      return *quoted;
    std::string pattern = (llvm::Twine(attr) + "=").str();
    size_t pos = line.find(pattern);
    if (pos == llvm::StringRef::npos)
      return {};
    pos += pattern.size();
    size_t end = pos;
    while (end < line.size() && !llvm::isSpace(line[end]))
      ++end;
    return line.slice(pos, end);
  };

  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (!trimmed.starts_with("diag localized-continuation-call-edge "))
      continue;
    llvm::StringRef caller = parseBareAttr(trimmed, "caller");
    llvm::StringRef callee = parseBareAttr(trimmed, "callee");
    if (caller.empty() || callee.empty())
      continue;
    if (!slice_handlers.count(caller))
      continue;
    auto callee_pc = parseSyntheticBlockLikePcFromName(callee);
    if (!callee_pc || *callee_pc == root_pc)
      continue;
    if (!seen_pcs.insert(*callee_pc).second)
      continue;
    callee_pcs.push_back(*callee_pc);
  }
  return callee_pcs;
}

static llvm::SmallVector<uint64_t, 16>
parseRootSliceFrontierTargetPcs(llvm::StringRef model_text, uint64_t root_pc) {
  llvm::SmallVector<uint64_t, 16> target_pcs;
  llvm::DenseSet<uint64_t> seen_pcs;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');

  bool in_root_block = false;
  auto add_pc = [&](llvm::StringRef value) {
    if (value.empty())
      return;
    if (value.consume_front("0x"))
      ;
    uint64_t pc = 0;
    if (value.getAsInteger(16, pc))
      return;
    if (seen_pcs.insert(pc).second)
      target_pcs.push_back(pc);
  };

  for (auto line : lines) {
    auto trimmed = line.trim();
    if (trimmed.starts_with("root-slice root=")) {
      in_root_block = false;
      auto root_value = parseQuotedAttrValueFromLine(trimmed, "root");
      llvm::StringRef root_text;
      if (root_value) {
        root_text = *root_value;
      } else {
        constexpr llvm::StringLiteral pattern = "root=";
        size_t pos = trimmed.find(pattern);
        if (pos != llvm::StringRef::npos) {
          pos += pattern.size();
          size_t end = pos;
          while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
            ++end;
          root_text = trimmed.slice(pos, end);
        }
      }
      uint64_t parsed_root = 0;
      if (!root_text.empty()) {
        if (root_text.consume_front("0x"))
          ;
        if (!root_text.getAsInteger(16, parsed_root) && parsed_root == root_pc)
          in_root_block = true;
      }
      continue;
    }
    if (!in_root_block)
      continue;
    if (trimmed.starts_with("frontier ")) {
      if (!trimmed.contains("kind=dispatch"))
        continue;
      if (auto canonical = parseQuotedAttrValueFromLine(trimmed, "canonical")) {
        add_pc(*canonical);
        continue;
      }
      if (auto target = parseQuotedAttrValueFromLine(trimmed, "target")) {
        add_pc(*target);
        continue;
      }
      for (llvm::StringRef attr : {"canonical", "target"}) {
        std::string pattern = (llvm::Twine(attr) + "=").str();
        size_t pos = trimmed.find(pattern);
        if (pos == llvm::StringRef::npos)
          continue;
        pos += pattern.size();
        size_t end = pos;
        while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
          ++end;
        add_pc(trimmed.slice(pos, end));
        if (!target_pcs.empty() && seen_pcs.contains(target_pcs.back()))
          break;
      }
      continue;
    }
    if (trimmed.starts_with("region ") || trimmed.starts_with("root-slice ") ||
        trimmed.starts_with("slot ") || trimmed.starts_with("handler ") ||
        trimmed.empty()) {
      in_root_block = false;
    }
  }
  return target_pcs;
}

static bool isTerminalRecoveryFrontierReason(llvm::StringRef reason) {
  return reason == "call_target_import_pointer" ||
         reason == "call_target_not_executable_in_image" ||
         reason == "call_target_out_of_image" ||
         reason == "call_target_undecodable" ||
         reason == "dispatch_target_not_executable" ||
         reason == "dispatch_target_undecodable";
}

static bool isExecutableRecoveryFrontierReason(llvm::StringRef reason) {
  return reason == "dispatch_target_unlifted" ||
         reason == "dispatch_target_nearby_unlifted" ||
         reason == "call_target_unlifted" ||
         reason == "call_target_nearby_unlifted";
}

static std::optional<uint64_t> selectFollowupRecoveryTarget(
    const TerminalBoundaryRecoveryModelSummary &summary) {
  std::optional<uint64_t> executable_target;
  std::optional<uint64_t> first_executable_target;
  std::optional<uint64_t> first_dispatch_target;
  std::optional<uint64_t> unique_dispatch_target;
  for (const auto &frontier : summary.frontiers) {
    if (frontier.reason.empty())
      continue;
    if (isTerminalRecoveryFrontierReason(frontier.reason))
      continue;
    if (!isExecutableRecoveryFrontierReason(frontier.reason))
      return std::nullopt;
    uint64_t target =
        frontier.canonical_target_va.value_or(frontier.target_pc.value_or(0));
    if (!target)
      return std::nullopt;
    if (!first_executable_target)
      first_executable_target = target;
    if (llvm::StringRef(frontier.reason).starts_with("dispatch_target_")) {
      if (!first_dispatch_target)
        first_dispatch_target = target;
      if (unique_dispatch_target && *unique_dispatch_target != target) {
        unique_dispatch_target = std::nullopt;
      } else if (!unique_dispatch_target) {
        unique_dispatch_target = target;
      }
    }
    if (executable_target && *executable_target != target)
      break;
    executable_target = target;
  }
  if (unique_dispatch_target)
    return unique_dispatch_target;
  if (executable_target)
    return executable_target;
  if (first_dispatch_target)
    return first_dispatch_target;
  return first_executable_target;
}

bool wantVerboseDriverLogs() {
  if (VerboseRemillLogs)
    return true;
  if (auto v = parseBoolEnv("OMILL_VERBOSE_LOGS"); v.has_value())
    return *v;
  if (auto v = parseBoolEnv("OMILL_VERBOSE_REMILL_LOGS"); v.has_value())
    return *v;
  return false;
}

void configureDriverLogging(const char *argv0) {
#if OMILL_LIFT_HAS_GLOG
  static bool glog_inited = false;
  if (!glog_inited) {
    google::InitGoogleLogging(argv0);
    glog_inited = true;
  }
#endif

  if (wantVerboseDriverLogs())
    return;

  setEnvIfUnset("GLOG_minloglevel", "2");
  setEnvIfUnset("GLOG_stderrthreshold", "3");
#if OMILL_LIFT_HAS_GLOG
  if (FLAGS_minloglevel < 2)
    FLAGS_minloglevel = 2;
  if (FLAGS_stderrthreshold < 3)
    FLAGS_stderrthreshold = 3;
#endif
}

class LiftEventLogger {
 public:
  using EventKV = llvm::json::Object::KV;

  LiftEventLogger() = default;

  bool init(llvm::StringRef sink_path, llvm::StringRef detail_text,
            llvm::StringRef input_file) {
    if (sink_path.empty()) {
      enabled_ = false;
      return true;
    }
    auto parsed = omill::tools::parseEventDetailLevel(detail_text);
    if (!parsed) {
      errs() << "Invalid --event-detail: " << detail_text
             << " (expected basic|detailed)\n";
      return false;
    }
    detail_ = *parsed;
    enabled_ = true;
    run_id_ = buildRunId(input_file);

    if (sink_path == "-") {
      os_ = &outs();
      return true;
    }

    std::error_code ec;
    file_ = std::make_unique<raw_fd_ostream>(sink_path, ec, sys::fs::OF_Text);
    if (ec) {
      errs() << "Error opening --event-jsonl output '" << sink_path
             << "': " << ec.message() << "\n";
      return false;
    }
    os_ = file_.get();
    return true;
  }

  bool enabled() const { return enabled_; }
  bool detailed() const { return detail_ == omill::tools::EventDetailLevel::kDetailed; }
  llvm::StringRef runId() const { return run_id_; }

  void emit(llvm::StringRef kind, llvm::StringRef severity,
            llvm::StringRef message = "",
            llvm::json::Object payload = {}) {
    if (!enabled_ || !os_)
      return;
    omill::tools::LiftRunEvent event;
    event.run_id = run_id_;
    event.seq = ++seq_;
    event.timestamp_ms = nowMs();
    event.kind = kind.str();
    event.severity = severity.str();
    event.message = message.str();
    event.payload = std::move(payload);
    *os_ << llvm::json::Value(omill::tools::toJSON(event)) << "\n";
    os_->flush();
  }

  void emitInfo(llvm::StringRef kind, llvm::StringRef message = "",
                llvm::json::Object payload = {}) {
    emit(kind, "info", message, std::move(payload));
  }
  void emitInfo(llvm::StringRef kind, llvm::StringRef message,
                std::initializer_list<EventKV> payload) {
    emit(kind, "info", message, llvm::json::Object(payload));
  }

  void emitWarn(llvm::StringRef kind, llvm::StringRef message = "",
                llvm::json::Object payload = {}) {
    emit(kind, "warning", message, std::move(payload));
  }
  void emitWarn(llvm::StringRef kind, llvm::StringRef message,
                std::initializer_list<EventKV> payload) {
    emit(kind, "warning", message, llvm::json::Object(payload));
  }

  void emitError(llvm::StringRef kind, llvm::StringRef message = "",
                 llvm::json::Object payload = {}) {
    emit(kind, "error", message, std::move(payload));
  }
  void emitError(llvm::StringRef kind, llvm::StringRef message,
                 std::initializer_list<EventKV> payload) {
    emit(kind, "error", message, llvm::json::Object(payload));
  }

  void emitTerminalSuccess(llvm::StringRef output_file) {
    llvm::json::Object payload;
    payload["status"] = "success";
    payload["output_file"] = output_file;
    emitInfo("run_done", "completed", std::move(payload));
  }

  void emitTerminalFailure(int exit_code, llvm::StringRef reason) {
    llvm::json::Object payload;
    payload["status"] = "failed";
    payload["exit_code"] = exit_code;
    payload["reason"] = reason;
    emitError("run_done", "failed", std::move(payload));
  }

 private:
  static int64_t nowMs() {
    auto now = std::chrono::system_clock::now().time_since_epoch();
    return std::chrono::duration_cast<std::chrono::milliseconds>(now).count();
  }

  static std::string buildRunId(llvm::StringRef input_file) {
    auto ms = nowMs();
    uint64_t pid = static_cast<uint64_t>(llvm::sys::Process::getProcessId());
    std::string basename = input_file.str();
    size_t slash = basename.find_last_of("/\\");
    if (slash != std::string::npos)
      basename = basename.substr(slash + 1);
    return ("run_" + std::to_string(ms) + "_" + std::to_string(pid) +
            "_" + basename);
  }

  bool enabled_ = false;
  omill::tools::EventDetailLevel detail_ = omill::tools::EventDetailLevel::kBasic;
  std::string run_id_;
  uint64_t seq_ = 0;
  raw_ostream *os_ = nullptr;
  std::unique_ptr<raw_fd_ostream> file_;
};

static void emitIterativeSessionEvents(
    LiftEventLogger &events,
    const std::shared_ptr<omill::IterativeLiftingSession> &session,
    llvm::StringRef stage) {
  if (!events.enabled() || !events.detailed() || !session)
    return;

  for (const auto &round : session->roundSummaries()) {
    events.emitInfo(
        "iterative_round", "iterative resolution round",
        {{"stage", stage.str()},
         {"pipeline", round.pipeline},
         {"iteration", static_cast<int64_t>(round.iteration)},
         {"dirty_before", static_cast<int64_t>(round.dirty_functions)},
         {"dirty_after", static_cast<int64_t>(round.dirty_functions_after)},
         {"affected_functions",
          static_cast<int64_t>(round.affected_functions)},
         {"optimized_functions",
          static_cast<int64_t>(round.optimized_functions)},
         {"unresolved_before",
          static_cast<int64_t>(round.unresolved_before)},
         {"unresolved_after", static_cast<int64_t>(round.unresolved_after)},
         {"new_targets", static_cast<int64_t>(round.new_targets)},
         {"pending_targets", static_cast<int64_t>(round.pending_targets)},
         {"dynamic_unresolved",
          static_cast<int64_t>(round.dynamic_unresolved)},
         {"missing_targets", static_cast<int64_t>(round.missing_targets)},
         {"blocked_unresolved", static_cast<int64_t>(round.blocked_unresolved)},
         {"total_ms", static_cast<int64_t>(round.total_ms)},
         {"optimize_ms", static_cast<int64_t>(round.optimize_ms)},
         {"resolve_ms", static_cast<int64_t>(round.resolve_ms)},
         {"ipcp_ms", static_cast<int64_t>(round.ipcp_ms)},
         {"lift_ms", static_cast<int64_t>(round.lift_ms)},
         {"lower_ms", static_cast<int64_t>(round.lower_ms)},
         {"inline_ms", static_cast<int64_t>(round.inline_ms)},
         {"reverse_inline_ms",
          static_cast<int64_t>(round.reverse_inline_ms)},
         {"ipcp_changed", round.ipcp_changed},
         {"lifted_new", round.lifted_new},
         {"stalled", round.stalled}});
  }
}

static const char *runtimeArtifactStageName(
    omill::RuntimeArtifactStage stage) {
  switch (stage) {
    case omill::RuntimeArtifactStage::kFrontierRound:
      return "frontier_round";
    case omill::RuntimeArtifactStage::kOutputRecoveryRound:
      return "output_recovery_round";
    case omill::RuntimeArtifactStage::kOutputRecoveryImportRound:
      return "output_recovery_import_round";
    case omill::RuntimeArtifactStage::kFinalization:
      return "finalization";
  }
  return "unknown";
}

static const char *importEligibilityName(omill::ImportEligibility eligibility) {
  switch (eligibility) {
    case omill::ImportEligibility::kImportable:
      return "importable";
    case omill::ImportEligibility::kRetryable:
      return "retryable";
    case omill::ImportEligibility::kRejected:
      return "rejected";
  }
  return "rejected";
}

static const char *recoveryRejectionReasonName(
    omill::RecoveryRejectionReason reason) {
  switch (reason) {
    case omill::RecoveryRejectionReason::kNone:
      return "none";
    case omill::RecoveryRejectionReason::kChildLiftFailed:
      return "child_lift_failed";
    case omill::RecoveryRejectionReason::kImportFailed:
      return "import_failed";
    case omill::RecoveryRejectionReason::kTypeMismatch:
      return "type_mismatch";
    case omill::RecoveryRejectionReason::kParseFailed:
      return "parse_failed";
    case omill::RecoveryRejectionReason::kMissingRoot:
      return "missing_root";
    case omill::RecoveryRejectionReason::kDisallowedFunction:
      return "disallowed_function";
    case omill::RecoveryRejectionReason::kDeclarationRejected:
      return "declaration_rejected";
    case omill::RecoveryRejectionReason::kGlobalRejected:
      return "global_rejected";
    case omill::RecoveryRejectionReason::kRuntimeLeak:
      return "runtime_leak";
    case omill::RecoveryRejectionReason::kNotSelfContained:
      return "not_self_contained";
    case omill::RecoveryRejectionReason::kUnsupported:
      return "unsupported";
  }
  return "unsupported";
}

static std::string hexString(uint64_t value) {
  return ("0x" + Twine::utohexstr(value)).str();
}

static llvm::json::Array jsonStringArray(
    const std::vector<std::string> &values) {
  llvm::json::Array arr;
  for (const auto &value : values)
    arr.push_back(value);
  return arr;
}

static llvm::json::Array jsonPcArray(const std::vector<uint64_t> &values) {
  llvm::json::Array arr;
  for (uint64_t value : values)
    arr.push_back(hexString(value));
  return arr;
}

static llvm::json::Array jsonRejectedImportArray(
    const std::vector<omill::RejectedImportArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["target_pc"] = hexString(artifact.target_pc);
    obj["reason"] = recoveryRejectionReasonName(artifact.reason);
    obj["detail"] = artifact.detail;
    arr.push_back(std::move(obj));
  }
  return arr;
}

static llvm::json::Array jsonImportDecisionArray(
    const std::vector<omill::ImportDecisionArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["label"] = artifact.label;
    obj["target_pc"] = hexString(artifact.target_pc);
    obj["eligibility"] = importEligibilityName(artifact.eligibility);
    obj["rejection_reason"] =
        recoveryRejectionReasonName(artifact.rejection_reason);
    if (artifact.selected_root_pc)
      obj["selected_root_pc"] = hexString(*artifact.selected_root_pc);
    if (artifact.import_class)
      obj["import_class"] = omill::toString(*artifact.import_class);
    obj["proof_summary"] = artifact.proof_summary;
    obj["resolution_summary"] = artifact.resolution_summary;
    obj["detail"] = artifact.detail;
    obj["imported"] = artifact.imported;
    arr.push_back(std::move(obj));
  }
  return arr;
}

static llvm::json::Array jsonCleanupActionArray(
    const std::vector<omill::CleanupActionArtifact> &artifacts) {
  llvm::json::Array arr;
  for (const auto &artifact : artifacts) {
    llvm::json::Object obj;
    obj["label"] = artifact.label;
    obj["changed"] = artifact.changed;
    obj["detail"] = artifact.detail;
    arr.push_back(std::move(obj));
  }
  return arr;
}

static llvm::json::Array jsonPlannedRecoveryActionArray(
    const std::vector<omill::FinalStateRecoveryAction> &actions) {
  llvm::json::Array arr;
  for (const auto &action : actions) {
    llvm::json::Object obj;
    obj["kind"] = omill::toString(action.kind);
    obj["target_pc"] = hexString(action.target_pc);
    obj["source_stage"] = runtimeArtifactStageName(action.source_stage);
    obj["source_label"] = action.source_label;
    obj["final_state_class"] = action.final_state_class;
    obj["reason"] = action.reason;
    obj["retry_budget"] = static_cast<int64_t>(action.retry_budget);
    obj["planned_resolver_path"] = action.planned_resolver_path;
    obj["expected_outcome"] = action.expected_outcome;
    arr.push_back(std::move(obj));
  }
  return arr;
}

static llvm::json::Array jsonExecutedRecoveryActionArray(
    const std::vector<omill::ExecutedRecoveryActionArtifact> &actions) {
  llvm::json::Array arr;
  for (const auto &action : actions) {
    llvm::json::Object obj;
    obj["kind"] = omill::toString(action.kind);
    obj["target_pc"] = hexString(action.target_pc);
    obj["attempted"] = action.attempted;
    obj["disposition"] = omill::toString(action.disposition);
    obj["detail"] = action.detail;
    obj["module_changed"] = action.module_changed;
    arr.push_back(std::move(obj));
  }
  return arr;
}

static llvm::json::Object jsonRecoveryQualitySummary(
    const omill::RecoveryQualitySummary &summary) {
  llvm::json::Object obj;
  obj["structurally_closed"] = summary.structurally_closed;
  obj["functionally_recovered"] = summary.functionally_recovered;
  obj["dispatcher_heavy"] = summary.dispatcher_heavy;
  obj["terminal_modeled_targets"] =
      jsonPcArray(summary.terminal_modeled_targets);
  obj["terminal_modeled_children"] =
      jsonPcArray(summary.terminal_modeled_children);
  obj["modeled_reentry_boundaries"] =
      jsonPcArray(summary.modeled_reentry_boundaries);
  obj["accepted_external_leaf_calls"] =
      jsonStringArray(summary.accepted_external_leaf_calls);
  obj["hard_rejected_targets"] =
      jsonPcArray(summary.hard_rejected_targets);
  return obj;
}

static void emitRuntimeArtifactBundleEvents(
    LiftEventLogger &events, llvm::StringRef source,
    const std::vector<omill::RoundArtifactBundle> &bundles) {
  if (!events.enabled() || !events.detailed())
    return;
  for (const auto &bundle : bundles) {
    llvm::json::Object payload;
    payload["source"] = source.str();
    payload["stage"] = runtimeArtifactStageName(bundle.stage);
    payload["label"] = bundle.label;
    if (bundle.round)
      payload["round"] = static_cast<int64_t>(*bundle.round);
    payload["module_fingerprint"] = hexString(bundle.module_fingerprint);
    payload["changed"] = bundle.changed;
    payload["output_root_names"] = jsonStringArray(bundle.output_root_names);
    payload["executable_placeholder_targets"] =
        jsonPcArray(bundle.executable_placeholder_targets);
    payload["native_boundary_targets"] =
        jsonPcArray(bundle.native_boundary_targets);
    payload["remill_runtime_callees"] =
        jsonStringArray(bundle.remill_runtime_callees);
    payload["external_callees"] = jsonStringArray(bundle.external_callees);
    payload["imported_targets"] = jsonPcArray(bundle.imported_targets);
    payload["rejected_imports"] =
        jsonRejectedImportArray(bundle.rejected_imports);
    payload["import_decisions"] =
        jsonImportDecisionArray(bundle.import_decisions);
    payload["cleanup_actions"] =
        jsonCleanupActionArray(bundle.cleanup_actions);
    payload["planned_recovery_actions"] =
        jsonPlannedRecoveryActionArray(bundle.planned_recovery_actions);
    payload["executed_recovery_actions"] =
        jsonExecutedRecoveryActionArray(bundle.executed_recovery_actions);
    payload["recovery_quality"] =
        jsonRecoveryQualitySummary(bundle.recovery_quality);
    payload["notes"] = jsonStringArray(bundle.notes);
    events.emitInfo("runtime_artifact_bundle", "runtime artifact bundle",
                    std::move(payload));
  }
}

static std::string runtimeArtifactReportPath(llvm::StringRef output_path) {
  llvm::SmallString<256> report_path(output_path);
  llvm::sys::path::replace_extension(report_path, ".artifacts.txt");
  return std::string(report_path.str());
}

static void appendReportLine(raw_ostream &os, llvm::StringRef text,
                             unsigned indent = 0) {
  for (unsigned i = 0; i < indent; ++i)
    os << ' ';
  os << text << '\n';
}

static void appendReportStringList(raw_ostream &os, llvm::StringRef label,
                                   const std::vector<std::string> &values,
                                   unsigned indent = 0) {
  if (values.empty())
    return;
  appendReportLine(os, label, indent);
  for (const auto &value : values)
    appendReportLine(os, value, indent + 2);
}

static void appendReportPcList(raw_ostream &os, llvm::StringRef label,
                               const std::vector<uint64_t> &values,
                               unsigned indent = 0) {
  if (values.empty())
    return;
  appendReportLine(os, label, indent);
  for (uint64_t value : values)
    appendReportLine(os, hexString(value), indent + 2);
}

static void appendReportPcListWithEmpty(raw_ostream &os, llvm::StringRef label,
                                        const std::vector<uint64_t> &values,
                                        unsigned indent = 0) {
  appendReportLine(os, label, indent);
  if (values.empty()) {
    appendReportLine(os, "<none>", indent + 2);
    return;
  }
  for (uint64_t value : values)
    appendReportLine(os, hexString(value), indent + 2);
}

static void appendUniqueStringValue(std::vector<std::string> &dst,
                                    llvm::StringRef value) {
  if (value.empty())
    return;
  const auto value_str = value.str();
  if (llvm::find(dst, value_str) == dst.end())
    dst.push_back(value_str);
}

static void appendUniquePcValue(std::vector<uint64_t> &dst, uint64_t value) {
  if (!value)
    return;
  if (llvm::find(dst, value) == dst.end())
    dst.push_back(value);
}

static bool writeRuntimeArtifactReport(
    llvm::StringRef output_path,
    const std::vector<omill::RoundArtifactBundle> &bundles,
    const std::optional<omill::ProtectorValidationReport> &protector_report,
    std::string *written_path = nullptr) {
  if (output_path.empty() || output_path == "-")
    return false;

  const auto report_path = runtimeArtifactReportPath(output_path);
  std::error_code ec;
  ToolOutputFile out(report_path, ec, sys::fs::OF_Text);
  if (ec)
    return false;

  auto &os = out.os();
  appendReportLine(os, "OMILL Runtime Artifact Report");
  appendReportLine(os, (llvm::Twine("Output: ") + output_path).str());
  appendReportLine(os, (llvm::Twine("Bundles: ") +
                        llvm::Twine(static_cast<uint64_t>(bundles.size())))
                           .str());
  os << '\n';

  if (!bundles.empty()) {
    const auto &final_bundle = bundles.back();
    std::vector<uint64_t> imported_targets;
    std::vector<std::string> final_rejections;
    for (const auto &bundle : bundles) {
      for (uint64_t target : bundle.imported_targets)
        appendUniquePcValue(imported_targets, target);
    }
    for (const auto &decision : final_bundle.import_decisions) {
      if (decision.imported ||
          decision.eligibility == omill::ImportEligibility::kImportable) {
        continue;
      }
      std::string line =
          (llvm::Twine("target=") + hexString(decision.target_pc) +
           " eligibility=" + importEligibilityName(decision.eligibility) +
           " reason=" +
           recoveryRejectionReasonName(decision.rejection_reason) +
           (decision.detail.empty() ? "" : " detail=" + decision.detail))
              .str();
      appendUniqueStringValue(final_rejections, line);
    }
    for (const auto &rejected : final_bundle.rejected_imports) {
      std::string line =
          (llvm::Twine("target=") + hexString(rejected.target_pc) +
           " reason=" + recoveryRejectionReasonName(rejected.reason) +
           (rejected.detail.empty() ? "" : " detail=" + rejected.detail))
              .str();
      appendUniqueStringValue(final_rejections, line);
    }

    appendReportLine(os, "Final State");
    appendReportLine(
        os, (llvm::Twine("  Latest Bundle: ") + final_bundle.label).str());
    appendReportLine(
        os, (llvm::Twine("  Latest Stage: ") +
             runtimeArtifactStageName(final_bundle.stage))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Final Fingerprint: ") +
             hexString(final_bundle.module_fingerprint))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Final Changed: ") +
             (final_bundle.changed ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Structurally Closed: ") +
             (final_bundle.recovery_quality.structurally_closed ? "true"
                                                                : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Functionally Recovered: ") +
             (final_bundle.recovery_quality.functionally_recovered ? "true"
                                                                   : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Dispatcher Heavy: ") +
             (final_bundle.recovery_quality.dispatcher_heavy ? "true"
                                                             : "false"))
                .str());
    appendReportStringList(os, "  Final Output Roots:",
                           final_bundle.output_root_names);
    appendReportPcList(os, "  Final Executable Placeholders:",
                       final_bundle.executable_placeholder_targets, 2);
    appendReportPcList(os, "  Final Native Boundaries:",
                       final_bundle.native_boundary_targets, 2);
    appendReportStringList(os, "  Final External Callees:",
                           final_bundle.external_callees, 2);
    appendReportStringList(os, "  Final Remill Runtime Callees:",
                           final_bundle.remill_runtime_callees, 2);
    appendReportPcList(os, "  Imported Targets Across Rounds:", imported_targets,
                       2);
    appendReportPcListWithEmpty(
        os, "  Terminal Modeled Imported Targets:",
        final_bundle.recovery_quality.terminal_modeled_children, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled Reentry Boundaries:",
        final_bundle.recovery_quality.modeled_reentry_boundaries, 2);
    appendReportStringList(os, "  Accepted External Leaf Calls:",
                           final_bundle.recovery_quality
                               .accepted_external_leaf_calls,
                           2);
    appendReportPcListWithEmpty(
        os, "  Hard Rejected Targets:",
        final_bundle.recovery_quality.hard_rejected_targets, 2);
    appendReportStringList(os, "  Final Rejected Continuations:",
                           final_rejections, 2);
    appendReportLine(os, "  Final State Recovery Plan:");
    if (!final_bundle.planned_recovery_actions.empty()) {
      for (const auto &action : final_bundle.planned_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 (action.reason.empty() ? "" : " reason=" + action.reason))
                    .str());
      }
    } else {
      appendReportLine(os, "    <none>");
    }
    appendReportLine(os, "  Final State Recovery Outcomes:");
    if (!final_bundle.executed_recovery_actions.empty()) {
      for (const auto &action : final_bundle.executed_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " disposition=" + omill::toString(action.disposition) +
                 " attempted=" + (action.attempted ? "true" : "false") +
                 (action.detail.empty() ? "" : " detail=" + action.detail))
                    .str());
      }
    } else {
      appendReportLine(os, "    <none>");
    }
    if (protector_report) {
      appendReportLine(
          os, (llvm::Twine("  Protector Issue Count: ") +
               llvm::Twine(
                   static_cast<uint64_t>(protector_report->issues.size())))
                  .str());
    }
    os << '\n';
  }

  for (size_t i = 0; i < bundles.size(); ++i) {
    const auto &bundle = bundles[i];
    appendReportLine(
        os, (llvm::Twine("Bundle ") + llvm::Twine(i + 1) + ": " + bundle.label)
                .str());
    appendReportLine(
        os, (llvm::Twine("  Stage: ") + runtimeArtifactStageName(bundle.stage))
                .str());
    if (bundle.round) {
      appendReportLine(
          os, (llvm::Twine("  Round: ") + llvm::Twine(*bundle.round)).str());
    }
    appendReportLine(
        os, (llvm::Twine("  Changed: ") + (bundle.changed ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Module Fingerprint: ") +
             hexString(bundle.module_fingerprint))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Structurally Closed: ") +
             (bundle.recovery_quality.structurally_closed ? "true" : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Functionally Recovered: ") +
             (bundle.recovery_quality.functionally_recovered ? "true"
                                                             : "false"))
                .str());
    appendReportLine(
        os, (llvm::Twine("  Dispatcher Heavy: ") +
             (bundle.recovery_quality.dispatcher_heavy ? "true" : "false"))
                .str());
    appendReportStringList(os, "  Output Roots:", bundle.output_root_names);
    appendReportPcList(os, "  Executable Placeholders:",
                       bundle.executable_placeholder_targets, 2);
    appendReportPcList(os, "  Native Boundaries:", bundle.native_boundary_targets,
                       2);
    appendReportPcListWithEmpty(
        os, "  Terminal Modeled Targets:",
        bundle.recovery_quality.terminal_modeled_children, 2);
    appendReportPcListWithEmpty(
        os, "  Modeled Reentry Boundaries:",
        bundle.recovery_quality.modeled_reentry_boundaries, 2);
    appendReportStringList(os, "  Accepted External Leaf Calls:",
                           bundle.recovery_quality.accepted_external_leaf_calls,
                           2);
    appendReportPcListWithEmpty(
        os, "  Hard Rejected Targets:",
        bundle.recovery_quality.hard_rejected_targets, 2);
    appendReportStringList(os, "  Remill Runtime Callees:",
                           bundle.remill_runtime_callees, 2);
    appendReportStringList(os, "  External Callees:", bundle.external_callees,
                           2);
    appendReportPcList(os, "  Imported Targets:", bundle.imported_targets, 2);
    if (!bundle.import_decisions.empty()) {
      appendReportLine(os, "  Import Decisions:");
      for (const auto &decision : bundle.import_decisions) {
        std::string line =
            (llvm::Twine("    ") + decision.label + " target=" +
             hexString(decision.target_pc) +
             " eligibility=" + importEligibilityName(decision.eligibility) +
             " imported=" + (decision.imported ? "true" : "false"))
                .str();
        appendReportLine(os, line);
        if (decision.selected_root_pc) {
          appendReportLine(
              os, (llvm::Twine("      selected_root=") +
                   hexString(*decision.selected_root_pc))
                      .str());
        }
        if (decision.import_class) {
          appendReportLine(
              os, (llvm::Twine("      import_class=") +
                   omill::toString(*decision.import_class))
                      .str());
        }
        if (!decision.proof_summary.empty())
          appendReportLine(
              os, (llvm::Twine("      proof=") + decision.proof_summary).str());
        if (!decision.resolution_summary.empty())
          appendReportLine(
              os,
              (llvm::Twine("      resolution=") + decision.resolution_summary)
                  .str());
        if (!decision.detail.empty()) {
          appendReportLine(
              os, (llvm::Twine("      detail=") + decision.detail).str());
        } else if (decision.rejection_reason !=
                   omill::RecoveryRejectionReason::kNone) {
          appendReportLine(
              os, (llvm::Twine("      rejection_reason=") +
                   recoveryRejectionReasonName(decision.rejection_reason))
                      .str());
        }
      }
    }
    if (!bundle.rejected_imports.empty()) {
      appendReportLine(os, "  Rejected Imports:");
      for (const auto &rejected : bundle.rejected_imports) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(rejected.target_pc) +
                 " reason=" +
                 recoveryRejectionReasonName(rejected.reason) +
                 (rejected.detail.empty() ? "" : " detail=" + rejected.detail))
                    .str());
      }
    }
    if (!bundle.cleanup_actions.empty()) {
      appendReportLine(os, "  Cleanup Actions:");
      for (const auto &cleanup : bundle.cleanup_actions) {
        appendReportLine(
            os, (llvm::Twine("    ") + cleanup.label + " changed=" +
                 (cleanup.changed ? "true" : "false") +
                 (cleanup.detail.empty() ? "" : " detail=" + cleanup.detail))
                    .str());
      }
    }
    if (!bundle.planned_recovery_actions.empty()) {
      appendReportLine(os, "  Final State Recovery Plan:");
      for (const auto &action : bundle.planned_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 " final_state_class=" + action.final_state_class +
                 " retry_budget=" + llvm::Twine(action.retry_budget) +
                 (action.reason.empty() ? "" : " reason=" + action.reason))
                    .str());
        if (!action.planned_resolver_path.empty()) {
          appendReportLine(
              os, (llvm::Twine("      resolver_path=") +
                   action.planned_resolver_path)
                      .str());
        }
        if (!action.expected_outcome.empty()) {
          appendReportLine(
              os, (llvm::Twine("      expected_outcome=") +
                   action.expected_outcome)
                      .str());
        }
      }
    }
    if (!bundle.executed_recovery_actions.empty()) {
      appendReportLine(os, "  Final State Recovery Outcomes:");
      for (const auto &action : bundle.executed_recovery_actions) {
        appendReportLine(
            os, (llvm::Twine("    target=") + hexString(action.target_pc) +
                 " kind=" + omill::toString(action.kind) +
                 " disposition=" + omill::toString(action.disposition) +
                 " attempted=" + (action.attempted ? "true" : "false") +
                 " changed=" + (action.module_changed ? "true" : "false") +
                 (action.detail.empty() ? "" : " detail=" + action.detail))
                    .str());
      }
    }
    appendReportStringList(os, "  Notes:", bundle.notes, 2);
    os << '\n';
  }

  if (protector_report) {
    appendReportLine(os, "Protector Validation Report");
    appendReportLine(
        os,
        (llvm::Twine("  Issue Count: ") +
         llvm::Twine(static_cast<uint64_t>(protector_report->issues.size())))
            .str());
    if (!protector_report->counts_by_class.empty()) {
      appendReportLine(os, "  Counts By Class:");
      for (const auto &[klass, count] : protector_report->counts_by_class) {
        appendReportLine(
            os, (llvm::Twine("    ") + klass + "=" + llvm::Twine(count)).str());
      }
    }
    if (!protector_report->issues.empty()) {
      appendReportLine(os, "  Issues:");
      for (const auto &issue : protector_report->issues) {
        appendReportLine(
            os, (llvm::Twine("    ") + omill::toString(issue.issue_class) +
                 " " + issue.message)
                    .str());
      }
    }
  }

  out.keep();
  if (written_path)
    *written_path = report_path;
  return true;
}

/// In-memory trace manager for remill lifting.
class BufferTraceManager : public omill::TraceManager {
 public:
  void setCode(const uint8_t *data, size_t size, uint64_t base) {
    code_[base] = {data, data + size};
    base_addr_ = base;
  }

  void setBaseAddr(uint64_t addr) { base_addr_ = addr; }
  uint64_t baseAddr() const { return base_addr_; }
  void setBinaryMemoryMap(const omill::BinaryMemoryMap *memory_map) {
    memory_map_ = memory_map;
  }
  void setTargetArch(omill::TargetArch arch) { target_arch_ = arch; }

  /// Must be called after the module and arch are created so that
  /// shallow-lift mode can create proper function declarations.
  void setModuleAndArch(llvm::Module *m, const remill::Arch *a) {
    module_ = m;
    arch_ = a;
  }

  void SetLiftedTraceDefinition(uint64_t addr,
                                llvm::Function *func) override {
    lifted_[addr] = func;
    ++lift_count_;
  }

  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr) override {
    auto it = lifted_.find(addr);
    if (it == lifted_.end())
      return nullptr;
    auto *func = llvm::dyn_cast_or_null<llvm::Function>(it->second);
    if (!func)
      lifted_.erase(it);
    return func;
  }

  llvm::Function *GetLiftedTraceDefinition(uint64_t addr) override {
    // In shallow mode, report all addresses outside the root set as
    // "already lifted" to prevent recursive lifting of the entire
    // call graph.  This is used for late target discovery where we
    // only need the target function, not its callees.
    if (max_lift_count_ > 0 && lift_count_ >= max_lift_count_) {
      auto it = lifted_.find(addr);
      if (it != lifted_.end()) {
        auto *func = llvm::dyn_cast_or_null<llvm::Function>(it->second);
        if (!func)
          lifted_.erase(it);
        else
          return func;
      }
      // Create a real declaration so the TraceLifter can safely
      // dereference the returned pointer (it checks getParent()).
      auto *decl = arch_->DeclareLiftedFunction(TraceName(addr), module_);
      lifted_[addr] = decl;
      return decl;
    }
    return GetLiftedTraceDeclaration(addr);
  }

  /// Set maximum number of traces to lift per Lift() call.  0 = unlimited.
  void setMaxLiftCount(unsigned n) { max_lift_count_ = n; }
  void resetLiftCount() { lift_count_ = 0; }

  bool TryReadExecutableByte(uint64_t addr, uint8_t *out) override {
    for (auto &[base, data] : code_) {
      if (addr >= base && addr < base + data.size()) {
        *out = data[addr - base];
        return true;
      }
    }
    return false;
  }

  omill::LiftTargetDecision ResolveLiftTarget(
      uint64_t source_pc, uint64_t raw_target_pc,
      omill::LiftTargetEdgeKind edge_kind) override {
    return getLiftTargetPolicy()->ResolveLiftTarget(source_pc, raw_target_pc,
                                                    edge_kind);
  }

  omill::DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_addr, uint64_t failed_pc,
      const omill::DecodeFailureContext &ctx) override {
    llvm::SmallVector<uint64_t, 16> known_entries;
    known_entries.reserve(lifted_.size());
    for (const auto &[candidate_pc, candidate_vh] : lifted_) {
      (void)candidate_vh;
      known_entries.push_back(candidate_pc);
    }
    return getLiftTargetPolicy()->ResolveDecodeFailure(source_addr, failed_pc,
                                                       known_entries, ctx);
  }

private:
  omill::LiftTargetPolicy *getLiftTargetPolicy() {
    if (!lift_target_policy_ ||
        lift_target_policy_memory_map_ != memory_map_ ||
        lift_target_policy_arch_ != target_arch_) {
      lift_target_policy_ =
          omill::createBinaryLiftTargetPolicy(memory_map_, target_arch_);
      lift_target_policy_memory_map_ = memory_map_;
      lift_target_policy_arch_ = target_arch_;
    }
    return lift_target_policy_.get();
  }

  std::map<uint64_t, std::vector<uint8_t>> code_;
  std::map<uint64_t, llvm::WeakTrackingVH> lifted_;
  uint64_t base_addr_ = 0;
  unsigned max_lift_count_ = 0;
  unsigned lift_count_ = 0;
  llvm::Module *module_ = nullptr;
  const remill::Arch *arch_ = nullptr;
  const omill::BinaryMemoryMap *memory_map_ = nullptr;
  omill::TargetArch target_arch_ = omill::TargetArch::kX86_64;
  std::unique_ptr<omill::LiftTargetPolicy> lift_target_policy_;
  const omill::BinaryMemoryMap *lift_target_policy_memory_map_ = nullptr;
  omill::TargetArch lift_target_policy_arch_ = omill::TargetArch::kX86_64;
};

/// In-memory block manager for block-lifting mode.
class BufferBlockManager : public omill::BlockManager {
 public:
  void setModule(llvm::Module *module) { module_ = module; }
  void setBinaryMemoryMap(const omill::BinaryMemoryMap *memory_map) {
    memory_map_ = memory_map;
  }
  void setTargetArch(omill::TargetArch arch) { target_arch_ = arch; }

  void setCode(const uint8_t *data, size_t size, uint64_t base) {
    code_[base] = {data, data + size};
  }

  void SetLiftedBlockDefinition(uint64_t addr,
                                 llvm::Function *fn) override {
    blocks_[addr] = fn;
  }

  llvm::Function *GetLiftedBlockDeclaration(uint64_t addr) override {
    auto it = blocks_.find(addr);
    return (it != blocks_.end()) ? it->second : nullptr;
  }

  llvm::Function *GetLiftedBlockDefinition(uint64_t addr) override {
    return GetLiftedBlockDeclaration(addr);
  }

  bool TryReadExecutableByte(uint64_t addr, uint8_t *out) override {
    for (auto &[base, data] : code_) {
      if (addr >= base && addr < base + data.size()) {
        *out = data[addr - base];
        return true;
      }
    }
    return false;
  }

  omill::LiftTargetDecision ResolveLiftTarget(
      uint64_t source_pc, uint64_t raw_target_pc,
      omill::LiftTargetEdgeKind edge_kind) override {
    return getLiftTargetPolicy()->ResolveLiftTarget(source_pc, raw_target_pc,
                                                    edge_kind);
  }

  omill::DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_addr, uint64_t failed_pc,
      const omill::DecodeFailureContext &ctx) override {
    llvm::SmallVector<uint64_t, 16> known_entries;
    known_entries.reserve(blocks_.size());
    for (const auto &[candidate_pc, candidate_fn] : blocks_) {
      (void)candidate_fn;
      known_entries.push_back(candidate_pc);
    }
    return getLiftTargetPolicy()->ResolveDecodeFailure(source_addr, failed_pc,
                                                       known_entries, ctx);
  }

  llvm::Module *GetLiftedBlockModule() override { return module_; }

private:
  omill::LiftTargetPolicy *getLiftTargetPolicy() {
    if (!lift_target_policy_ ||
        lift_target_policy_memory_map_ != memory_map_ ||
        lift_target_policy_arch_ != target_arch_) {
      lift_target_policy_ =
          omill::createBinaryLiftTargetPolicy(memory_map_, target_arch_);
      lift_target_policy_memory_map_ = memory_map_;
      lift_target_policy_arch_ = target_arch_;
    }
    return lift_target_policy_.get();
  }

  std::map<uint64_t, std::vector<uint8_t>> code_;
  std::map<uint64_t, llvm::Function *> blocks_;
  llvm::Module *module_ = nullptr;
  const omill::BinaryMemoryMap *memory_map_ = nullptr;
  omill::TargetArch target_arch_ = omill::TargetArch::kX86_64;
  std::unique_ptr<omill::LiftTargetPolicy> lift_target_policy_;
  const omill::BinaryMemoryMap *lift_target_policy_memory_map_ = nullptr;
  omill::TargetArch lift_target_policy_arch_ = omill::TargetArch::kX86_64;
};

struct SectionInfo {
  uint64_t va;
  size_t size;
  size_t storage_index;  // index into section_storage
  std::string segment_name;
  std::string section_name;
};

struct PEInfo {
  std::deque<std::vector<uint8_t>> section_storage;
  omill::BinaryMemoryMap memory_map;
  omill::ExceptionInfo exception_info;
  std::vector<SectionInfo> code_sections;
  std::vector<uint64_t> discovered_function_starts;
  std::vector<uint64_t> exported_function_starts;
  std::deque<std::vector<uint8_t>> synthetic_dc_storage;
  uint64_t image_base = 0;
  bool is_macho = false;
};

static bool sectionContainsVA(const SectionInfo &section, uint64_t va) {
  return va >= section.va && va < (section.va + section.size);
}

static bool matchesSectionName(const SectionInfo &section,
                               llvm::StringRef requested_name) {
  if (requested_name == section.section_name)
    return true;
  if (!section.segment_name.empty() &&
      requested_name ==
          (Twine(section.segment_name) + "," + section.section_name).str()) {
    return true;
  }
  return false;
}

static const SectionInfo *findCodeSection(const PEInfo &pe, uint64_t va) {
  for (const auto &section : pe.code_sections) {
    if (sectionContainsVA(section, va))
      return &section;
  }
  return nullptr;
}

static const SectionInfo *findCodeSectionByName(const PEInfo &pe,
                                                llvm::StringRef name) {
  for (const auto &section : pe.code_sections) {
    if (matchesSectionName(section, name))
      return &section;
  }
  return nullptr;
}

static std::vector<uint64_t> collectBatchFunctionStarts(const PEInfo &pe) {
  std::vector<uint64_t> starts;
  if (pe.is_macho) {
    starts = pe.discovered_function_starts;
  } else {
    starts.reserve(pe.exception_info.entries().size());
    for (const auto &entry : pe.exception_info.entries())
      starts.push_back(entry.begin_va);
  }

  llvm::sort(starts);
  starts.erase(std::unique(starts.begin(), starts.end()), starts.end());
  return starts;
}

/// Parse .pdata (exception table) from a PE binary.
/// Populates exception_info with RUNTIME_FUNCTION entries that have
/// language-specific exception handlers.
void parsePData(const object::COFFObjectFile &coff, uint64_t image_base,
                omill::ExceptionInfo &exception_info) {
  const object::data_directory *dd = coff.getDataDirectory(COFF::EXCEPTION_TABLE);
  if (!dd || dd->RelativeVirtualAddress == 0 || dd->Size == 0)
    return;

  uintptr_t table_ptr = 0;
  if (auto err = coff.getRvaPtr(dd->RelativeVirtualAddress, table_ptr)) {
    consumeError(std::move(err));
    return;
  }

  unsigned num_entries = dd->Size / sizeof(Win64EH::RuntimeFunction);
  auto *entries = reinterpret_cast<const Win64EH::RuntimeFunction *>(table_ptr);

  for (unsigned i = 0; i < num_entries; ++i) {
    uint32_t begin_rva = entries[i].StartAddress;
    uint32_t end_rva = entries[i].EndAddress;
    uint32_t unwind_rva = entries[i].UnwindInfoOffset;

    if (begin_rva == 0 && end_rva == 0)
      continue;

    // Follow unwind info chain to find the exception handler.
    uint64_t handler_va = 0;
    uint64_t handler_data_va = 0;
    uint32_t current_unwind_rva = unwind_rva;

    for (unsigned depth = 0; depth < 16; ++depth) {
      uintptr_t unwind_ptr = 0;
      if (auto err = coff.getRvaPtr(current_unwind_rva, unwind_ptr)) {
        consumeError(std::move(err));
        break;
      }

      auto *uwi =
          reinterpret_cast<const Win64EH::UnwindInfo *>(unwind_ptr);
      uint8_t flags = uwi->getFlags();

      if (flags & Win64EH::UNW_ExceptionHandler) {
        uint32_t handler_rva = uwi->getLanguageSpecificHandlerOffset();
        handler_va = image_base + handler_rva;

        // HandlerData follows the handler RVA in the language-specific data.
        auto *lsd = reinterpret_cast<const support::ulittle32_t *>(
            uwi->getLanguageSpecificData());
        // lsd[0] = handler RVA, lsd[1] = handler data RVA
        uint32_t data_rva = lsd[1];
        if (data_rva != 0)
          handler_data_va = image_base + data_rva;
        break;
      }

      if (flags & Win64EH::UNW_ChainInfo) {
        // Follow chain to next RUNTIME_FUNCTION.
        auto *chained = uwi->getChainedFunctionEntry();
        current_unwind_rva = chained->UnwindInfoOffset;
        continue;
      }

      // No handler, no chain — done.
      break;
    }

    exception_info.addEntry({image_base + begin_rva, image_base + end_rva,
                             handler_va, handler_data_va, 0, 0});
  }
}

bool loadPE(StringRef path, PEInfo &out) {
  out.is_macho = false;
  auto buf_or_err = MemoryBuffer::getFile(path);
  if (!buf_or_err) {
    errs() << "Cannot open " << path << ": "
           << buf_or_err.getError().message() << "\n";
    return false;
  }

  auto obj_or_err = object::COFFObjectFile::create(
      (*buf_or_err)->getMemBufferRef());
  if (!obj_or_err) {
    errs() << "Not a valid COFF/PE: "
           << toString(obj_or_err.takeError()) << "\n";
    return false;
  }
  auto &coff = **obj_or_err;
  out.image_base = coff.getImageBase();

  // Parse IAT: map each import's IAT slot VA to its module+function name.
  for (const auto &dir : coff.import_directories()) {
    StringRef dll_name;
    if (dir.getName(dll_name))
      continue;

    // Get IAT RVA from the raw import directory entry.
    const object::coff_import_directory_table_entry *raw_entry = nullptr;
    if (dir.getImportTableEntry(raw_entry) || !raw_entry)
      continue;
    uint32_t iat_rva = raw_entry->ImportAddressTableRVA;

    unsigned idx = 0;
    for (auto sym : dir.imported_symbols()) {
      StringRef sym_name;
      if (!sym.getSymbolName(sym_name)) {
        uint64_t iat_va = out.image_base + iat_rva + idx * 8;
        out.memory_map.addImport(iat_va, dll_name.str(), sym_name.str());
      }
      ++idx;
    }
  }

  for (const auto &exp : coff.export_directories()) {
    bool is_forwarder = false;
    if (auto err = exp.isForwarder(is_forwarder)) {
      consumeError(std::move(err));
      continue;
    }
    if (is_forwarder)
      continue;

    uint32_t export_rva = 0;
    if (auto err = exp.getExportRVA(export_rva)) {
      consumeError(std::move(err));
      continue;
    }
    if (!export_rva)
      continue;

    out.exported_function_starts.push_back(out.image_base + export_rva);
  }
  llvm::sort(out.exported_function_starts);
  out.exported_function_starts.erase(
      std::unique(out.exported_function_starts.begin(),
                  out.exported_function_starts.end()),
      out.exported_function_starts.end());

  // Determine image size from PE optional header.
  uint64_t image_size = 0;
  if (auto *pe32p = coff.getPE32PlusHeader())
    image_size = pe32p->SizeOfImage;
  else if (auto *pe32 = coff.getPE32Header())
    image_size = pe32->SizeOfImage;
  out.memory_map.setImageBase(out.image_base);
  out.memory_map.setImageSize(image_size);

  // Check for suspicious preferred base (anti-analysis defense).
  if (out.memory_map.isSuspiciousImageBase()) {
    errs() << "WARNING: suspicious preferred image base 0x"
           << Twine::utohexstr(out.image_base)
           << " — ASLR will likely produce a non-zero delta.\n"
           << "         Relocated constants in the binary may be unreliable.\n";
  }

  // Parse .reloc (base relocations) for relocation-aware constant folding.
  for (const auto &reloc : coff.base_relocs()) {
    uint8_t type = 0;
    uint32_t rva = 0;
    if (auto err = reloc.getType(type)) {
      consumeError(std::move(err));
      continue;
    }
    if (auto err = reloc.getRVA(rva)) {
      consumeError(std::move(err));
      continue;
    }

    uint8_t reloc_size = 0;
    if (type == COFF::IMAGE_REL_BASED_DIR64)
      reloc_size = 8;
    else if (type == COFF::IMAGE_REL_BASED_HIGHLOW)
      reloc_size = 4;
    else
      continue;  // Skip padding (ABSOLUTE) and exotic types.

    out.memory_map.addRelocation(out.image_base + rva, reloc_size);
  }
  out.memory_map.finalizeRelocations();

  for (const auto &sec : coff.sections()) {
    auto contents_or_err = sec.getContents();
    if (!contents_or_err) { consumeError(contents_or_err.takeError()); continue; }
    StringRef contents = *contents_or_err;

    uint64_t va = sec.getAddress();
    size_t idx = out.section_storage.size();
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();
    const auto *coff_sec = coff.getCOFFSection(sec);
    bool read_only = true;
    if (coff_sec && (coff_sec->Characteristics & COFF::IMAGE_SCN_MEM_WRITE))
      read_only = false;
    bool executable = coff_sec &&
                      (coff_sec->Characteristics &
                       (COFF::IMAGE_SCN_CNT_CODE |
                        COFF::IMAGE_SCN_MEM_EXECUTE));
    out.memory_map.addRegion(va, stored.data(), stored.size(), read_only,
                             executable);

    // Track all executable sections for the trace manager.
    Expected<StringRef> name_or = sec.getName();
    std::string section_name;
    if (name_or)
      section_name = name_or->str();
    else
      consumeError(name_or.takeError());
    if (coff_sec && (coff_sec->Characteristics &
                     (COFF::IMAGE_SCN_CNT_CODE | COFF::IMAGE_SCN_MEM_EXECUTE))) {
      out.code_sections.push_back({va, stored.size(), idx, "", section_name});
    }
  }

  // Parse .pdata unconditionally (cheap); the flag controls usage.
  parsePData(coff, out.image_base, out.exception_info);
  out.exception_info.setImageBase(out.image_base);

  // Create synthetic DISPATCHER_CONTEXT regions in BinaryMemoryMap.
  // Each exception entry with HandlerData gets a synthetic DC at a unique
  // address so ConstantMemoryFolding can resolve [R9+0x38] → HandlerData.
  out.exception_info.buildSyntheticDCs(out.synthetic_dc_storage, out.memory_map,
                                        out.image_base);

  return true;
}

static void collectMachOFunctionStarts(object::MachOObjectFile &macho,
                                       PEInfo &out) {
  for (uint64_t start : macho.getFunctionStarts()) {
    if (findCodeSection(out, start))
      out.discovered_function_starts.push_back(start);
  }

  for (const auto &sym : macho.symbols()) {
    auto type_or = sym.getType();
    if (!type_or) {
      consumeError(type_or.takeError());
      continue;
    }
    if (*type_or != object::SymbolRef::ST_Function)
      continue;

    auto flags_or = sym.getFlags();
    if (!flags_or) {
      consumeError(flags_or.takeError());
      continue;
    }
    if (*flags_or & object::BasicSymbolRef::SF_Undefined)
      continue;

    auto addr_or = sym.getAddress();
    if (!addr_or) {
      consumeError(addr_or.takeError());
      continue;
    }
    if (*addr_or == 0)
      continue;
    if (findCodeSection(out, *addr_or))
      out.discovered_function_starts.push_back(*addr_or);
  }

  llvm::sort(out.discovered_function_starts);
  out.discovered_function_starts.erase(
      std::unique(out.discovered_function_starts.begin(),
                  out.discovered_function_starts.end()),
      out.discovered_function_starts.end());
}

/// Helper: parse sections, imports, and relocations from a MachOObjectFile.
static void parseMachOContents(object::MachOObjectFile &macho,
                                PEInfo &out) {
  // Use __TEXT segment vmaddr as image base.
  uint64_t text_vmaddr = 0;
  uint64_t max_addr = 0;
  for (const auto &cmd : macho.load_commands()) {
    if (cmd.C.cmd == MachO::LC_SEGMENT_64) {
      auto seg = macho.getSegment64LoadCommand(cmd);
      StringRef seg_name(seg.segname, strnlen(seg.segname, 16));
      uint64_t end = seg.vmaddr + seg.vmsize;
      if (end > max_addr) max_addr = end;
      if (seg_name == "__TEXT" && text_vmaddr == 0)
        text_vmaddr = seg.vmaddr;
    }
  }
  out.image_base = text_vmaddr;
  out.memory_map.setImageBase(text_vmaddr);
  out.memory_map.setImageSize(
      max_addr > text_vmaddr ? max_addr - text_vmaddr : 0);

  // Parse sections.
  for (const auto &sec : macho.sections()) {
    auto contents_or = sec.getContents();
    if (!contents_or) { consumeError(contents_or.takeError()); continue; }
    StringRef contents = *contents_or;
    uint64_t va = sec.getAddress();
    size_t idx = out.section_storage.size();
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();
    auto name_or = sec.getName();
    std::string section_name;
    if (name_or)
      section_name = name_or->str();
    else
      consumeError(name_or.takeError());
    std::string seg_name =
        macho.getSectionFinalSegmentName(sec.getRawDataRefImpl()).str();
    bool read_only = !llvm::StringRef(seg_name).starts_with("__DATA");
    bool executable = sec.isText() || section_name == "__stubs";
    out.memory_map.addRegion(va, stored.data(), stored.size(), read_only,
                             executable);
    if (executable) {
      out.code_sections.push_back(
          {va, stored.size(), idx, seg_name, section_name});
    }
  }

  collectMachOFunctionStarts(macho, out);

  // Parse imports from bind opcodes.
  // The ordinal maps to a library index via getLibraryShortNameByIndex().
  {
    Error err = Error::success();
    for (const auto &entry : macho.bindTable(err)) {
      uint64_t addr = entry.address();
      StringRef sym = entry.symbolName();
      if (sym.starts_with("_")) sym = sym.drop_front(1);
      StringRef lib_name;
      int ord = entry.ordinal();
      if (ord > 0)
        macho.getLibraryShortNameByIndex(ord - 1, lib_name);
      out.memory_map.addImport(addr, lib_name.str(), sym.str());
    }
    if (err) consumeError(std::move(err));
  }
  {
    Error err = Error::success();
    for (const auto &entry : macho.lazyBindTable(err)) {
      uint64_t addr = entry.address();
      StringRef sym = entry.symbolName();
      if (sym.starts_with("_")) sym = sym.drop_front(1);
      StringRef lib_name;
      int ord = entry.ordinal();
      if (ord > 0)
        macho.getLibraryShortNameByIndex(ord - 1, lib_name);
      out.memory_map.addImport(addr, lib_name.str(), sym.str());
    }
    if (err) consumeError(std::move(err));
  }

  // Parse relocations from rebase opcodes.
  {
    Error err = Error::success();
    for (const auto &entry : macho.rebaseTable(err)) {
      out.memory_map.addRelocation(entry.address(), 8);
    }
    if (err) consumeError(std::move(err));
  }
  out.memory_map.finalizeRelocations();
}

/// Load a Mach-O binary (or extract arm64/x86_64 slice from a fat binary).
/// Populates the PEInfo struct with code sections, imports, and relocations.
/// Returns the detected remill arch name.
bool loadMachO(StringRef path, PEInfo &out,
               remill::ArchName &out_arch, remill::OSName &out_os) {
  out.is_macho = true;
  auto buf_or_err = MemoryBuffer::getFile(path);
  if (!buf_or_err) {
    errs() << "Cannot open " << path << ": "
           << buf_or_err.getError().message() << "\n";
    return false;
  }

  MemoryBufferRef mbr = (*buf_or_err)->getMemBufferRef();
  auto magic = identify_magic(mbr.getBuffer());

  // Handle fat/universal binaries — prefer arm64, fall back to x86_64.
  if (magic == file_magic::macho_universal_binary) {
    auto uni_or = object::MachOUniversalBinary::create(mbr);
    if (!uni_or) {
      errs() << "Invalid fat binary: " << toString(uni_or.takeError()) << "\n";
      return false;
    }
    auto &uni = **uni_or;

    const object::MachOUniversalBinary::ObjectForArch *arm64_slice = nullptr;
    const object::MachOUniversalBinary::ObjectForArch *x64_slice = nullptr;
    for (const auto &obj : uni.objects()) {
      if (obj.getCPUType() == MachO::CPU_TYPE_ARM64)
        arm64_slice = &obj;
      else if (obj.getCPUType() == MachO::CPU_TYPE_X86_64)
        x64_slice = &obj;
    }
    auto *chosen = arm64_slice ? arm64_slice : x64_slice;
    if (!chosen) {
      errs() << "Fat binary has no arm64 or x86_64 slice\n";
      return false;
    }
    auto obj_or = chosen->getAsObjectFile();
    if (!obj_or) {
      errs() << "Cannot extract slice: " << toString(obj_or.takeError()) << "\n";
      return false;
    }
    auto &macho = **obj_or;

    if (chosen == arm64_slice) {
      out_arch = remill::kArchAArch64LittleEndian;
    } else {
      out_arch = remill::kArchAMD64_AVX;
    }
    out_os = remill::kOSmacOS;

    parseMachOContents(macho, out);
    return true;
  }

  // Non-fat Mach-O: use ObjectFile factory for automatic parsing.
  auto obj_or = object::ObjectFile::createMachOObjectFile(mbr);
  if (!obj_or) {
    errs() << "Not a valid Mach-O: " << toString(obj_or.takeError()) << "\n";
    return false;
  }
  auto &macho = *llvm::cast<object::MachOObjectFile>(obj_or->get());

  // Detect architecture from header.
  auto header = macho.getHeader();
  if (header.cputype == MachO::CPU_TYPE_ARM64) {
    out_arch = remill::kArchAArch64LittleEndian;
  } else if (header.cputype == MachO::CPU_TYPE_X86_64) {
    out_arch = remill::kArchAMD64_AVX;
  } else {
    errs() << "Unsupported Mach-O CPU type: " << header.cputype << "\n";
    return false;
  }
  out_os = remill::kOSmacOS;

  parseMachOContents(macho, out);
  return true;
}

struct ScanResult {
  uint64_t va;
  uint32_t size;
  SmallVector<StringRef, 2> tags;
};

/// Scan an executable section, classifying discovered functions by size and
/// simple control-flow heuristics.
std::vector<ScanResult> scanSection(StringRef section_name, const PEInfo &pe) {
  const SectionInfo *section = findCodeSectionByName(pe, section_name);
  if (!section) {
    errs() << "Section '" << section_name << "' not found\n";
    return {};
  }

  const uint8_t *sec_data = pe.section_storage[section->storage_index].data();
  uint64_t sec_va = section->va;
  uint64_t sec_size = section->size;
  uint64_t sec_end = sec_va + sec_size;
  std::vector<ScanResult> results;

  if (pe.is_macho) {
    auto starts = pe.discovered_function_starts;
    llvm::sort(starts);
    for (size_t i = 0; i < starts.size(); ++i) {
      uint64_t start = starts[i];
      if (!sectionContainsVA(*section, start))
        continue;

      uint64_t next_start = sec_end;
      for (size_t j = i + 1; j < starts.size(); ++j) {
        if (sectionContainsVA(*section, starts[j])) {
          next_start = starts[j];
          break;
        }
      }

      if (next_start <= start)
        continue;

      uint32_t func_size = static_cast<uint32_t>(next_start - start);
      ScanResult sr;
      sr.va = start;
      sr.size = func_size;

      if (section->section_name == "__stubs")
        sr.tags.push_back("stub");
      else if (func_size < 64)
        sr.tags.push_back("trivial");
      else if (func_size <= 256)
        sr.tags.push_back("stub");
      else
        sr.tags.push_back("normal");

      if (func_size > 4096)
        sr.tags.push_back("large");

      results.push_back(std::move(sr));
    }
    return results;
  }

  for (const auto &entry : pe.exception_info.entries()) {
    if (entry.begin_va < sec_va || entry.begin_va >= sec_end)
      continue;

    uint32_t func_size = static_cast<uint32_t>(entry.end_va - entry.begin_va);
    ScanResult sr;
    sr.va = entry.begin_va;
    sr.size = func_size;

    // Compute jmp density from raw bytes if we have section data.
    float jmp_density = 0.0f;
    if (sec_data && func_size > 0) {
      uint64_t offset = entry.begin_va - sec_va;
      uint64_t end_offset = std::min(offset + func_size, sec_size);
      unsigned jmp_count = 0;
      for (uint64_t i = offset; i < end_offset; ++i) {
        uint8_t b = sec_data[i];
        if (b == 0xE9 || b == 0xEB)
          ++jmp_count;
      }
      jmp_density = static_cast<float>(jmp_count) / func_size;
    }

    // Classify.
    if (func_size < 64)
      sr.tags.push_back("trivial");
    else if (func_size <= 256)
      sr.tags.push_back("stub");
    else if (func_size > 256 && jmp_density > 0.08f)
      sr.tags.push_back("cff");
    else
      sr.tags.push_back("normal");

    if (func_size > 4096)
      sr.tags.push_back("large");

    results.push_back(std::move(sr));
  }

  return results;
}

/// Write scan results as JSON.
void writeScanJSON(ArrayRef<ScanResult> results, StringRef binary_name,
                   uint64_t image_base, StringRef section_name,
                   raw_ostream &os) {
  json::OStream J(os, /*IndentSize=*/2);
  J.objectBegin();
  J.attributeBegin("binary");
  J.value(binary_name);
  J.attributeEnd();
  J.attributeBegin("image_base");
  J.value(("0x" + Twine::utohexstr(image_base)).str());
  J.attributeEnd();
  J.attributeBegin("section");
  J.value(section_name);
  J.attributeEnd();
  J.attributeBegin("functions");
  J.arrayBegin();
  for (const auto &r : results) {
    J.objectBegin();
    J.attributeBegin("va");
    J.value(("0x" + Twine::utohexstr(r.va)).str());
    J.attributeEnd();
    J.attributeBegin("size");
    J.value(static_cast<int64_t>(r.size));
    J.attributeEnd();
    J.attributeBegin("tags");
    J.arrayBegin();
    for (auto &tag : r.tags)
      J.value(tag);
    J.arrayEnd();
    J.attributeEnd();
    J.objectEnd();
  }
  J.arrayEnd();
  J.attributeEnd();
  J.objectEnd();
  os << "\n";
}

/// Parse a deobf-targets JSON file, returning function VAs.
std::vector<uint64_t> parseDeobfTargets(StringRef path) {
  auto buf = MemoryBuffer::getFile(path);
  if (!buf) {
    errs() << "Cannot open " << path << ": "
           << buf.getError().message() << "\n";
    return {};
  }
  auto parsed = json::parse((*buf)->getBuffer());
  if (!parsed) {
    errs() << "JSON parse error: " << toString(parsed.takeError()) << "\n";
    return {};
  }
  auto *root = parsed->getAsObject();
  if (!root) {
    errs() << "Expected JSON object at root\n";
    return {};
  }
  auto *funcs = root->getArray("functions");
  if (!funcs) {
    errs() << "No 'functions' array in JSON\n";
    return {};
  }
  std::vector<uint64_t> vas;
  for (const auto &item : *funcs) {
    auto *obj = item.getAsObject();
    if (!obj) continue;
    auto va_str = obj->getString("va");
    if (!va_str) continue;
    uint64_t va = 0;
    StringRef sr = *va_str;
    if (sr.starts_with("0x") || sr.starts_with("0X"))
      sr = sr.drop_front(2);
    sr.getAsInteger(16, va);
    if (va != 0)
      vas.push_back(va);
  }
  return vas;
}

/// Parse an external VMTraceRecord JSON file (e.g. from eac_vm_tracer.py)
/// and populate a VMTraceMap.
//
/// Expected JSON schema:
///   {
///     "vmenter_va": "0x...",
///     "vmexit_va":  "0x...",
///     "records": [
///       {
///         "handler_va":       "0x...",
///         "incoming_hash":    "0x...",
///         "outgoing_hash":    "0x...",
///         "exit_target_va":   "0x...",
///         "native_target_va": "0x...",
///         "successors":       ["0x..."],
///         "passed_vmexit":    bool,
///         "is_vmexit":        bool,
///         "is_error":         bool
///       }
///     ]
///   }
std::shared_ptr<omill::VMTraceMap>
parseExternalVMTrace(StringRef path) {
  auto buf = MemoryBuffer::getFile(path);
  if (!buf) {
    errs() << "Cannot open VM trace JSON " << path << ": "
           << buf.getError().message() << "\n";
    return nullptr;
  }
  auto parsed = json::parse((*buf)->getBuffer());
  if (!parsed) {
    errs() << "VM trace JSON parse error: "
           << toString(parsed.takeError()) << "\n";
    return nullptr;
  }
  auto *root = parsed->getAsObject();
  if (!root) {
    errs() << "Expected JSON object at root of VM trace\n";
    return nullptr;
  }

  auto parseHex = [](std::optional<StringRef> s) -> uint64_t {
    if (!s) return 0;
    StringRef sr = *s;
    if (sr.starts_with("0x") || sr.starts_with("0X"))
      sr = sr.drop_front(2);
    uint64_t val = 0;
    sr.getAsInteger(16, val);
    return val;
  };

  uint64_t vmenter = parseHex(root->getString("vmenter_va"));
  uint64_t vmexit  = parseHex(root->getString("vmexit_va"));
  auto graph = std::make_shared<omill::VMTraceMap>(vmenter, vmexit);

  auto *records = root->getArray("records");
  if (!records) {
    errs() << "No 'records' array in VM trace JSON\n";
    return nullptr;
  }

  unsigned imported = 0;
  for (const auto &item : *records) {
    auto *obj = item.getAsObject();
    if (!obj) continue;

    omill::VMTraceRecord rec;
    rec.handler_va       = parseHex(obj->getString("handler_va"));
    rec.incoming_hash    = parseHex(obj->getString("incoming_hash"));
    rec.outgoing_hash    = parseHex(obj->getString("outgoing_hash"));
    rec.exit_target_va   = parseHex(obj->getString("exit_target_va"));
    rec.native_target_va = parseHex(obj->getString("native_target_va"));
    rec.passed_vmexit    = obj->getBoolean("passed_vmexit").value_or(false);
    rec.is_vmexit        = obj->getBoolean("is_vmexit").value_or(false);
    rec.is_error         = obj->getBoolean("is_error").value_or(false);

    if (auto *succs = obj->getArray("successors")) {
      for (const auto &sv : *succs) {
        if (auto ss = sv.getAsString()) {
          uint64_t succ = 0;
          StringRef sr = *ss;
          if (sr.starts_with("0x") || sr.starts_with("0X"))
            sr = sr.drop_front(2);
          sr.getAsInteger(16, succ);
          if (succ) rec.successors.push_back(succ);
        }
      }
    }

    if (rec.handler_va == 0) continue;
    graph->recordTrace(std::move(rec));
    ++imported;
  }

  errs() << "VMTraceMap: imported " << imported << " records from "
         << path << " (vmenter=0x" << utohexstr(vmenter)
         << " vmexit=0x" << utohexstr(vmexit) << ")\n";
  return graph;
}

}  // namespace

int main(int argc, char **argv) {
  omill::setProcessMemoryLimit(32ULL * 1024 * 1024 * 1024);  // 32 GB
  InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv,
      "omill-lift: Lift a function from a PE/Mach-O binary and optimize\n");
  configureDriverLogging(argv[0]);

  LiftEventLogger events;
  if (!events.init(EventJSONL, EventDetail, InputFilename))
    return 1;
  events.emitInfo("run_started", "omill-lift started",
                  {{"input", InputFilename}});

  auto fail = [&](int code, StringRef reason) -> int {
    events.emitError("run_error", reason);
    events.emitTerminalFailure(code, reason);
    return code;
  };

  // Check for batch/scan modes that don't require --va.
  bool batch_mode = (ScanSection.getNumOccurrences() > 0 ||
                     DeobfTargets.getNumOccurrences() > 0 ||
                     DeobfSection.getNumOccurrences() > 0 ||
                     AllFunctions);

  // Parse VA — for raw binaries, default to base address if --va not given.
  uint64_t func_va = 0;
  if (FuncVA.getNumOccurrences() > 0) {
    if (StringRef(FuncVA).starts_with("0x") ||
        StringRef(FuncVA).starts_with("0X")) {
      StringRef(FuncVA).drop_front(2).getAsInteger(16, func_va);
    } else {
      StringRef(FuncVA).getAsInteger(16, func_va);
    }
  } else if (RawBinary) {
    func_va = BaseAddress;
  } else if (!batch_mode) {
    errs() << "--va is required for single-function lifting\n";
    return fail(1, "--va is required for single-function lifting");
  }
  if (func_va == 0 && !RawBinary && !batch_mode) {
    errs() << "Invalid VA: " << FuncVA << "\n";
    return fail(1, "invalid --va value");
  }
  const uint64_t requested_func_va = func_va;
  if (func_va != 0)
    errs() << "Lifting function at VA 0x" << Twine::utohexstr(func_va) << "\n";

  // Parse VM entry/exit VAs if provided.
  uint64_t vm_entry_va = 0, vm_exit_va = 0;
  auto parseHexOpt = [](const std::string &s) -> uint64_t {
    uint64_t v = 0;
    StringRef sr(s);
    if (sr.starts_with("0x") || sr.starts_with("0X"))
      sr.drop_front(2).getAsInteger(16, v);
    else
      sr.getAsInteger(16, v);
    return v;
  };
  if (VMEntry.getNumOccurrences() > 0)
    vm_entry_va = parseHexOpt(VMEntry);
  if (VMExit.getNumOccurrences() > 0)
    vm_exit_va = parseHexOpt(VMExit);

  uint64_t vm_wrapper_va = 0;
  if (VMWrapper.getNumOccurrences() > 0)
    vm_wrapper_va = parseHexOpt(VMWrapper);

  bool vm_mode = (vm_entry_va != 0);
  const bool has_external_vm_trace = VMTraceJSON.getNumOccurrences() > 0;
  const bool force_devirtualize = Devirtualize;
  bool use_block_lift_mode =
      BlockLift || force_devirtualize || GenericStaticDevirtualize ||
      parseBoolEnv("OMILL_GENERIC_STATIC_DEVIRT").value_or(false);
  if (vm_mode) {
    // Default wrapper to func_va if not explicitly specified.
    if (vm_wrapper_va == 0)
      vm_wrapper_va = func_va;
    errs() << "VM mode: vmenter=0x" << Twine::utohexstr(vm_entry_va)
           << " vmexit=0x" << Twine::utohexstr(vm_exit_va);
    if (vm_wrapper_va != func_va)
      errs() << " wrapper=0x" << Twine::utohexstr(vm_wrapper_va);
    errs() << "\n";
    events.emitInfo("vm_mode",
                    "vm devirtualization mode enabled",
                    {{"vm_entry", ("0x" + Twine::utohexstr(vm_entry_va)).str()},
                     {"vm_exit", ("0x" + Twine::utohexstr(vm_exit_va)).str()}});
  }
  if (force_devirtualize) {
    events.emitInfo("devirtualization_requested",
                    "library-owned devirtualization requested",
                    {{"forced", true},
                     {"compat_block_lift", static_cast<bool>(BlockLift)},
                     {"compat_generic_static",
                      static_cast<bool>(GenericStaticDevirtualize)}});
  }

  // --- Binary loading with format auto-detection ---
  PEInfo pe;
  std::vector<uint8_t> raw_code;
  remill::ArchName detected_arch = remill::kArchAMD64_AVX;
  remill::OSName detected_os = remill::kOSWindows;
  omill::TargetArch target_arch = omill::TargetArch::kX86_64;
  std::string target_os_str = "windows";
  events.emitInfo("input_load_started", "loading input");

  if (RawBinary) {
    auto buf_or_err = MemoryBuffer::getFile(InputFilename);
    if (!buf_or_err) {
      errs() << "Cannot open " << InputFilename << ": "
             << buf_or_err.getError().message() << "\n";
      return fail(1, "cannot open raw input file");
    }
    auto &buf = *buf_or_err;
    raw_code.assign(
        reinterpret_cast<const uint8_t *>(buf->getBufferStart()),
        reinterpret_cast<const uint8_t *>(buf->getBufferEnd()));
    errs() << "Loaded raw binary: " << raw_code.size()
           << " bytes at base 0x" << Twine::utohexstr(BaseAddress) << "\n";
    detected_os = remill::kOSLinux;
    target_os_str = "linux";
    events.emitInfo("input_load_completed", "raw input loaded",
                    {{"mode", "raw"},
                     {"bytes", static_cast<int64_t>(raw_code.size())},
                     {"base", ("0x" + Twine::utohexstr(BaseAddress)).str()}});
  } else {
    // Auto-detect binary format by peeking at the magic bytes.
    bool is_macho = false;
    {
      auto probe_buf = MemoryBuffer::getFile(InputFilename);
      if (!probe_buf) {
        errs() << "Cannot open " << InputFilename << "\n";
        return fail(1, "cannot open input file");
      }
      auto magic = identify_magic((*probe_buf)->getBuffer());
      is_macho = (magic == file_magic::macho_object ||
                  magic == file_magic::macho_executable ||
                  magic == file_magic::macho_dynamically_linked_shared_lib ||
                  magic == file_magic::macho_bundle ||
                  magic == file_magic::macho_universal_binary);
    }

    if (is_macho) {
      if (!loadMachO(InputFilename, pe, detected_arch, detected_os))
        return fail(1, "failed to load Mach-O input");
      if (detected_arch == remill::kArchAArch64LittleEndian) {
        target_arch = omill::TargetArch::kAArch64;
        target_os_str = "darwin";
      } else {
        target_arch = omill::TargetArch::kX86_64;
        target_os_str = "darwin";
      }
      errs() << "Loaded Mach-O: image_base=0x"
             << Twine::utohexstr(pe.image_base)
             << " code_sections=" << pe.code_sections.size()
             << " arch=" << (target_arch == omill::TargetArch::kAArch64
                                 ? "aarch64" : "x86_64") << "\n";
    } else {
      // Default: PE/COFF
      if (!loadPE(InputFilename, pe))
        return fail(1, "failed to load PE input");
      errs() << "Loaded PE: image_base=0x" << Twine::utohexstr(pe.image_base)
             << " code_sections=" << pe.code_sections.size() << "\n";
    }
    for (const auto &cs : pe.code_sections) {
      errs() << "  code: 0x" << Twine::utohexstr(cs.va)
             << " (" << cs.size << " bytes)\n";
    }
    if (pe.code_sections.empty()) {
      errs() << "No executable sections found in input binary\n";
      return fail(1, "no executable sections found");
    }
    events.emitInfo("input_load_completed",
                    pe.is_macho ? "Mach-O input loaded" : "PE input loaded",
                    {{"mode", pe.is_macho ? "macho" : "pe"},
                     {"image_base", ("0x" + Twine::utohexstr(pe.image_base)).str()},
                     {"code_sections", static_cast<int64_t>(pe.code_sections.size())}});

    auto resolveDirectJmpThunkTarget = [&](uint64_t root_va)
        -> std::optional<uint64_t> {
      const auto *section = findCodeSection(pe, root_va);
      if (!section || section->storage_index >= pe.section_storage.size())
        return std::nullopt;
      const auto &stored = pe.section_storage[section->storage_index];
      const size_t offset = static_cast<size_t>(root_va - section->va);
      if (offset >= stored.size())
        return std::nullopt;
      const size_t remaining = stored.size() - offset;
      if (remaining >= 5u && stored[offset] == 0xE9u) {
        int32_t rel = 0;
        std::memcpy(&rel, stored.data() + offset + 1u, sizeof(rel));
        const uint64_t target_va = root_va + 5u + static_cast<int64_t>(rel);
        if (findCodeSection(pe, target_va))
          return target_va;
      }
      if (remaining >= 2u && stored[offset] == 0xEBu) {
        int8_t rel = static_cast<int8_t>(stored[offset + 1u]);
        const uint64_t target_va = root_va + 2u + rel;
        if (findCodeSection(pe, target_va))
          return target_va;
      }
      return std::nullopt;
    };

    if (!batch_mode && !vm_mode && func_va != 0 &&
        std::find(pe.exported_function_starts.begin(),
                  pe.exported_function_starts.end(),
                  requested_func_va) != pe.exported_function_starts.end()) {
      if (auto thunk_target = resolveDirectJmpThunkTarget(requested_func_va)) {
        if (*thunk_target != requested_func_va) {
          errs() << "Export thunk root normalized: 0x"
                 << Twine::utohexstr(requested_func_va) << " -> 0x"
                 << Twine::utohexstr(*thunk_target) << "\n";
          func_va = *thunk_target;
        }
      }
    }

    // --scan-section: classify functions and output JSON, then exit.
    if (ScanSection.getNumOccurrences() > 0) {
      events.emitInfo("scan_started", "scan-section started",
                      {{"section", ScanSection}});
      auto results = scanSection(ScanSection, pe);
      // Filter by minimum size unless --scan-all.
      if (!ScanAll) {
        results.erase(
            std::remove_if(results.begin(), results.end(),
                           [](const ScanResult &r) {
                             return r.size < MinFuncSize;
                           }),
            results.end());
      }
      errs() << "Scanned " << results.size() << " functions in '"
             << ScanSection << "'\n";

      if (ScanOutput == "-") {
        writeScanJSON(results, InputFilename, pe.image_base, ScanSection,
                      outs());
      } else {
        std::error_code ec;
        raw_fd_ostream out(ScanOutput, ec, sys::fs::OF_Text);
        if (ec) {
          errs() << "Error opening " << ScanOutput << ": "
                 << ec.message() << "\n";
          return fail(1, "scan-output open failed");
        }
        writeScanJSON(results, InputFilename, pe.image_base, ScanSection, out);
      }
      events.emitInfo("scan_completed", "scan-section completed",
                      {{"section", ScanSection},
                       {"function_count", static_cast<int64_t>(results.size())}});
      events.emitTerminalSuccess(ScanOutput == "-"
                                     ? StringRef("<stdout>")
                                     : StringRef(ScanOutput));
      return 0;
    }
  }

  // Collect batch VAs from --deobf-targets, --deobf-section, or
  // --all-functions.
  std::vector<uint64_t> batch_vas;
  if (DeobfTargets.getNumOccurrences() > 0) {
    batch_vas = parseDeobfTargets(DeobfTargets);
    if (batch_vas.empty()) {
      errs() << "No valid VAs in " << DeobfTargets << "\n";
      return fail(1, "no valid VAs in --deobf-targets");
    }
    errs() << "Batch mode: " << batch_vas.size()
           << " targets from " << DeobfTargets << "\n";
  } else if (DeobfSection.getNumOccurrences() > 0) {
    events.emitInfo("batch_discovery_started",
                    "discovering targets from section",
                    {{"section", DeobfSection}});
    auto results = scanSection(DeobfSection, pe);
    for (const auto &r : results) {
      if (r.size >= MinFuncSize)
        batch_vas.push_back(r.va);
    }
    if (batch_vas.empty()) {
      errs() << "No functions >= " << MinFuncSize
             << "B in section '" << DeobfSection << "'\n";
      return fail(1, "no qualifying functions found in --deobf-section");
    }
    errs() << "Section mode: " << batch_vas.size()
           << " functions from '" << DeobfSection << "' (>= "
           << MinFuncSize << "B)\n";
    // Force deobfuscation on for --deobf-section.
    Deobfuscate = true;
  } else if (AllFunctions) {
    if (RawBinary) {
      errs() << "--all-functions is not supported for raw binaries\n";
      return fail(1, "--all-functions is not supported for raw binaries");
    }
    batch_vas = collectBatchFunctionStarts(pe);
    if (batch_vas.empty()) {
      errs() << "No discovered functions in executable sections\n";
      return fail(1, "no discovered functions found");
    }
    errs() << "All-functions mode: " << batch_vas.size()
           << " discovered functions\n";
    events.emitInfo("batch_discovery_started",
                    "discovering all executable functions",
                    {{"count", static_cast<int64_t>(batch_vas.size())}});
  }
  if (!batch_vas.empty()) {
    events.emitInfo("batch_targets_ready", "batch target set created",
                    {{"count", static_cast<int64_t>(batch_vas.size())}});
  }

  // Set up remill with the detected architecture.
  LLVMContext ctx;
  auto arch = remill::Arch::Get(ctx, detected_os, detected_arch);
  if (!arch) {
    errs() << "Failed to create arch (arch="
           << static_cast<int>(detected_arch)
           << " os=" << static_cast<int>(detected_os) << ")\n";
    return fail(1, "failed to create arch");
  }

  auto module = remill::LoadArchSemantics(arch.get());
  if (!module) {
    errs() << "Failed to load arch semantics\n";
    return fail(1, "failed to load arch semantics");
  }

  // Load code into the trace manager.
  BufferTraceManager manager;
  manager.setModuleAndArch(module.get(), arch.get());
  if (!RawBinary)
    manager.setBinaryMemoryMap(&pe.memory_map);
  manager.setTargetArch(target_arch);
  if (RawBinary) {
    manager.setCode(raw_code.data(), raw_code.size(), BaseAddress);
  } else {
    for (const auto &cs : pe.code_sections) {
      auto &stored = pe.section_storage[cs.storage_index];
      manager.setCode(stored.data(), stored.size(), cs.va);
    }
  }
  if (!batch_vas.empty())
    manager.setBaseAddr(batch_vas.front());
  else if (func_va != 0)
    manager.setBaseAddr(func_va);

  if (!RawBinary && ResolveExceptions && !pe.exception_info.empty()) {
    errs() << "Parsed .pdata: " << pe.exception_info.getHandlerVAs().size()
           << " unique handler(s)\n";
  }

  // Lift
  omill::TraceLifter lifter(arch.get(), manager);
  auto iterative_session =
      std::make_shared<omill::IterativeLiftingSession>("omill-lift");
  iterative_session->setBlockLiftingEnabled(use_block_lift_mode);

  std::unique_ptr<BufferBlockManager> block_manager;
  std::unique_ptr<omill::BlockLifter> block_lifter;
  if (!vm_mode) {
    block_manager = std::make_unique<BufferBlockManager>();
    block_manager->setModule(module.get());
    if (!RawBinary)
      block_manager->setBinaryMemoryMap(&pe.memory_map);
    block_manager->setTargetArch(target_arch);
    if (RawBinary) {
      block_manager->setCode(raw_code.data(), raw_code.size(), BaseAddress);
    } else {
      for (auto &sec : pe.code_sections) {
        auto &data = pe.section_storage[sec.storage_index];
        block_manager->setCode(data.data(), data.size(), sec.va);
      }
    }
    block_lifter =
        std::make_unique<omill::BlockLifter>(arch.get(), *block_manager);
  }

  if (!batch_vas.empty()) {
    for (uint64_t va : batch_vas)
      iterative_session->queueTarget(va);
  } else if (func_va != 0) {
    iterative_session->queueTarget(func_va);
  }
  events.emitInfo("lifting_started", "lifting started");

  auto tagOutputRoot = [&](uint64_t va) {
    std::string base = "sub_" + llvm::Twine::utohexstr(va).str();
    if (auto *fn = module->getFunction(base)) {
      if (!fn->isDeclaration())
        fn->addFnAttr("omill.output_root");
      return;
    }
    for (int i = 1; i <= 20; ++i) {
      if (auto *fn = module->getFunction((base + "." + std::to_string(i)).c_str())) {
        if (!fn->isDeclaration()) {
          fn->addFnAttr("omill.output_root");
          return;
        }
      }
    }
    std::string block_name = "blk_" + llvm::Twine::utohexstr(va).str();
    if (auto *fn = module->getFunction(block_name)) {
      if (!fn->isDeclaration())
        fn->addFnAttr("omill.output_root");
    }
  };

  // Wrapper VAs detected during auto-detection (thunk_va, wrapper_va).
  std::vector<std::pair<uint64_t, uint64_t>> auto_detected_wrappers;

  if (!batch_vas.empty()) {
    // Batch lifting mode.
    unsigned lifted = 0, failed = 0;
    for (uint64_t va : batch_vas) {
      if (events.detailed()) {
        events.emitInfo("lift_target_started", "lifting target",
                        {{"va", ("0x" + Twine::utohexstr(va)).str()}});
      }
      bool ok = false;
      if (use_block_lift_mode && !vm_mode && block_lifter) {
        ok = block_lifter->LiftReachable(va) > 0;
      } else {
        ok = lifter.Lift(va);
      }
      if (ok) {
        iterative_session->noteLiftedTarget(va);
        ++lifted;
      } else {
        ++failed;
      }
    }
    errs() << "Batch lift: " << lifted << " succeeded, "
           << failed << " failed\n";
    events.emitInfo("lifting_batch_completed", "batch lift finished",
                    {{"lifted", static_cast<int64_t>(lifted)},
                     {"failed", static_cast<int64_t>(failed)}});
    if (lifted == 0) {
      errs() << "No functions lifted\n";
      return fail(1, "no functions lifted");
    }
    for (uint64_t va : batch_vas)
      tagOutputRoot(va);
  } else {
    // Single-function lifting mode.
    if (use_block_lift_mode && !vm_mode && block_lifter) {
      if (block_lifter->LiftReachable(func_va) == 0) {
        errs() << "BlockLifter::LiftReachable() failed\n";
        return fail(1, "block lifter failed");
      }
      iterative_session->noteLiftedTarget(func_va);
      tagOutputRoot(func_va);
      errs() << "Block-lifting initial reachable blocks complete\n";
    } else {
    // If available, lift the handler first so Remill reuses a canonical
    // sub_<va> function instead of creating a late duplicate (sub_<va>.1).
    uint64_t auto_handler_va = 0;
    if (!RawBinary && ResolveExceptions) {
      if (auto *entry = pe.exception_info.lookup(func_va)) {
        auto_handler_va = entry->handler_va;
      }
    }
    if (auto_handler_va != 0 && auto_handler_va != func_va) {
      errs() << "Auto-lifting exception handler at 0x"
             << Twine::utohexstr(auto_handler_va) << "\n";
      if (events.detailed()) {
        events.emitInfo("lift_handler_started", "auto-lifting exception handler",
                        {{"va", ("0x" + Twine::utohexstr(auto_handler_va)).str()}});
      }
      if (!lifter.Lift(auto_handler_va)) {
        errs() << "WARNING: failed to lift handler at 0x"
               << Twine::utohexstr(auto_handler_va) << "\n";
        events.emitWarn("lift_handler_failed", "failed to lift exception handler",
                        {{"va", ("0x" + Twine::utohexstr(auto_handler_va)).str()}});
      } else {
        iterative_session->noteLiftedTarget(auto_handler_va);
      }
    }

    if (!lifter.Lift(func_va)) {
      errs() << "TraceLifter::Lift() failed\n";
      return fail(1, "trace lifter failed");
    }
    iterative_session->noteLiftedTarget(func_va);
    tagOutputRoot(func_va);
    }

    // Auto-detect VM wrappers when --vm-wrapper is not specified.
    // DriverEntry (or similar outer function) calls thunks (E9 jmp) that
    // resolve to actual VM wrappers.  Collect ALL detected wrappers.
    if (vm_mode && vm_wrapper_va == func_va) {
      auto *entry_fn = module->getFunction(
          "sub_" + llvm::Twine::utohexstr(func_va).str());
      if (entry_fn) {
        for (auto &BB : *entry_fn) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee_fn = call->getCalledFunction();
            if (!callee_fn)
              continue;
            auto callee_name = callee_fn->getName();
            if (!callee_name.starts_with("sub_"))
              continue;
            uint64_t callee_va = 0;
            callee_name.drop_front(4).getAsInteger(16, callee_va);
            if (callee_va == 0)
              continue;

            // Follow jmp-thunks to a real function body.
            uint64_t resolved = callee_va;
            for (int hop = 0; hop < 4; ++hop) {
              uint8_t tbuf[16];
              if (!pe.memory_map.read(resolved, tbuf, sizeof(tbuf)))
                break;
              if (tbuf[0] == 0xE9) {
                int32_t rel;
                std::memcpy(&rel, &tbuf[1], 4);
                resolved = resolved + 5 + static_cast<int64_t>(rel);
              } else if (tbuf[0] == 0xEB) {
                int8_t rel = static_cast<int8_t>(tbuf[1]);
                resolved = resolved + 2 + rel;
              } else {
                break;
              }
            }
            if (resolved == callee_va)
              continue;  // not a thunk

            // Probe the resolved VA for the wrapper pattern:
            //   optional lea rsp,[rsp-N] / sub rsp,N
            //   E8 <rel32>  (call to vmentry or near it)
            uint8_t probe[32];
            if (!pe.memory_map.read(resolved, probe, sizeof(probe)))
              continue;
            unsigned p = 0;
            if (p + 8 <= sizeof(probe) &&
                probe[p] == 0x48 && probe[p+1] == 0x8D &&
                probe[p+2] == 0xA4 && probe[p+3] == 0x24) {
              p += 8;
            } else if (p + 5 <= sizeof(probe) &&
                       probe[p] == 0x48 && probe[p+1] == 0x8D &&
                       probe[p+2] == 0x64 && probe[p+3] == 0x24) {
              p += 5;
            } else if (p + 7 <= sizeof(probe) &&
                       probe[p] == 0x48 && probe[p+1] == 0x81 &&
                       probe[p+2] == 0xEC) {
              p += 7;
            }
            if (p + 5 > sizeof(probe) || probe[p] != 0xE8)
              continue;
            int32_t crel;
            std::memcpy(&crel, &probe[p+1], 4);
            uint64_t ctarget = resolved + p + 5 + static_cast<int64_t>(crel);
            // Accept if the call target is within a reasonable range of vmentry.
            if (ctarget < vm_entry_va - 0x1000 || ctarget > vm_entry_va + 0x1000)
              continue;

            // Avoid duplicates (same wrapper from different thunks).
            bool dup = false;
            for (auto &[tv, wv] : auto_detected_wrappers)
              if (wv == resolved) { dup = true; break; }
            if (dup) continue;

            errs() << "Auto-detected VM wrapper at 0x"
                   << Twine::utohexstr(resolved)
                   << " (via thunk sub_"
                   << Twine::utohexstr(callee_va) << ")\n";
            auto_detected_wrappers.push_back({callee_va, resolved});
          }
        }
      }
      // Use the first detected wrapper as the primary one.
      if (!auto_detected_wrappers.empty())
        vm_wrapper_va = auto_detected_wrappers.front().second;
    }

    // When --vm-wrapper differs from --va, fold jmp-thunks between
    // func_va and the VM wrapper so that the entry function calls the
    // wrapper directly.  Without this, remill's TraceLifter follows the
    // thunk's JMP and duplicates the wrapper's code inside the thunk
    // function, producing an incomplete copy (only the first VM chain)
    // that confuses ABI recovery.
    if (vm_mode && vm_wrapper_va != func_va) {
      // Ensure the wrapper is lifted.
      {
        std::string wrapper_name =
            "sub_" + llvm::Twine::utohexstr(vm_wrapper_va).str();
        auto *wrapper_fn = module->getFunction(wrapper_name);
        if (!wrapper_fn || wrapper_fn->isDeclaration()) {
          errs() << "Auto-lifting VM wrapper at 0x"
                 << Twine::utohexstr(vm_wrapper_va) << "\n";
          lifter.Lift(vm_wrapper_va);
        }
      }

      // Detect jmp-thunks between the entry function and the wrapper by
      // reading binary bytes.  A jmp-thunk is a single E9/EB JMP
      // instruction that transfers to another function.  When the target
      // is the VM wrapper (or chains to it), rewrite the caller to call
      // the wrapper directly.
      //
      // Remill's TraceLifter creates DIRECT calls to lifted functions
      // (e.g. `call @sub_1400d5dc4(...)`) rather than going through
      // `__remill_function_call`.  So we scan for calls to `sub_*`
      // functions and check if the callee's VA is a jmp-thunk.
      auto *entry_fn = module->getFunction(
          "sub_" + llvm::Twine::utohexstr(func_va).str());
      if (entry_fn) {
        for (auto &BB : *entry_fn) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee_fn = call->getCalledFunction();
            if (!callee_fn)
              continue;

            // Parse VA from the callee function name (sub_<hex>).
            auto callee_name = callee_fn->getName();
            if (!callee_name.starts_with("sub_"))
              continue;
            uint64_t callee_va = 0;
            callee_name.drop_front(4).getAsInteger(16, callee_va);
            if (callee_va == 0 || callee_va == vm_wrapper_va)
              continue;

            // Follow up to 3 levels of jmp-thunks to find the wrapper.
            uint64_t resolved = callee_va;
            for (int hop = 0; hop < 3; ++hop) {
              uint8_t thunk_buf[16];
              if (!pe.memory_map.read(resolved, thunk_buf, sizeof(thunk_buf)))
                break;
              // E9 rel32 = near relative jmp (5 bytes)
              if (thunk_buf[0] == 0xE9) {
                int32_t rel;
                std::memcpy(&rel, &thunk_buf[1], 4);
                resolved = resolved + 5 + static_cast<int64_t>(rel);
              }
              // EB rel8 = short relative jmp (2 bytes)
              else if (thunk_buf[0] == 0xEB) {
                int8_t rel = static_cast<int8_t>(thunk_buf[1]);
                resolved = resolved + 2 + rel;
              } else {
                break;
              }
            }

            if (resolved != vm_wrapper_va)
              continue;

            // This callee is a jmp-thunk chain to the VM wrapper.
            // Rewrite the call to target the wrapper directly.
            errs() << "Folding jmp-thunk: sub_"
                   << Twine::utohexstr(callee_va) << " -> sub_"
                   << Twine::utohexstr(vm_wrapper_va) << "\n";

            std::string wrapper_name =
                "sub_" + llvm::Twine::utohexstr(vm_wrapper_va).str();
            auto *wrapper_fn = module->getFunction(wrapper_name);
            if (!wrapper_fn)
              continue;

            // Rewrite: call @sub_<thunk_va>(state, pc, mem)
            //       → call @sub_<wrapper_va>(state, wrapper_va, mem)
            call->setCalledFunction(wrapper_fn);
            // Fix the program_counter argument to the wrapper's address.
            auto *pc_arg = call->getArgOperand(1);
            call->setArgOperand(
                1, llvm::ConstantInt::get(pc_arg->getType(), vm_wrapper_va));

            // Delete the thunk function — it's a duplicated partial
            // copy of the wrapper that would confuse ABI recovery.
            std::string thunk_name =
                "sub_" + llvm::Twine::utohexstr(callee_va).str();
            if (auto *thunk_fn = module->getFunction(thunk_name)) {
              if (!thunk_fn->use_empty()) {
                // Can't delete if it has other uses; just leave it.
                errs() << "  (thunk has other callers, keeping)\n";
              } else {
                thunk_fn->eraseFromParent();
                errs() << "  (deleted thunk sub_"
                       << Twine::utohexstr(callee_va) << ")\n";
              }
            }
          }
        }
      }
    }

    // Process additional auto-detected wrappers (beyond the first one
    // which was handled above as vm_wrapper_va).
    if (vm_mode && auto_detected_wrappers.size() > 1) {
      auto *entry_fn = module->getFunction(
          "sub_" + llvm::Twine::utohexstr(func_va).str());
      for (size_t wi = 1; wi < auto_detected_wrappers.size(); ++wi) {
        uint64_t thunk_va = auto_detected_wrappers[wi].first;
        uint64_t wrapper_va = auto_detected_wrappers[wi].second;

        // Lift the wrapper.
        std::string wrapper_name =
            "sub_" + llvm::Twine::utohexstr(wrapper_va).str();
        auto *wrapper_fn = module->getFunction(wrapper_name);
        if (!wrapper_fn || wrapper_fn->isDeclaration()) {
          errs() << "Auto-lifting VM wrapper at 0x"
                 << Twine::utohexstr(wrapper_va) << "\n";
          lifter.Lift(wrapper_va);
          wrapper_fn = module->getFunction(wrapper_name);
        }
        if (!wrapper_fn)
          continue;

        // Fold the thunk to this wrapper.
        if (entry_fn) {
          std::string thunk_name =
              "sub_" + llvm::Twine::utohexstr(thunk_va).str();
          for (auto &BB : *entry_fn) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->arg_size() < 2)
                continue;
              auto *callee_fn = call->getCalledFunction();
              if (!callee_fn || callee_fn->getName() != thunk_name)
                continue;
              errs() << "Folding jmp-thunk: sub_"
                     << Twine::utohexstr(thunk_va) << " -> sub_"
                     << Twine::utohexstr(wrapper_va) << "\n";
              call->setCalledFunction(wrapper_fn);
              auto *pc_arg = call->getArgOperand(1);
              call->setArgOperand(
                  1, llvm::ConstantInt::get(pc_arg->getType(), wrapper_va));
            }
          }
          // Delete the thunk if unused.
          if (auto *thunk_fn = module->getFunction(thunk_name)) {
            if (thunk_fn->use_empty()) {
              thunk_fn->eraseFromParent();
              errs() << "  (deleted thunk sub_"
                     << Twine::utohexstr(thunk_va) << ")\n";
            }
          }
        }
      }
    }
  }
  for (auto &F : llvm::make_early_inc_range(*module)) {
    if (!F.isDeclaration())
      continue;
    auto fname = F.getName();
    if (!fname.starts_with("sub_"))
      continue;
    size_t dot = fname.rfind('.');
    if (dot == StringRef::npos || dot + 1 >= fname.size())
      continue;
    auto suffix = fname.drop_front(dot + 1);
    unsigned clone_index = 0;
    if (suffix.getAsInteger(10, clone_index))
      continue;
    std::string base_name = fname.take_front(dot).str();
    if (auto *base = module->getFunction(base_name)) {
      if (!base->isDeclaration()) {
        F.replaceAllUsesWith(base);
        F.eraseFromParent();
        errs() << "Folded lifted declaration alias " << fname << " -> "
               << base_name << "\n";
      }
    }
  }
  errs() << "Lifting complete\n";
  events.emitInfo("lifting_completed", "lifting complete");

  // VM mode: use the trace emulator to discover handlers reachable from the
  // entry wrapper, then lift only those. No byte-pattern bulk scan — further
  // targets are discovered naturally by the pipeline's iterative resolution.
  std::shared_ptr<omill::VMTraceMap> vm_graph;
  std::vector<omill::NativeCallInfo> native_call_infos;
  if (vm_mode && !RawBinary) {
    vm_graph = std::make_shared<omill::VMTraceMap>(vm_entry_va, vm_exit_va);

    struct VMTraceLiftKey {
      uint64_t handler_va = 0;
      uint64_t incoming_hash = 0;
    };

    std::vector<VMTraceLiftKey> trace_work_items;
    std::vector<uint64_t> native_call_vas;
    llvm::DenseSet<uint64_t> seen_vm_trace_work;
    llvm::DenseMap<uint64_t, llvm::SmallVector<uint64_t, 2>>
        handler_trace_hashes;
    std::optional<uint64_t> imported_entry_seed_hash;

    // Demerging must preserve distinct incoming hashes for the same handler VA.
    // Deduplicating only on handler_va would collapse merged ops back together
    // before clone generation even begins, so the lift worklist is keyed by
    // (handler_va, incoming_hash).
    auto recordTraceWorkItem = [&](uint64_t handler_va, uint64_t incoming_hash) {
      uint64_t key = incoming_hash ^
                     (handler_va + 0x9E3779B97F4A7C15ull +
                      (incoming_hash << 6) + (incoming_hash >> 2));
      if (seen_vm_trace_work.insert(key).second)
        trace_work_items.push_back({handler_va, incoming_hash});

      auto &hashes = handler_trace_hashes[handler_va];
      if (std::find(hashes.begin(), hashes.end(), incoming_hash) == hashes.end())
        hashes.push_back(incoming_hash);
    };
    auto rememberFlatTrace = [&](const auto &records) {
      for (const auto &record : records)
        recordTraceWorkItem(record.handler_va, record.incoming_hash);
    };

    auto rememberRawTrace = [&](const auto &entries) {
      for (const auto &entry : entries)
        recordTraceWorkItem(entry.handler_va, entry.incoming_hash);
    };

    auto mergeSupplementalWrapperTrace = [&](StringRef primary_trace_path) {
      if (!VMTraceJSON.getNumOccurrences())
        return;

      SmallString<260> supplemental_path(primary_trace_path);
      sys::path::remove_filename(supplemental_path);
      sys::path::append(supplemental_path, "vm_trace_records.json");
      if (supplemental_path == primary_trace_path)
        return;
      if (!sys::fs::exists(supplemental_path))
        return;

      auto supplemental_graph = parseExternalVMTrace(supplemental_path);
      if (!supplemental_graph)
        return;

      unsigned merged_records = 0;
      llvm::DenseSet<uint64_t> merged_wrappers;
      for (uint64_t native_va : native_call_vas) {
        auto records = supplemental_graph->getTraceRecords(native_va);
        if (records.empty())
          continue;
        merged_wrappers.insert(native_va);
        for (const auto &record : records) {
          vm_graph->recordTrace(record);
          recordTraceWorkItem(record.handler_va, record.incoming_hash);
          ++merged_records;
        }
      }

      if (merged_records > 0) {
        errs() << "VMTraceMap: merged " << merged_records
               << " supplemental wrapper trace record(s) from "
               << supplemental_path << " for " << merged_wrappers.size()
               << " traced native target(s)\n";
      }
    };

    auto tagExactTraceHash = [&](llvm::Function &F, uint64_t handler_va) {
      auto it = handler_trace_hashes.find(handler_va);
      if (it == handler_trace_hashes.end() || it->second.size() != 1) {
        F.removeFnAttr("omill.vm_trace_in_hash");
        return;
      }
      F.addFnAttr("omill.vm_trace_in_hash",
                  llvm::utohexstr(it->second.front()));
    };
    // --- Populate vm_graph and trace_work_items from either external JSON
    //     or the built-in emulator. ---
    if (VMTraceJSON.getNumOccurrences()) {
      // External trace: load pre-computed VMTraceRecords from JSON.
      auto ext_graph = parseExternalVMTrace(VMTraceJSON);
      if (!ext_graph)
        return fail(1, "failed to parse --vm-trace-json");
      vm_graph = std::move(ext_graph);

      // Populate lift work items from the imported trace records.
      // Also collect native call targets (vmenter wrappers) that need
      // to be lifted as separate VM functions.
      for (const auto &handler_va : vm_graph->handlerEntries()) {
        auto records = vm_graph->getTraceRecords(handler_va);
        for (const auto &rec : records) {
          if (!imported_entry_seed_hash.has_value())
            imported_entry_seed_hash = rec.incoming_hash;
          recordTraceWorkItem(rec.handler_va, rec.incoming_hash);
          if (rec.native_target_va != 0) {
            native_call_vas.push_back(rec.native_target_va);
          }
        }
      }
      mergeSupplementalWrapperTrace(VMTraceJSON.getValue());
      events.emitInfo("vm_trace_imported", "external VM trace loaded",
                      {{"records",
                        static_cast<int64_t>(trace_work_items.size())},
                       {"source", VMTraceJSON.getValue()}});
    } else {
      omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                    vm_entry_va, vm_exit_va);

      // Set the handler segment range (seg006 bounds).
      uint64_t seg_start = vm_entry_va;
      uint64_t seg_end = vm_entry_va + 0x2000000;
      pe.memory_map.forEachRegion(
          [&](uint64_t base, const uint8_t *, size_t size) {
            if (vm_entry_va >= base && vm_entry_va < base + size) {
              seg_start = base;
              seg_end = base + size;
            }
          });
      solver.setHandlerSegmentRange(seg_start, seg_end);

      // Trace from the entry wrapper. Use vm_wrapper_va (which defaults to
      // func_va) so that --vm-wrapper can point to the actual lea/call pattern
      // even when --va is an outer function like DriverEntry.
      auto trace = solver.traceFromWrapper(vm_wrapper_va);
      if (!trace.empty()) {
        vm_graph->mergeTraceResults(solver);
        auto flat =
            vm_graph->followFlatTrace(vm_wrapper_va, trace.front().incoming_hash);
        events.emitInfo("vm_trace_built", "vm flat trace built",
                        {{"handlers", static_cast<int64_t>(flat.records.empty()
                                                           ? trace.size()
                                                           : flat.records.size())},
                         {"complete", flat.completed() ? int64_t{1} : int64_t{0}}});
        if (!flat.records.empty()) {
          rememberFlatTrace(flat.records);
        } else {
          rememberRawTrace(trace);
        }
      }

      // Trace from additional auto-detected wrappers.
      for (size_t wi = 1; wi < auto_detected_wrappers.size(); ++wi) {
        uint64_t extra_wrapper = auto_detected_wrappers[wi].second;
        auto extra_trace = solver.traceFromWrapper(extra_wrapper);
        if (!extra_trace.empty()) {
          vm_graph->mergeTraceResults(solver);
          auto flat = vm_graph->followFlatTrace(extra_wrapper,
                                                extra_trace.front().incoming_hash);
          if (!flat.records.empty()) {
            rememberFlatTrace(flat.records);
          } else {
            rememberRawTrace(extra_trace);
          }
        }
      }

      // Extract native call targets before the emulator goes out of scope.
      native_call_vas = solver.nativeCallTargets();
      native_call_infos = solver.nativeCallInfos();
      errs() << "Trace emulator captured " << native_call_infos.size()
             << " native call infos, " << native_call_vas.size()
             << " unique targets\n";
      for (unsigned i = 0; i < native_call_infos.size(); ++i) {
        errs() << "  [" << i << "] target=0x"
               << Twine::utohexstr(native_call_infos[i].target_va)
               << " from handler=0x"
               << Twine::utohexstr(native_call_infos[i].handler_va)
               << " R12=0x"
               << Twine::utohexstr(native_call_infos[i].r12_base)
               << " vmctx_size="
               << native_call_infos[i].vmcontext_snapshot.size()
               << "\n";
      }
    }

    auto seedWrapperTraceHash = [&](uint64_t wrapper_va) {
      if (!imported_entry_seed_hash.has_value())
        return;
      auto *fn = module->getFunction("sub_" + Twine::utohexstr(wrapper_va).str());
      if (!fn || fn->isDeclaration())
        return;
      fn->addFnAttr("omill.vm_trace_in_hash",
                    llvm::utohexstr(*imported_entry_seed_hash));
    };

    if (VMTraceJSON.getNumOccurrences()) {
      seedWrapperTraceHash(vm_wrapper_va);
      for (auto &[thunk_va, wrapper_va] : auto_detected_wrappers)
        seedWrapperTraceHash(wrapper_va);
    }

    // Lift only trace-reachable handlers.
    unsigned lifted_count = 0;
    unsigned failed_count = 0;
    unsigned skipped_count = 0;
    for (const auto &trace_item : trace_work_items) {
      uint64_t handler_va = trace_item.handler_va;
      // Skip if already lifted (e.g. func_va or vmenter/vmexit).
      std::string name = "sub_" + Twine::utohexstr(handler_va).str();
      if (auto *existing = module->getFunction(name)) {
        if (!existing->isDeclaration()) {
          // Tag existing function as a VM handler.
          existing->addFnAttr("omill.vm_handler");
          tagExactTraceHash(*existing, handler_va);
          // The VM wrapper is a boundary function: handlers get inlined
          // INTO it, but it must NOT be inlined into callers like
          // DriverEntry.  Tag it so VMHandlerInlinerPass excludes it
          // from the handler_set while keeping it in
          // VMDispatchResolution's scope (which requires vm_handler).
          if (handler_va == vm_wrapper_va) {
            existing->addFnAttr("omill.vm_wrapper");
          } else {
            for (auto &[tv, wv] : auto_detected_wrappers) {
              if (handler_va == wv) {
                existing->addFnAttr("omill.vm_wrapper");
                break;
              }
            }
          }
          continue;
        }
      }

      // Probe decode: skip handler VAs where the first instruction can't
      // be decoded.  These are typically decoy dispatch patterns in
      // obfuscated code with garbage RVAs pointing mid-instruction.
      {
        uint8_t probe_buf[15];
        if (!pe.memory_map.read(handler_va, probe_buf, sizeof(probe_buf))) {
          ++skipped_count;
          continue;
        }
        std::string_view probe_bytes(
            reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
        remill::Instruction probe_inst;
        if (!arch->DecodeInstruction(handler_va, probe_bytes, probe_inst,
                                     arch->CreateInitialContext())) {
          ++skipped_count;
          continue;
        }
      }

      if (lifter.Lift(handler_va)) {
        ++lifted_count;
        // Tag the lifted function.
        if (auto *fn = module->getFunction(name)) {
          fn->addFnAttr("omill.vm_handler");
          tagExactTraceHash(*fn, handler_va);
        } else {
          errs() << "  [WARN] Lift succeeded for 0x"
                 << Twine::utohexstr(handler_va)
                 << " but function " << name << " not found in module\n";
        }
      } else {
        errs() << "  [WARN] Lift FAILED for 0x"
               << Twine::utohexstr(handler_va) << "\n";
        ++failed_count;
      }
    }

    errs() << "VM bulk lift: " << lifted_count << " handlers lifted";
    if (skipped_count > 0)
      errs() << ", " << skipped_count << " skipped (bad VA)";
    if (failed_count > 0)
      errs() << ", " << failed_count << " failed";
    errs() << "\n";
    events.emitInfo("vm_bulk_lift_completed", "vm handler bulk lift complete",
                    {{"lifted", static_cast<int64_t>(lifted_count)},
                     {"skipped", static_cast<int64_t>(skipped_count)},
                     {"failed", static_cast<int64_t>(failed_count)}});

    // Lift native functions called through vmexit→call→vmentry.
    // These are regular (non-VM) functions that the VM handlers call
    // through temporary VM exit.  Lifting them enables ResolveIntToPtrCalls
    // to resolve the constant inttoptr calls after ABI recovery.
    if (!native_call_vas.empty()) {
      unsigned native_lifted = 0;
      auto tagTraceNativeTarget = [&](uint64_t native_va) {
        std::string tagged_name = "sub_" + Twine::utohexstr(native_va).str();
        if (auto *fn = module->getFunction(tagged_name)) {
          if (!fn->isDeclaration()) {
            fn->addFnAttr("omill.trace_native_target", "1");
            fn->addFnAttr(llvm::Attribute::NoInline);
          }
        }
      };
      for (uint64_t native_va : native_call_vas) {
        std::string name = "sub_" + Twine::utohexstr(native_va).str();
        if (auto *existing = module->getFunction(name)) {
          if (!existing->isDeclaration()) {
            tagTraceNativeTarget(native_va);
            continue;
          }
        }

        // Probe decode — skip if first instruction can't be decoded.
        {
          uint8_t probe_buf[15];
          if (!pe.memory_map.read(native_va, probe_buf, sizeof(probe_buf)))
            continue;
          std::string_view probe_bytes(
              reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
          remill::Instruction probe_inst;
          if (!arch->DecodeInstruction(native_va, probe_bytes, probe_inst,
                                       arch->CreateInitialContext()))
            continue;
        }

        if (lifter.Lift(native_va)) {
          ++native_lifted;
          tagTraceNativeTarget(native_va);
          // If this native VA is also in the trace work items (i.e. it's
          // a vmenter wrapper for an inner VM), tag it as vm_handler +
          // vm_wrapper so VMDispatchResolution can process it and
          // VMHandlerInliner won't inline it into callers.
          std::string name = "sub_" + Twine::utohexstr(native_va).str();
          if (auto *fn = module->getFunction(name)) {
            if (vm_graph && vm_graph->isVMHandler(native_va)) {
              fn->addFnAttr("omill.vm_handler");
              fn->addFnAttr("omill.vm_wrapper");
            }
          }
        }
      }
      errs() << "VM native lift: " << native_lifted << " native functions"
             << " (from " << native_call_vas.size() << " targets)\n";
    }

    // Tag native call targets that are vmenter wrappers (inner VM entry
    // points) so VMHandlerInliner preserves them as call boundaries.
    // Detection: follow jmp-thunks from the native VA, probe the resolved
    // body for [lea rsp,... / sub rsp,...] + call vmentry.
    if (!native_call_vas.empty() && vm_entry_va != 0) {
      unsigned wrapper_tagged = 0;
      for (uint64_t native_va : native_call_vas) {
        std::string name = "sub_" + Twine::utohexstr(native_va).str();
        auto *fn = module->getFunction(name);
        if (!fn || fn->isDeclaration())
          continue;
        // Already tagged as wrapper (e.g. matches vm_wrapper_va)?
        if (fn->hasFnAttribute("omill.vm_wrapper"))
          continue;
        // Follow jmp-thunks to the body.
        uint64_t resolved = native_va;
        for (int hop = 0; hop < 4; ++hop) {
          uint8_t tbuf[16];
          if (!pe.memory_map.read(resolved, tbuf, sizeof(tbuf)))
            break;
          if (tbuf[0] == 0xE9) {
            int32_t rel;
            std::memcpy(&rel, &tbuf[1], 4);
            resolved = resolved + 5 + static_cast<int64_t>(rel);
          } else if (tbuf[0] == 0xEB) {
            int8_t rel = static_cast<int8_t>(tbuf[1]);
            resolved = resolved + 2 + rel;
          } else {
            break;
          }
        }
        // Probe the resolved body for the wrapper pattern:
        //   optional lea rsp,[rsp-N] / sub rsp,N
        //   E8 <rel32>  (call near vmentry)
        uint8_t probe[32];
        if (!pe.memory_map.read(resolved, probe, sizeof(probe)))
          continue;
        unsigned p = 0;
        if (p + 8 <= sizeof(probe) &&
            probe[p] == 0x48 && probe[p+1] == 0x8D &&
            probe[p+2] == 0xA4 && probe[p+3] == 0x24) {
          p += 8;
        } else if (p + 5 <= sizeof(probe) &&
                   probe[p] == 0x48 && probe[p+1] == 0x8D &&
                   probe[p+2] == 0x64 && probe[p+3] == 0x24) {
          p += 5;
        } else if (p + 7 <= sizeof(probe) &&
                   probe[p] == 0x48 && probe[p+1] == 0x81 &&
                   probe[p+2] == 0xEC) {
          p += 7;
        }
        if (p + 5 > sizeof(probe) || probe[p] != 0xE8)
          continue;
        int32_t crel;
        std::memcpy(&crel, &probe[p+1], 4);
        uint64_t ctarget = resolved + p + 5 + static_cast<int64_t>(crel);
        // Accept if the call target is the vmentry, the vm wrapper, or
        // within 0x1000 of either.
        bool near_entry = (ctarget >= vm_entry_va - 0x1000 &&
                           ctarget <= vm_entry_va + 0x1000);
        bool near_wrapper = (vm_wrapper_va != 0 &&
                             ctarget >= vm_wrapper_va - 0x1000 &&
                             ctarget <= vm_wrapper_va + 0x1000);
        if (!near_entry && !near_wrapper)
          continue;
        // This native target is a vmenter wrapper.  Tag it so
        // VMHandlerInliner preserves it as a call boundary.
        fn->addFnAttr("omill.vm_wrapper");
        if (!fn->hasFnAttribute("omill.vm_handler"))
          fn->addFnAttr("omill.vm_handler");
        ++wrapper_tagged;
        errs() << "Native target 0x" << Twine::utohexstr(native_va)
               << " is vmenter wrapper (body 0x"
               << Twine::utohexstr(resolved) << ")\n";
      }
      if (wrapper_tagged > 0)
        errs() << "Tagged " << wrapper_tagged
               << " native targets as vmenter wrappers\n";
    }

    // Fix DeclareLiftedFunction naming collisions (sub_X.N → sub_X).
    // Must happen BEFORE setting attributes on vmentry/vmexit, because
    // the fix erases declarations (which may hold attributes from the
    // chain handler loop above) and renames definitions (which don't).
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto fname = F.getName();
      if (!fname.starts_with("sub_"))
        continue;
      for (int i = 1; i <= 20; ++i) {
        std::string def_name = (fname + "." + Twine(i)).str();
        if (auto *def = module->getFunction(def_name)) {
          if (!def->isDeclaration()) {
            F.replaceAllUsesWith(def);
            F.eraseFromParent();
            def->setName(fname);
            break;
          }
        }
      }
    }

    bool verbose_vm_demerge = (std::getenv("OMILL_VM_VERBOSE") != nullptr);
    unsigned demerged_clone_count = 0;
    for (auto &[handler_va, hashes] : handler_trace_hashes) {
      if (verbose_vm_demerge) {
        errs() << "VM demerge candidate 0x" << Twine::utohexstr(handler_va)
               << " hashes=" << hashes.size() << "\n";
      }
      if (hashes.size() <= 1)
        continue;

      bool is_vm_wrapper_handler = (handler_va == vm_wrapper_va) ||
                                   (handler_va == vm_entry_va) ||
                                   (handler_va == vm_exit_va);
      if (!is_vm_wrapper_handler) {
        for (auto &[tv, wv] : auto_detected_wrappers) {
          if (handler_va == wv) {
            is_vm_wrapper_handler = true;
            break;
          }
        }
      }
      if (is_vm_wrapper_handler) {
        if (verbose_vm_demerge) {
          errs() << "  skip wrapper-like handler 0x"
                 << Twine::utohexstr(handler_va) << "\n";
        }
        continue;
      }

      auto *base_fn = module->getFunction(omill::liftedFunctionName(handler_va));
      if (!base_fn || base_fn->isDeclaration()) {
        if (verbose_vm_demerge) {
          errs() << "  missing lifted base for 0x"
                 << Twine::utohexstr(handler_va) << "\n";
        }
        continue;
      }

      for (uint64_t incoming_hash : hashes) {
        std::string clone_name =
            omill::demergedHandlerCloneName(handler_va, incoming_hash);
        if (module->getFunction(clone_name))
          continue;

        llvm::ValueToValueMapTy VMap;
        auto *clone = llvm::CloneFunction(base_fn, VMap);
        clone->setName(clone_name);
        clone->setLinkage(llvm::GlobalValue::InternalLinkage);
        clone->addFnAttr("omill.vm_handler");
        clone->addFnAttr("omill.vm_demerged_clone", "1");
        clone->addFnAttr("omill.vm_trace_in_hash",
                         llvm::utohexstr(incoming_hash));
        ++demerged_clone_count;

        if (verbose_vm_demerge) {
          errs() << "Demerged VM handler clone " << clone_name
                 << " from 0x" << Twine::utohexstr(handler_va)
                 << " hash=0x" << Twine::utohexstr(incoming_hash) << "\n";
        }
      }
    }
    if (demerged_clone_count > 0) {
      errs() << "VM demerge: materialized " << demerged_clone_count
             << " hash-keyed handler clones\n";
      if (events.enabled()) {
        events.emitInfo("vm_demerge_materialized",
                        "vm demerged handler clones materialized",
                        {{"clones", static_cast<int64_t>(demerged_clone_count)}});
      }
    }


    // After naming collisions are fixed, tag vmentry/vmexit as vm_handler
    // and set internal linkage.  Must happen AFTER the naming fix because
    // DeclareLiftedFunction creates sub_X.1 definitions for existing sub_X
    // declarations; the fix erases the declaration (losing any attributes
    // we set) and renames the definition.
    //
    // vmentry must NOT get AlwaysInline.  If inlined at Phase 0, its
    // __remill_function_return ends up inside DriverEntry; LowerFunctionReturn
    // (Phase 3b) converts it to `ret`, creating an early return that kills
    // DriverEntry's continuation code (hash computation + dispatch to the
    // first handler).  Instead, vmentry is tagged omill.vm_handler so
    // VMHandlerInlinerPass inlines it at Phase 3.56 — by that point
    // LowerFunctionReturn has already converted vmentry's return to a plain
    // `ret`, and LLVM's InlineFunction replaces it with a branch to the
    // continuation block.  The vmcontext alloca then lands on DriverEntry's
    // stack (fixing the dangling-pointer / 0xCC sentinel issue).
    if (auto *fn = module->getFunction(
            "sub_" + Twine::utohexstr(vm_entry_va).str())) {
      fn->addFnAttr("omill.vm_handler");
      fn->setLinkage(llvm::GlobalValue::InternalLinkage);
      // Tag direct callees of vmentry as vm_handlers too — they're
      // internal helpers (PIC relocation, etc.) that only make sense
      // in the caller's stack context and should be inlined into vmentry.
      for (auto &BB : *fn) {
        for (auto &I : BB) {
          if (auto *call = dyn_cast<CallInst>(&I)) {
            if (auto *callee = call->getCalledFunction()) {
              if (callee->getName().starts_with("sub_") &&
                  !callee->isDeclaration()) {
                callee->addFnAttr("omill.vm_handler");
                callee->setLinkage(llvm::GlobalValue::InternalLinkage);
              }
            }
          }
        }
      }
    } else {
      // vm_entry function not found at its exact VA — likely a thunk/E9
      // chain was resolved by remill, folding the vm_entry code into the
      // thunk's function.  Find functions that contain __remill_jump
      // (i.e., the unresolved indirect jump from the vm_enter tail) and tag
      // them as vm_handlers so VMDispatchResolution can resolve them.
      // At this point the passes haven't run yet, so the intrinsic is still
      // __remill_jump (later lowered to __omill_dispatch_jump).
      auto *jump_fn = module->getFunction("__remill_jump");
      if (jump_fn) {
        for (auto *user : jump_fn->users()) {
          if (auto *call = dyn_cast<CallInst>(user)) {
            auto *parent = call->getFunction();
            if (parent && !parent->isDeclaration() &&
                parent->getName().starts_with("sub_") &&
                !parent->hasFnAttribute("omill.vm_handler")) {
              parent->addFnAttr("omill.vm_handler");
              parent->addFnAttr("omill.vm_wrapper");
              parent->setLinkage(llvm::GlobalValue::InternalLinkage);
              errs() << "VM thunk fixup: tagged " << parent->getName()
                     << " as vm_handler+vm_wrapper (thunk-resolved vmenter)\n";
              // Also tag its callees
              for (auto &BB : *parent) {
                for (auto &I : BB) {
                  if (auto *inner_call = dyn_cast<CallInst>(&I)) {
                    if (auto *callee = inner_call->getCalledFunction()) {
                      if (callee->getName().starts_with("sub_") &&
                          !callee->isDeclaration() &&
                          !callee->hasFnAttribute("omill.vm_handler")) {
                        callee->addFnAttr("omill.vm_handler");
                        callee->setLinkage(llvm::GlobalValue::InternalLinkage);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    if (vm_exit_va != 0) {
      if (auto *fn = module->getFunction(
              "sub_" + Twine::utohexstr(vm_exit_va).str())) {
        fn->addFnAttr("omill.vm_handler");
        fn->setLinkage(llvm::GlobalValue::InternalLinkage);
      }
    }
  }

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("before.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote before.ll\n";
    }
  }

  // Set up pass timing and verification instrumentation.
  PassInstrumentationCallbacks PIC;
  TimePassesHandler TimingHandler(OmillTimePasses);
  TimingHandler.registerCallbacks(PIC);

  struct PassTimingFrame {
    std::string pass_name;
    std::string ir_kind;
    std::string ir_name;
    const void *ir_ptr = nullptr;
    std::chrono::steady_clock::time_point started_at;
  };
  llvm::SmallVector<PassTimingFrame, 32> pass_timing_stack;

  auto describeIRUnit = [](Any IR) {
    std::pair<std::string, std::string> desc{"unknown", ""};
    if (const auto **F = any_cast<const Function *>(&IR)) {
      desc.first = "function";
      desc.second = (*F)->getName().str();
    } else if (const auto **MPtr = any_cast<const Module *>(&IR)) {
      desc.first = "module";
      desc.second = (*MPtr)->getModuleIdentifier();
    } else if (const auto **L = any_cast<const Loop *>(&IR)) {
      desc.first = "loop";
      desc.second = (*L)->getHeader()->getParent()->getName().str();
    }
    return desc;
  };

  auto irPointer = [](Any IR) -> const void * {
    if (const auto **F = any_cast<const Function *>(&IR))
      return *F;
    if (const auto **MPtr = any_cast<const Module *>(&IR))
      return *MPtr;
    if (const auto **L = any_cast<const Loop *>(&IR))
      return *L;
    return nullptr;
  };

  auto shouldEmitPassTiming = [&](StringRef PassName) {
    if (!events.enabled() || !events.detailed())
      return false;
    if (PassName.starts_with("PassManager") || PassName.contains("Adaptor"))
      return false;
    return true;
  };

  PIC.registerBeforeNonSkippedPassCallback(
      [&](StringRef PassName, Any IR) {
        if (!shouldEmitPassTiming(PassName))
          return;
        auto [ir_kind, ir_name] = describeIRUnit(IR);
        pass_timing_stack.push_back(
            {PassName.str(), std::move(ir_kind), std::move(ir_name),
             irPointer(IR), std::chrono::steady_clock::now()});
      });

  if (events.enabled()) {
    PIC.registerAfterPassCallback([&events](StringRef PassName, Any,
                                            const PreservedAnalyses &) {
      if (PassName.contains("PhaseMarkerPass")) {
        events.emitInfo("pipeline_phase_boundary", "phase boundary",
                        {{"pass", PassName.str()}});
      } else if (events.detailed() && PassName.contains("omill")) {
        events.emitInfo("pipeline_pass", "pass completed",
                        {{"pass", PassName.str()}});
      }
    });
    PIC.registerAfterPassCallback(
        [&](StringRef PassName, Any IR, const PreservedAnalyses &) {
          if (!shouldEmitPassTiming(PassName) || pass_timing_stack.empty())
            return;
          auto ir_ptr = irPointer(IR);
          for (auto it = pass_timing_stack.end(); it != pass_timing_stack.begin();) {
            --it;
            if (it->pass_name != PassName.str() || it->ir_ptr != ir_ptr)
              continue;
            auto duration_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                                   std::chrono::steady_clock::now() -
                                   it->started_at)
                                   .count();
            events.emitInfo("pipeline_pass_timing", "pass timing",
                            {{"pass", it->pass_name},
                             {"ir_kind", it->ir_kind},
                             {"ir_name", it->ir_name},
                             {"duration_ms",
                              static_cast<int64_t>(duration_ms)}});
            pass_timing_stack.erase(it);
            break;
          }
        });
    PIC.registerAfterPassInvalidatedCallback(
        [&](StringRef PassName, const PreservedAnalyses &) {
          if (!shouldEmitPassTiming(PassName) || pass_timing_stack.empty())
            return;
          for (auto it = pass_timing_stack.end(); it != pass_timing_stack.begin();) {
            --it;
            if (it->pass_name != PassName.str())
              continue;
            auto duration_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                                   std::chrono::steady_clock::now() -
                                   it->started_at)
                                   .count();
            events.emitInfo("pipeline_pass_timing", "pass timing",
                            {{"pass", it->pass_name},
                             {"ir_kind", it->ir_kind},
                             {"ir_name", it->ir_name},
                             {"duration_ms",
                              static_cast<int64_t>(duration_ms)},
                             {"invalidated_ir", true}});
            pass_timing_stack.erase(it);
            break;
          }
        });
  }

  // Set up pass infrastructure
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  StandardInstrumentations SI(ctx, /*DebugLogging=*/false,
                              /*VerifyEach=*/false);
  SI.registerCallbacks(PIC, &MAM);

  // Custom safe verify-each: only runs after omill custom passes (not LLVM
  // standard passes) for performance.  Uses nullptr stream to avoid crash
  // in SlotTracker on corrupted modules.
  if (VerifyEach) {
    PIC.registerAfterPassCallback(
        [&](StringRef PassName, Any IR,
            const PreservedAnalyses &) {
          // Skip standard LLVM passes — verifying after every InstCombine/
          // GVN/SimplifyCFG etc. is prohibitively slow.
          static const char *const llvm_passes[] = {
              "InstCombinePass",
              "GVNPass",
              "SimplifyCFGPass",
              "SROAPass",
              "ADCEPass",
              "DSEPass",
              "EarlyCSEPass",
              "GlobalDCEPass",
              "AlwaysInlinerPass",
              "InlinerPass",
              "GlobalOptPass",
              "LoopSimplifyPass",
              "LCSSAPass",
              "LoopRotatePass",
              "LICMPass",
              "IndVarSimplifyPass",
              "LoopDeletionPass",
              "LoopUnrollPass",
              "JumpThreadingPass",
              "CorrelatedValuePropagationPass",
              "MemCpyOptPass",
              "SCCPPass",
              "BDCEPass",
              "ReassociatePass",
              "MergedLoadStoreMotionPass",
              "TailCallElimPass",
              "PromotePass",
              "AggressiveInstCombinePass",
              "LibCallsShrinkWrapPass",
              "ConstraintEliminationPass",
              "CoroSplitPass",
              "CoroElidePass",
              "InvalidateAnalysisPass",
              "RequireAnalysisPass",
              "VerifierPass",
              "PrintModulePass",
              "BitcodeWriterPass",
          };
          for (const char *p : llvm_passes) {
            if (PassName == p) return;
          }
          // Also skip pass manager wrappers and adaptors.
          if (PassName.starts_with("PassManager") ||
              PassName.starts_with("ModuleToFunction") ||
              PassName.starts_with("CGSCCToFunction") ||
              PassName.starts_with("ModuleInliner") ||
              PassName.starts_with("DevirtSCCRepeated") ||
              PassName.contains("Adaptor") ||
              PassName.contains("PassManager"))
            return;

          // Extract the module from whatever IR level we're at.
          const Module *M = nullptr;
          if (const auto **F = any_cast<const Function *>(&IR))
            M = (*F)->getParent();
          else if (const auto **MPtr = any_cast<const Module *>(&IR))
            M = *MPtr;
          else if (const auto **L = any_cast<const Loop *>(&IR))
            M = (*L)->getHeader()->getParent()->getParent();
          if (!M) return;

          if (verifyModule(*M, nullptr)) {
            errs() << "VERIFY-EACH: verification failed after pass: "
                   << PassName << "\n";
            events.emitError("verify_each_failed",
                             "module verification failed after pass",
                             {{"pass", PassName.str()}});
            events.emitTerminalFailure(1, "verify-each failure");
            // Don't try module->print() — SlotTracker may crash on
            // corrupted modules with dangling Comdat/Value references.
            // Per-function verification to narrow down:
            for (const auto &F : *M) {
              if (F.isDeclaration()) continue;
              if (verifyFunction(F, nullptr))
                errs() << "  broken function: " << F.getName() << "\n";
            }
            exit(1);
          }
        });
  }

  // --trace-func: print block/instruction counts after every pass for a
  // specific function.  Helps diagnose when the function body disappears.
  if (!TraceFunc.empty()) {
    // Track both the lifted name and the _native wrapper.
    std::string target_base = TraceFunc;
    std::string target_native = target_base + "_native";
    unsigned prev_blocks = 0, prev_insts = 0;
    unsigned prev_blocks_n = 0, prev_insts_n = 0;
    unsigned dump_seq = 0;

    // Helper: dump function IR to a file for post-mortem analysis.
    auto dumpFuncIR = [&](const Function *F, StringRef reason,
                          unsigned seq) {
      if (!DumpFuncPhases || !F || F->isDeclaration())
        return;
      std::string filename = (F->getName() + ".phase" +
                              llvm::Twine(seq) + ".ll").str();
      std::error_code EC;
      llvm::raw_fd_ostream OS(filename, EC);
      if (EC) return;
      OS << "; " << reason << "\n";
      F->print(OS);
      errs() << "[TRACE] dumped " << F->getName() << " → " << filename
             << " (" << reason << ")\n";
    };

    PIC.registerAfterPassCallback(
        [=, &prev_blocks, &prev_insts,
         &prev_blocks_n, &prev_insts_n,
         &dump_seq, &dumpFuncIR](
            StringRef PassName, Any IR, const PreservedAnalyses &) mutable {
          const Module *M = nullptr;
          if (const auto **F = any_cast<const Function *>(&IR))
            M = (*F)->getParent();
          else if (const auto **MPtr = any_cast<const Module *>(&IR))
            M = *MPtr;
          else if (const auto **L = any_cast<const Loop *>(&IR))
            M = (*L)->getHeader()->getParent()->getParent();
          if (!M) return;

          auto report = [&](const std::string &name,
                            unsigned &pb, unsigned &pi) {
            auto *F = M->getFunction(name);
            if (!F || F->isDeclaration()) {
              if (pb != 0 || pi != 0) {
                errs() << "[TRACE] " << PassName << " | " << name
                       << ": GONE (was " << pb << " blocks, "
                       << pi << " instrs)\n";
                pb = 0;
                pi = 0;
              }
              return;
            }
            unsigned blocks = 0, insts = 0;
            for (auto &BB : *F) {
              ++blocks;
              insts += BB.size();
            }
            if (blocks != pb || insts != pi) {
              int di = (pi > 0) ? (int)insts - (int)pi : 0;
              errs() << "[TRACE] " << PassName << " | " << name
                     << ": " << blocks << " blocks, " << insts
                     << " instrs";
              if (pb != 0) {
                int db = (int)blocks - (int)pb;
                errs() << " (delta: " << db << " blocks, "
                       << di << " instrs)";
              }
              errs() << "\n";

              // Dump IR on large drops (>30% instruction loss) or phase markers.
              bool is_phase = PassName.contains("PhaseMarker");
              bool large_drop = pi > 0 && di < 0 &&
                                (unsigned)(-di) > pi * 3 / 10;
              if (DumpFuncPhases && (is_phase || large_drop)) {
                std::string reason = (PassName + " | " +
                    llvm::Twine(blocks) + "bb/" +
                    llvm::Twine(insts) + "i").str();
                dumpFuncIR(F, reason, dump_seq++);
              }

              pb = blocks;
              pi = insts;
            }
          };

          report(target_base, prev_blocks, prev_insts);
          report(target_native, prev_blocks_n, prev_insts_n);
        });
  }

  PassBuilder PB(nullptr, PipelineTuningOptions(), std::nullopt, &PIC);

  // Register custom module analyses first and keep backing storage stable.
  omill::BinaryMemoryMap raw_memory_map;
  if (RawBinary) {
    raw_memory_map.addRegion(BaseAddress, raw_code.data(), raw_code.size(),
                             true, /*executable=*/true);
    raw_memory_map.setImageBase(BaseAddress);
    raw_memory_map.setImageSize(raw_code.size());
  }
  auto memory_map_holder =
      std::make_shared<omill::BinaryMemoryMap>(
          RawBinary ? std::move(raw_memory_map) : pe.memory_map);
  MAM.registerPass([memory_map_holder] {
    return omill::BinaryMemoryAnalysis(*memory_map_holder);
  });

  std::shared_ptr<omill::ExceptionInfo> exception_info_holder;
  if (!RawBinary && ResolveExceptions) {
    exception_info_holder =
        std::make_shared<omill::ExceptionInfo>(std::move(pe.exception_info));
    MAM.registerPass([exception_info_holder] {
      return omill::ExceptionInfoAnalysis(*exception_info_holder);
    });
  }

  // Build AAManager with omill's custom SegmentsAA before standard
  // registration so it's included in LLVM's AA pipeline.
  FAM.registerPass([&] {
    auto AAM = PB.buildDefaultAAPipeline();
    omill::registerAAWithManager(AAM);
    return AAM;
  });

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);  // AAManager already registered, skipped.
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  omill::registerAnalyses(FAM);
  // Register remaining module analyses without overriding custom ones above.
  MAM.registerPass([&] { return omill::TargetArchAnalysis(); });
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });
  MAM.registerPass([&] { return omill::CallGraphAnalysis(); });
  MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
  MAM.registerPass([iterative_session] {
    return omill::IterativeLiftingSessionAnalysis(iterative_session);
  });
  MAM.registerPass([&] { return omill::VirtualCalleeRegistryAnalysis(); });
  MAM.registerPass([&] { return omill::VirtualMachineModelAnalysis(); });
  if (!ResolveExceptions) {
    MAM.registerPass([&] { return omill::ExceptionInfoAnalysis(); });
  }

  // Register the emulator-derived VM trace map analysis.
  if (vm_graph) {
    MAM.registerPass([vm_graph] {
      return omill::VMTraceMapAnalysis(*vm_graph);
    });
  } else {
    MAM.registerPass([&] { return omill::VMTraceMapAnalysis(); });
  }

  // Register trace-lift callback so IterativeTargetResolutionPass can
  // lift new functions from resolved dispatch targets.
  auto safeTraceLiftTarget = [&](uint64_t pc) -> bool {
#if defined(_WIN32)
    __try {
#endif
      bool ok = lifter.Lift(pc);
      if (ok)
        iterative_session->noteLiftedTarget(pc);
      return ok;
#if defined(_WIN32)
    } __except (1) {
      errs() << "WARNING: TraceLifter crashed at 0x"
             << llvm::Twine::utohexstr(pc) << "\n";
      if (events.detailed()) {
        events.emitWarn("trace_lift_crashed",
                        "trace lift crashed for discovered target",
                        {{"va", ("0x" + llvm::Twine::utohexstr(pc)).str()}});
      }
      return false;
    }
#endif
  };

  auto safeBlockLiftTarget = [&](uint64_t pc) -> bool {
    if (!block_lifter)
      return false;
#if defined(_WIN32)
    __try {
#endif
      llvm::SmallVector<uint64_t, 4> targets;
      auto *fn = block_lifter->LiftBlock(pc, targets);
      if (fn)
        iterative_session->noteLiftedTarget(pc);
      return fn != nullptr;
#if defined(_WIN32)
    } __except (1) {
      errs() << "WARNING: BlockLifter crashed at 0x"
             << llvm::Twine::utohexstr(pc) << "\n";
      if (events.detailed()) {
        events.emitWarn("block_lift_crashed",
                        "block lift crashed for discovered target",
                        {{"va", ("0x" + llvm::Twine::utohexstr(pc)).str()}});
      }
      return false;
    }
#endif
  };

  {
    omill::TraceLiftCallback trace_cb;
    if (ResolveTargets) {
      trace_cb = safeTraceLiftTarget;
    }
    iterative_session->setTraceLiftCallback(trace_cb);
    MAM.registerPass([trace_cb] {
      return omill::TraceLiftAnalysis(trace_cb);
    });
  }

  // Always register BlockLiftAnalysis so late generic-static cleanup passes
  // can query it safely on both block-lift and plain-lift runs.
  omill::BlockLiftCallback lift_cb;
  if (block_lifter) {
    lift_cb = safeBlockLiftTarget;
  }
  iterative_session->setBlockLiftCallback(lift_cb);
  MAM.registerPass([lift_cb] {
    return omill::BlockLiftAnalysis(lift_cb);
  });
  // Prime the lightweight block-lift callback analysis so later function
  // passes can retrieve it through getCachedResult via the module proxy.
  (void) MAM.getResult<omill::BlockLiftAnalysis>(*module);

  auto runPostPatchCleanup = [&](StringRef reason) {
    ModulePassManager MPM;
    omill::buildPostPatchCleanupPipeline(MPM, 80);
    MPM.run(*module, MAM);

    if (events.detailed()) {
      events.emitInfo("post_patch_cleanup_completed",
                      "post patch cleanup completed",
                      {{"reason", reason.str()}});
    }
  };

  auto runLateClosureCanonicalization = [&](StringRef reason) {
    ModulePassManager MPM;
    omill::buildLateClosureCanonicalizationPipeline(MPM);
    MPM.run(*module, MAM);

    if (events.detailed()) {
      events.emitInfo("late_closure_canonicalization_completed",
                      "late closure canonicalization completed",
                      {{"reason", reason.str()}});
    }
  };

  auto restoreVMHandlerAttrs = [&]() {
    if (!vm_graph)
      return;

    for (uint64_t va : vm_graph->handlerEntries()) {
      std::string name = "sub_" + Twine::utohexstr(va).str();
      if (auto *fn = module->getFunction(name)) {
        if (!fn->isDeclaration()) {
          fn->addFnAttr("omill.vm_handler");
          if (va == vm_wrapper_va)
            fn->addFnAttr("omill.vm_wrapper");
        }
      }
    }

    for (uint64_t va : {vm_entry_va, vm_exit_va}) {
      if (!va)
        continue;
      std::string name = "sub_" + Twine::utohexstr(va).str();
      if (auto *fn = module->getFunction(name)) {
        if (!fn->isDeclaration()) {
          fn->addFnAttr("omill.vm_handler");
          // Tag direct callees of vmentry/vmexit as vm_handlers too.
          if (va == vm_entry_va) {
            for (auto &BB : *fn) {
              for (auto &I : BB) {
                if (auto *call = dyn_cast<CallInst>(&I)) {
                  if (auto *callee = call->getCalledFunction()) {
                    if (callee->getName().starts_with("sub_") &&
                        !callee->isDeclaration()) {
                      callee->addFnAttr("omill.vm_handler");
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  };

  // Run the main pipeline (without ABI first)
  const bool requested_root_is_export =
      !RawBinary &&
      (std::find(pe.exported_function_starts.begin(),
                 pe.exported_function_starts.end(),
                 requested_func_va) != pe.exported_function_starts.end());
  const bool normalized_export_thunk_root =
      requested_root_is_export && requested_func_va != func_va;
  auto scanExportDirectCallsiteWin64ParamCount = [&](uint64_t target_va) {
    if (RawBinary || pe.is_macho || !requested_root_is_export)
      return 0u;
    if (target_arch != omill::TargetArch::kX86_64 || target_os_str != "windows")
      return 0u;

    auto mapPhysicalRegToParamIndex = [](unsigned reg_id)
        -> std::optional<unsigned> {
      switch (reg_id) {
        case 1:
          return 0;  // RCX
        case 2:
          return 1;  // RDX
        case 8:
          return 2;  // R8
        case 9:
          return 3;  // R9
        default:
          return std::nullopt;
      }
    };

    auto classifyWrittenWin64Param = [&](llvm::ArrayRef<uint8_t> inst_bytes)
        -> std::optional<unsigned> {
      if (inst_bytes.empty())
        return std::nullopt;

      size_t i = 0;
      uint8_t rex = 0;
      if ((inst_bytes[i] & 0xF0u) == 0x40u) {
        rex = inst_bytes[i++];
        if (i >= inst_bytes.size())
          return std::nullopt;
      }

      auto regFromOpcodeLowBits = [&](uint8_t opcode_low_bits) {
        return mapPhysicalRegToParamIndex(
            static_cast<unsigned>(opcode_low_bits) +
            ((rex & 0x1u) ? 8u : 0u));
      };
      auto regFromModRMReg = [&](uint8_t modrm) {
        return mapPhysicalRegToParamIndex(
            static_cast<unsigned>((modrm >> 3u) & 0x7u) +
            ((rex & 0x4u) ? 8u : 0u));
      };
      auto regFromModRMRM = [&](uint8_t modrm) {
        return mapPhysicalRegToParamIndex(
            static_cast<unsigned>(modrm & 0x7u) +
            ((rex & 0x1u) ? 8u : 0u));
      };

      const uint8_t opcode = inst_bytes[i];
      if (opcode >= 0xB8u && opcode <= 0xBFu)
        return regFromOpcodeLowBits(static_cast<uint8_t>(opcode - 0xB8u));

      if ((opcode == 0x8Bu || opcode == 0x8Du || opcode == 0x33u) &&
          (i + 1u) < inst_bytes.size()) {
        return regFromModRMReg(inst_bytes[i + 1u]);
      }

      if (opcode == 0x0Fu && (i + 2u) < inst_bytes.size() &&
          inst_bytes[i + 1u] == 0xB6u) {
        return regFromModRMReg(inst_bytes[i + 2u]);
      }

      if (opcode == 0x31u && (i + 1u) < inst_bytes.size()) {
        const uint8_t modrm = inst_bytes[i + 1u];
        if (((modrm >> 6u) & 0x3u) == 0x3u &&
            (((modrm >> 3u) & 0x7u) == (modrm & 0x7u))) {
          return regFromModRMRM(modrm);
        }
      }

      return std::nullopt;
    };

    auto scanDirectRel32CallsitesForTarget = [&](uint64_t callee_va) {
      unsigned max_param_count = 0;
      auto decode_ctx = arch->CreateInitialContext();
      remill::Instruction decoded_inst;
      auto isCallInstruction = [](llvm::ArrayRef<uint8_t> inst_bytes) {
        if (inst_bytes.empty())
          return false;
        size_t i = 0;
        if ((inst_bytes[i] & 0xF0u) == 0x40u) {
          ++i;
          if (i >= inst_bytes.size())
            return false;
        }
        const uint8_t opcode = inst_bytes[i];
        if (opcode == 0xE8u)
          return true;
        if (opcode == 0xFFu && (i + 1u) < inst_bytes.size()) {
          const uint8_t modrm = inst_bytes[i + 1u];
          return (((modrm >> 3u) & 0x7u) == 0x2u);
        }
        return false;
      };
      for (const auto &sec : pe.code_sections) {
        if (sec.storage_index >= pe.section_storage.size())
          continue;
        const auto &stored = pe.section_storage[sec.storage_index];
        if (stored.size() < 5u)
          continue;

        for (size_t i = 0; i + 5u <= stored.size(); ++i) {
          if (stored[i] != 0xE8u)
            continue;

          int32_t rel = 0;
          std::memcpy(&rel, stored.data() + i + 1u, sizeof(rel));
          const uint64_t call_pc = sec.va + i;
          const uint64_t call_target =
              call_pc + 5u + static_cast<int64_t>(rel);
          if (call_target != callee_va)
            continue;

          std::array<bool, 4> seen_param_writes = {
              false, false, false, false};
          const size_t window_start = (i > 48u) ? (i - 48u) : 0u;
          size_t cursor = window_start;
          while (cursor < i) {
            const size_t remaining = std::min<size_t>(15u, stored.size() - cursor);
            std::string_view probe_bytes(
                reinterpret_cast<const char *>(stored.data() + cursor), remaining);
            decoded_inst.Reset();
            if (!arch->DecodeInstruction(sec.va + cursor, probe_bytes, decoded_inst,
                                         decode_ctx) ||
                decoded_inst.NumBytes() == 0) {
              ++cursor;
              continue;
            }
            const size_t inst_size = std::min<size_t>(decoded_inst.NumBytes(), i - cursor);
            llvm::ArrayRef<uint8_t> inst_bytes(stored.data() + cursor, inst_size);
            if (isCallInstruction(inst_bytes)) {
              seen_param_writes = {false, false, false, false};
              cursor += decoded_inst.NumBytes();
              continue;
            }
            if (auto param_index = classifyWrittenWin64Param(inst_bytes)) {
              seen_param_writes[*param_index] = true;
            }
            cursor += decoded_inst.NumBytes();
          }

          unsigned param_count = 0;
          while (param_count < seen_param_writes.size() &&
                 seen_param_writes[param_count]) {
            ++param_count;
          }
          max_param_count = std::max(max_param_count, param_count);
        }
      }
      return max_param_count;
    };

    auto findDirectJmpThunkTarget = [&](uint64_t root_va)
        -> std::optional<uint64_t> {
      const auto *section = findCodeSection(pe, root_va);
      if (!section || section->storage_index >= pe.section_storage.size())
        return std::nullopt;
      const auto &stored = pe.section_storage[section->storage_index];
      const size_t offset = static_cast<size_t>(root_va - section->va);
      if (offset >= stored.size())
        return std::nullopt;
      const size_t remaining = stored.size() - offset;
      if (remaining >= 5u && stored[offset] == 0xE9u) {
        int32_t rel = 0;
        std::memcpy(&rel, stored.data() + offset + 1u, sizeof(rel));
        return root_va + 5u + static_cast<int64_t>(rel);
      }
      if (remaining >= 2u && stored[offset] == 0xEBu) {
        int8_t rel = static_cast<int8_t>(stored[offset + 1u]);
        return root_va + 2u + rel;
      }
      return std::nullopt;
    };

    unsigned max_param_count = scanDirectRel32CallsitesForTarget(target_va);
    if (max_param_count != 0)
      return max_param_count;

    if (auto thunk_target = findDirectJmpThunkTarget(target_va))
      return scanDirectRel32CallsitesForTarget(*thunk_target);

    return 0u;
  };
  auto annotateExportCallsiteWin64ParamHint = [&](uint64_t callsite_root_va,
                                                  uint64_t tagged_root_va) {
    const unsigned hint_count =
        scanExportDirectCallsiteWin64ParamCount(callsite_root_va);
    const bool debug_export_callsite_abi_hints =
        (std::getenv("OMILL_DEBUG_EXPORT_CALLSITE_ABI_HINTS") != nullptr);
    if (hint_count == 0)
      {
        if (debug_export_callsite_abi_hints) {
          errs() << "[export-callsite-abi-hint] root=0x"
                 << Twine::utohexstr(callsite_root_va) << " hint_count=0\n";
        }
      return;
      }

    unsigned tagged = 0;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      if (omill::extractEntryVA(F.getName()) != tagged_root_va)
        continue;
      F.addFnAttr("omill.export_callsite_win64_gpr_count",
                  std::to_string(hint_count));
      ++tagged;
    }

    if (debug_export_callsite_abi_hints) {
      errs() << "[export-callsite-abi-hint] root=0x"
             << Twine::utohexstr(callsite_root_va) << " tagged_root=0x"
             << Twine::utohexstr(tagged_root_va) << " hint_count="
             << hint_count << " tagged=" << tagged << "\n";
    }
    if (tagged != 0) {
      errs() << "Export callsite ABI hint: root=0x"
             << Twine::utohexstr(callsite_root_va) << " tagged_root=0x"
             << Twine::utohexstr(tagged_root_va) << " win64_gpr_params="
             << hint_count << " tagged_roots=" << tagged << "\n";
    }
  };
  auto scanExportEntryHiddenSeedExprs = [&](uint64_t root_va) {
    const bool debug_public_root_seeds =
        (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
    if (RawBinary || pe.is_macho || !requested_root_is_export) {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped raw=" << RawBinary
               << " macho=" << pe.is_macho
               << " requested_root_is_export=" << requested_root_is_export
               << "\n";
      }
      return std::string();
    }
    if (target_arch != omill::TargetArch::kX86_64 || target_os_str != "windows") {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped arch=" << static_cast<unsigned>(target_arch)
               << " os=" << target_os_str << "\n";
      }
      return std::string();
    }

    const auto *section = findCodeSection(pe, root_va);
    if (!section || section->storage_index >= pe.section_storage.size()) {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped missing section\n";
      }
      return std::string();
    }
    const auto &stored = pe.section_storage[section->storage_index];
    const size_t offset = static_cast<size_t>(root_va - section->va);
    if (offset >= stored.size()) {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped offset past section size\n";
      }
      return std::string();
    }

    enum class SeedReg : unsigned {
      RAX = 0,
      RCX = 1,
      RDX = 2,
      RBX = 3,
      RSP = 4,
      RBP = 5,
      RSI = 6,
      RDI = 7,
      R8 = 8,
      R9 = 9,
      R10 = 10,
      R11 = 11,
      R12 = 12,
      R13 = 13,
      R14 = 14,
      R15 = 15,
      Invalid = 255,
    };

    auto regName = [&](SeedReg reg) -> llvm::StringRef {
      switch (reg) {
        case SeedReg::RAX: return "RAX";
        case SeedReg::RCX: return "RCX";
        case SeedReg::RDX: return "RDX";
        case SeedReg::RBX: return "RBX";
        case SeedReg::RSP: return "RSP";
        case SeedReg::RBP: return "RBP";
        case SeedReg::RSI: return "RSI";
        case SeedReg::RDI: return "RDI";
        case SeedReg::R8: return "R8";
        case SeedReg::R9: return "R9";
        case SeedReg::R10: return "R10";
        case SeedReg::R11: return "R11";
        case SeedReg::R12: return "R12";
        case SeedReg::R13: return "R13";
        case SeedReg::R14: return "R14";
        case SeedReg::R15: return "R15";
        default: return "";
      }
    };

    auto regFromBase = [](unsigned id) -> SeedReg {
      switch (id & 0xfu) {
        case 0: return SeedReg::RAX;
        case 1: return SeedReg::RCX;
        case 2: return SeedReg::RDX;
        case 3: return SeedReg::RBX;
        case 4: return SeedReg::RSP;
        case 5: return SeedReg::RBP;
        case 6: return SeedReg::RSI;
        case 7: return SeedReg::RDI;
        case 8: return SeedReg::R8;
        case 9: return SeedReg::R9;
        case 10: return SeedReg::R10;
        case 11: return SeedReg::R11;
        case 12: return SeedReg::R12;
        case 13: return SeedReg::R13;
        case 14: return SeedReg::R14;
        case 15: return SeedReg::R15;
        default: return SeedReg::Invalid;
      }
    };

    auto paramRegIndex = [](SeedReg reg) -> std::optional<unsigned> {
      switch (reg) {
        case SeedReg::RCX: return 0u;
        case SeedReg::RDX: return 1u;
        case SeedReg::R8: return 2u;
        case SeedReg::R9: return 3u;
        default: return std::nullopt;
      }
    };

    struct SeedExpr {
      std::string text;
    };

    auto exprConst = [](uint64_t value) {
      return SeedExpr{"const(0x" + llvm::utohexstr(value) + ")"};
    };
    auto exprParam = [](unsigned index) {
      return SeedExpr{"param(" + std::to_string(index) + ")"};
    };
    auto exprUnary = [](llvm::StringRef op, const SeedExpr &arg) {
      return SeedExpr{(op + "(" + arg.text + ")").str()};
    };
    auto exprBinary = [](llvm::StringRef op, const SeedExpr &lhs,
                         const SeedExpr &rhs) {
      return SeedExpr{(op + "(" + lhs.text + "," + rhs.text + ")").str()};
    };

    auto makeZero = [&]() { return exprConst(0); };

    auto exprEqual = [](const SeedExpr &lhs, const SeedExpr &rhs) {
      return lhs.text == rhs.text;
    };

    std::array<std::optional<SeedExpr>, 16> regs;
    regs[static_cast<unsigned>(SeedReg::RCX)] = exprParam(0);
    regs[static_cast<unsigned>(SeedReg::RDX)] = exprParam(1);
    regs[static_cast<unsigned>(SeedReg::R8)] = exprParam(2);
    regs[static_cast<unsigned>(SeedReg::R9)] = exprParam(3);

    auto getRegExpr = [&](SeedReg reg) -> std::optional<SeedExpr> {
      if (reg == SeedReg::Invalid)
        return std::nullopt;
      return regs[static_cast<unsigned>(reg)];
    };
    auto setRegExpr = [&](SeedReg reg, SeedExpr expr) {
      if (reg == SeedReg::Invalid)
        return;
      regs[static_cast<unsigned>(reg)] = std::move(expr);
    };

    auto decodeReg = [&](uint8_t reg_bits, bool high_bit) {
      return regFromBase(static_cast<unsigned>(reg_bits) +
                         (high_bit ? 8u : 0u));
    };

    auto stopOnControlFlow = [&](uint8_t opcode) {
      if (opcode == 0xE8u || opcode == 0xE9u || opcode == 0xEBu ||
          opcode == 0xC3u || opcode == 0xC2u)
        return true;
      if ((opcode & 0xF0u) == 0x70u)
        return true;
      return false;
    };

    size_t cursor = offset;
    size_t decoded = 0;
    constexpr size_t kMaxDecoded = 24;
    const size_t end = std::min(stored.size(), offset + 96u);
    auto seed_decode_ctx = arch->CreateInitialContext();
    while (cursor < end && decoded < kMaxDecoded) {
      const size_t remaining = std::min<size_t>(15u, end - cursor);
      std::string_view probe_bytes(
          reinterpret_cast<const char *>(stored.data() + cursor), remaining);
      remill::Instruction decoded_inst;
      if (!arch->DecodeInstruction(section->va + cursor, probe_bytes,
                                   decoded_inst, seed_decode_ctx) ||
          decoded_inst.NumBytes() == 0) {
        break;
      }
      const size_t inst_len =
          std::min<size_t>(decoded_inst.NumBytes(), end - cursor);
      uint8_t rex = 0;
      size_t inst_start = cursor;
      uint8_t opcode = stored[cursor];
      if ((opcode & 0xF0u) == 0x40u) {
        rex = opcode;
        ++cursor;
        if (cursor >= end)
          break;
        opcode = stored[cursor];
      }

      if (stopOnControlFlow(opcode))
        break;
      if (opcode == 0x0Fu && cursor + 1u < end &&
          ((stored[cursor + 1u] & 0xF0u) == 0x80u)) {
        break;
      }

      bool handled = false;

      if (opcode >= 0x50u && opcode <= 0x5Fu) {
        cursor = inst_start + inst_len;
        handled = true;
      } else if ((opcode == 0x89u || opcode == 0x8Bu || opcode == 0x03u ||
                  opcode == 0x33u || opcode == 0x85u) &&
                 cursor + 1u < end) {
        uint8_t modrm = stored[cursor + 1u];
        if (((modrm >> 6u) & 0x3u) == 0x3u) {
          auto dst =
              decodeReg(static_cast<uint8_t>((modrm >> 3u) & 0x7u),
                        (rex & 0x4u) != 0);
          auto src =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          if (opcode == 0x8Bu) {
            if (auto src_expr = getRegExpr(src)) {
              if (rex & 0x8u) {
                setRegExpr(dst, *src_expr);
              } else {
                setRegExpr(dst, exprUnary("zext32", *src_expr));
              }
            }
            handled = true;
          } else if (opcode == 0x89u) {
            if (auto src_expr = getRegExpr(dst)) {
              if (rex & 0x8u) {
                setRegExpr(src, *src_expr);
              } else {
                setRegExpr(src, exprUnary("zext32", *src_expr));
              }
            }
            handled = true;
          } else if (opcode == 0x03u && (rex & 0x8u)) {
            if (auto dst_expr = getRegExpr(dst)) {
              if (auto src_expr = getRegExpr(src)) {
                setRegExpr(dst, exprBinary("add64", *dst_expr, *src_expr));
              }
            }
            handled = true;
          } else if (opcode == 0x33u) {
            if (auto dst_expr = getRegExpr(dst)) {
              if (auto src_expr = getRegExpr(src)) {
                if (exprEqual(*dst_expr, *src_expr)) {
                  setRegExpr(dst, makeZero());
                } else if (rex & 0x8u) {
                  setRegExpr(dst, exprBinary("xor64", *dst_expr, *src_expr));
                } else {
                  setRegExpr(dst, exprBinary("xor32", *dst_expr, *src_expr));
                }
              }
            }
            handled = true;
          } else if (opcode == 0x85u) {
            handled = true;
          }
          if (handled)
            cursor = inst_start + inst_len;
        } else if (opcode == 0x89u || opcode == 0x85u) {
          // Ignore register spills / tests against stack slots in the prologue.
          cursor = inst_start + inst_len;
          handled = true;
        } else if (opcode == 0x8Bu) {
          // Ignore memory loads that feed stack-cookie / local-frame setup.
          // They are not stable public-root seeds, but they should not stop us
          // from seeing the real hidden live-ins that follow.
          auto dst =
              decodeReg(static_cast<uint8_t>((modrm >> 3u) & 0x7u),
                        (rex & 0x4u) != 0);
          setRegExpr(dst, exprConst(0));
          cursor = inst_start + inst_len;
          handled = true;
        }
      } else if (opcode >= 0xB8u && opcode <= 0xBFu && (rex & 0x8u) &&
                 cursor + 8u < end) {
        auto dst = decodeReg(static_cast<uint8_t>(opcode - 0xB8u),
                             (rex & 0x1u) != 0);
        uint64_t imm = 0;
        std::memcpy(&imm, stored.data() + cursor + 1u, sizeof(imm));
        setRegExpr(dst, exprConst(imm));
        cursor = inst_start + inst_len;
        handled = true;
      } else if (opcode == 0x8Du && cursor + 1u < end) {
        uint8_t modrm = stored[cursor + 1u];
        auto dst = decodeReg(static_cast<uint8_t>((modrm >> 3u) & 0x7u),
                             (rex & 0x4u) != 0);
        uint8_t mod = static_cast<uint8_t>((modrm >> 6u) & 0x3u);
        uint8_t rm = static_cast<uint8_t>(modrm & 0x7u);
        std::optional<SeedExpr> expr;

        if (mod == 0 && rm == 5u && cursor + 5u < end) {
          int32_t disp = 0;
          std::memcpy(&disp, stored.data() + cursor + 2u, sizeof(disp));
          uint64_t target = section->va + inst_start + inst_len +
                            static_cast<int64_t>(disp);
          expr = exprConst(target);
        } else if (rm == 4u && cursor + 2u < end) {
          uint8_t sib = stored[cursor + 2u];
          auto base = decodeReg(static_cast<uint8_t>(sib & 0x7u),
                                (rex & 0x1u) != 0);
          auto index = decodeReg(static_cast<uint8_t>((sib >> 3u) & 0x7u),
                                 (rex & 0x2u) != 0);
          if (auto base_expr = getRegExpr(base)) {
            expr = *base_expr;
            if (((sib >> 3u) & 0x7u) != 4u) {
              if (auto index_expr = getRegExpr(index))
                expr = exprBinary("add64", *expr, *index_expr);
            }
            if (mod == 1u && cursor + 3u < end) {
              int8_t disp = static_cast<int8_t>(stored[cursor + 3u]);
              expr = exprBinary("add64", *expr,
                                exprConst(static_cast<uint64_t>(
                                    static_cast<int64_t>(disp))));
            } else if (mod == 2u && cursor + 6u < end) {
              int32_t disp = 0;
              std::memcpy(&disp, stored.data() + cursor + 3u, sizeof(disp));
              expr = exprBinary("add64", *expr,
                                exprConst(static_cast<uint64_t>(
                                    static_cast<int64_t>(disp))));
            }
          }
        }

        if (expr) {
          setRegExpr(dst, *expr);
          handled = true;
        } else if (mod == 0u || mod == 1u || mod == 2u) {
          // Ignore LEA forms we don't currently model instead of bailing out.
          handled = true;
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0x83u && cursor + 2u < end) {
        uint8_t modrm = stored[cursor + 1u];
        uint8_t imm = stored[cursor + 2u];
        if (((modrm >> 6u) & 0x3u) == 0x3u) {
          auto dst =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
          if (subop == 0x0u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst, exprBinary("add64", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x4u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst,
                         exprBinary("and32", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x5u || subop == 0x7u) {
            handled = true;
          }
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0x81u && cursor + 5u < end) {
        uint8_t modrm = stored[cursor + 1u];
        if (((modrm >> 6u) & 0x3u) == 0x3u) {
          auto dst =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
          uint32_t imm = 0;
          std::memcpy(&imm, stored.data() + cursor + 2u, sizeof(imm));
          if (subop == 0x0u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst, exprBinary("add64", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x4u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst, exprBinary("and32", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x5u || subop == 0x7u) {
            handled = true;
          }
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0xC1u && cursor + 2u < end) {
        uint8_t modrm = stored[cursor + 1u];
        uint8_t imm = stored[cursor + 2u];
        if (((modrm >> 6u) & 0x3u) == 0x3u && (rex & 0x8u)) {
          auto dst =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
          if (auto dst_expr = getRegExpr(dst)) {
            if (subop == 0x0u) {
              setRegExpr(dst,
                         exprBinary("rol64", *dst_expr, exprConst(imm)));
              handled = true;
            } else if (subop == 0x1u) {
              setRegExpr(dst,
                         exprBinary("ror64", *dst_expr, exprConst(imm)));
              handled = true;
            }
          }
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0x0Fu && cursor + 1u < end &&
                 stored[cursor + 1u] == 0x1Fu) {
        cursor = inst_start + inst_len;
        handled = true;
      }

      if (!handled)
        break;

      ++decoded;
      if (cursor <= inst_start)
        break;
    }

    const unsigned public_param_count =
        scanExportDirectCallsiteWin64ParamCount(root_va);
    llvm::SmallVector<std::string, 8> seeds;
    for (unsigned i = 0; i < regs.size(); ++i) {
      auto reg = regFromBase(i);
      auto expr = regs[i];
      if (!expr || reg == SeedReg::Invalid)
        continue;
      auto param_index = paramRegIndex(reg);
      if (param_index && *param_index < public_param_count)
        continue;
      if (param_index && expr->text == exprParam(*param_index).text)
        continue;
      seeds.push_back((regName(reg) + "=" + expr->text).str());
    }
    auto joined = llvm::join(seeds, ";");
    if (debug_public_root_seeds) {
      errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
             << " public_param_count=" << public_param_count
             << " decoded=" << decoded
             << " seeds=" << joined << "\n";
    }
    return joined;
  };
  auto annotateExportEntryHiddenSeedHint = [&](uint64_t root_va,
                                               uint64_t tagged_root_va) {
    auto seed_exprs = scanExportEntryHiddenSeedExprs(root_va);
    if (seed_exprs.empty())
      return;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      if (omill::extractEntryVA(F.getName()) != tagged_root_va)
        continue;
      F.addFnAttr("omill.export_entry_seed_exprs", seed_exprs);
    }
  };
  if (!batch_vas.empty()) {
    for (uint64_t va : batch_vas) {
      annotateExportCallsiteWin64ParamHint(va, va);
      annotateExportEntryHiddenSeedHint(va, va);
    }
  } else if (func_va != 0) {
    annotateExportCallsiteWin64ParamHint(requested_func_va, func_va);
    annotateExportEntryHiddenSeedHint(func_va, func_va);
  }
  const uint64_t largest_executable_section_size = [&]() -> uint64_t {
    if (RawBinary)
      return raw_code.size();
    uint64_t max_size = 0;
    for (const auto &cs : pe.code_sections) {
      if (cs.storage_index < pe.section_storage.size())
        max_size = std::max<uint64_t>(max_size,
                                      pe.section_storage[cs.storage_index].size());
    }
    return max_size;
  }();
  const uint64_t executable_section_count =
      RawBinary ? 1ull : static_cast<uint64_t>(pe.code_sections.size());
  const uint64_t requested_root_rva =
      (!RawBinary && requested_func_va >= pe.image_base)
          ? (requested_func_va - pe.image_base)
          : 0;
  auto foldRecursiveDeclarationAliases = [&]() {
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto fname = F.getName();
      if (!fname.starts_with("sub_"))
        continue;
      size_t dot = fname.rfind('.');
      if (dot == StringRef::npos || dot + 1 >= fname.size())
        continue;
      auto suffix = fname.drop_front(dot + 1);
      unsigned clone_index = 0;
      if (suffix.getAsInteger(10, clone_index))
        continue;
      std::string base_name = fname.take_front(dot).str();
      if (auto *base = module->getFunction(base_name)) {
        if (!base->isDeclaration()) {
          F.replaceAllUsesWith(base);
          F.eraseFromParent();
          errs() << "Folded recursive declaration alias " << fname
                 << " -> " << base_name << "\n";
        }
      }
    }
  };
  foldRecursiveDeclarationAliases();

  omill::DevirtualizationRequest devirtualization_request;
  devirtualization_request.output_mode =
      NoABI ? omill::DevirtualizationOutputMode::kNoABI
            : omill::DevirtualizationOutputMode::kABI;
  devirtualization_request.deobfuscate = Deobfuscate;
  devirtualization_request.verify_rewrites =
      VerifyGenericStaticDevirtualization;
  devirtualization_request.force_devirtualize = force_devirtualize;
  devirtualization_request.auto_detect = true;
  devirtualization_request.deprecated_block_lift = BlockLift;
  devirtualization_request.deprecated_generic_static =
      GenericStaticDevirtualize;
  devirtualization_request.deprecated_vm_entry_mode = vm_mode;
  if (!batch_vas.empty()) {
    devirtualization_request.root_vas.assign(batch_vas.begin(), batch_vas.end());
  } else if (func_va != 0) {
    devirtualization_request.root_vas.push_back(func_va);
  }

  omill::DevirtualizationPolicy devirtualization_policy;
  omill::DevirtualizationOrchestrator devirtualization_orchestrator(
      devirtualization_policy, iterative_session);
  omill::DevirtualizationRuntime devirtualization_runtime(
      devirtualization_orchestrator);
  auto emit_latest_devirtualization_epoch = [&](llvm::StringRef message) {
    const auto &epochs = devirtualization_orchestrator.session().epochs;
    if (epochs.empty())
      return;
    const auto &epoch = epochs.back();
    events.emitInfo(
        "devirtualization_epoch", message.str(),
        {{"epoch", omill::toString(epoch.epoch)},
         {"changed", epoch.changed},
         {"clean", epoch.clean},
         {"units_lifted", static_cast<int64_t>(epoch.units_lifted)},
         {"units_reused", static_cast<int64_t>(epoch.units_reused)},
         {"unresolved_complete",
          static_cast<int64_t>(epoch.unresolved_exits_complete)},
         {"unresolved_incomplete",
          static_cast<int64_t>(epoch.unresolved_exits_incomplete)},
         {"unresolved_invalidated",
          static_cast<int64_t>(epoch.unresolved_exits_invalidated)},
         {"normalization_failures",
          static_cast<int64_t>(epoch.normalization_failures)},
         {"dispatches_materialized",
          static_cast<int64_t>(epoch.dispatches_materialized)},
         {"leaked_runtime_artifacts",
          static_cast<int64_t>(epoch.leaked_runtime_artifacts)}});
  };
  devirtualization_orchestrator.recordEpoch(
      omill::DevirtualizationEpoch::kInitialLiftNormalization, *module,
      devirtualization_request.output_mode, /*changed=*/true,
      "initial lift complete");
  emit_latest_devirtualization_epoch("initial lift complete");
  auto devirtualization_plan =
      devirtualization_orchestrator.buildExecutionPlan(*module,
                                                       devirtualization_request);
  devirtualization_orchestrator.recordEpoch(
      omill::DevirtualizationEpoch::kDetectionSeedExtraction, *module,
      devirtualization_request.output_mode, /*changed=*/false,
      "devirtualization detection complete");
  emit_latest_devirtualization_epoch("devirtualization detection complete");
  devirtualization_orchestrator.recordEpoch(
      omill::DevirtualizationEpoch::kFrontierScheduling, *module,
      devirtualization_request.output_mode,
      !devirtualization_orchestrator.session().discovered_frontier_pcs.empty(),
      "frontier scheduling complete");
  emit_latest_devirtualization_epoch("frontier scheduling complete");
  events.emitInfo("devirtualization_detection_completed",
                  "devirtualization detection complete",
                  {{"should_devirtualize",
                    devirtualization_plan.enable_devirtualization},
                   {"confidence",
                    omill::toString(
                        devirtualization_plan.detection.confidence)},
                   {"unresolved_dispatches",
                    static_cast<int64_t>(
                        devirtualization_plan.detection.unresolved_dispatches)},
                   {"protected_boundaries",
                    static_cast<int64_t>(
                        devirtualization_plan.detection.protected_boundaries)},
                   {"reasons",
                    static_cast<int64_t>(
                        devirtualization_plan.detection.reasons.size())}});
  if (devirtualization_plan.enable_devirtualization) {
    events.emitInfo("devirtualization_plan_selected",
                    "devirtualization plan selected",
                    {{"use_block_lift",
                      use_block_lift_mode ||
                          devirtualization_plan.use_block_lift},
                     {"use_generic_static",
                      devirtualization_plan
                          .use_generic_static_devirtualization},
                     {"disable_legacy_vm_path",
                      devirtualization_plan.disable_legacy_vm_path}});
  }

  omill::PipelineOptions opts;
  opts.target_arch = target_arch;
  opts.target_os = target_os_str;
  opts.recover_abi = false;
  opts.deobfuscate = Deobfuscate;
  opts.resolve_indirect_targets = ResolveTargets;
  opts.max_resolution_iterations = MaxIterations;
  opts.interprocedural_const_prop = IPCP;
  opts.use_block_lifting = use_block_lift_mode;
  opts.vm_devirtualize = vm_mode;
  opts.generic_static_devirtualize =
      force_devirtualize || GenericStaticDevirtualize ||
      parseBoolEnv("OMILL_GENERIC_STATIC_DEVIRT").value_or(false);
  opts.verify_generic_static_devirtualization =
      VerifyGenericStaticDevirtualization ||
      parseBoolEnv("OMILL_VERIFY_GENERIC_STATIC_DEVIRT").value_or(false);
  devirtualization_orchestrator.applyExecutionPlan(devirtualization_plan, opts);
  if (vm_mode && !opts.vm_devirtualize &&
      devirtualization_plan.enable_devirtualization) {
    events.emitInfo("legacy_vm_mode_suppressed",
                    "legacy VM mode suppressed by devirtualization plan",
                    {{"forced", force_devirtualize}});
  }
  const bool generic_static_devirtualize_requested =
      opts.generic_static_devirtualize;
  const bool force_generic_static_devirtualize =
      parseBoolEnv("OMILL_FORCE_GENERIC_STATIC_DEVIRT").value_or(false);
  const bool known_unstable_large_default_export_root =
      requested_root_is_export &&
      largest_executable_section_size >= (1ull << 20) &&
      (requested_root_rva == 0x2400 || requested_root_rva == 0x23F0);
  const bool export_root_has_hidden_entry_seed_exprs =
      batch_vas.empty() && func_va != 0 &&
      !scanExportEntryHiddenSeedExprs(func_va).empty();
  const bool fast_plain_export_root_fallback =
      opts.generic_static_devirtualize &&
      omill::shouldUseFastPlainExportRootFallback(
          opts.vm_devirtualize, requested_root_is_export, opts.use_block_lifting,
          generic_static_devirtualize_requested,
          force_generic_static_devirtualize,
          largest_executable_section_size, executable_section_count) &&
      !export_root_has_hidden_entry_seed_exprs;
  const bool stable_no_gsd_export_root_fallback =
      opts.generic_static_devirtualize &&
      omill::shouldUseStableNoGsdExportRootFallback(
          opts.vm_devirtualize, requested_root_is_export,
          opts.use_block_lifting,
          generic_static_devirtualize_requested,
          force_generic_static_devirtualize,
          largest_executable_section_size) &&
      known_unstable_large_default_export_root;
  if (fast_plain_export_root_fallback) {
    opts.generic_static_devirtualize = false;
    opts.verify_generic_static_devirtualization = false;
    errs() << "Generic static devirtualization skipped: using fast "
              "non-GSD path for a small plain export root\n";
    events.emitInfo("generic_static_devirtualization_skipped",
                    "generic static devirtualization skipped",
                    {{"reason", "fast_plain_export_root_fallback"}});
  }
  if (!fast_plain_export_root_fallback && stable_no_gsd_export_root_fallback) {
    opts.generic_static_devirtualize = false;
    opts.verify_generic_static_devirtualization = false;
    errs() << "Generic static devirtualization skipped: using stable "
              "non-GSD export-root path for a large export root\n";
    events.emitInfo("generic_static_devirtualization_skipped",
                    "generic static devirtualization skipped",
                    {{"reason", "stable_large_export_root_fallback"}});
  }
  const bool root_local_generic_static_devirtualization_shape =
      omill::moduleHasRootLocalGenericStaticDevirtualizationShape(*module);
  if (!fast_plain_export_root_fallback &&
      !stable_no_gsd_export_root_fallback && opts.generic_static_devirtualize &&
      omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
          *module, opts.vm_devirtualize, requested_root_is_export,
          force_generic_static_devirtualize,
          root_local_generic_static_devirtualization_shape)) {
    opts.generic_static_devirtualize = false;
    opts.verify_generic_static_devirtualization = false;
    errs() << "Generic static devirtualization skipped: no VM-like candidates\n";
    events.emitInfo("generic_static_devirtualization_skipped",
                    "generic static devirtualization skipped",
                    {{"reason", "no_vm_like_candidates"}});
  }
  const bool auto_skip_always_inline_for_internal_root =
      omill::shouldAutoSkipAlwaysInlineForRoot(
          opts.vm_devirtualize, requested_root_is_export,
          generic_static_devirtualize_requested,
          opts.generic_static_devirtualize,
          root_local_generic_static_devirtualization_shape);
  std::unique_ptr<ScopedEnvOverride> auto_skip_always_inline_guard;
  if (auto_skip_always_inline_for_internal_root ||
      stable_no_gsd_export_root_fallback) {
    auto_skip_always_inline_guard =
        std::make_unique<ScopedEnvOverride>("OMILL_SKIP_ALWAYS_INLINE", "1");
    errs() << "Always-inliner suppressed after selecting a stable non-GSD "
              "root path\n";
    events.emitInfo("always_inliner_auto_suppressed",
                    "always-inliner suppressed after selecting stable root path",
                    {{"reason", stable_no_gsd_export_root_fallback
                                    ? "stable_large_export_root_fallback"
                                    : "no_root_local_devirt_shape"}});
  }
  const bool use_pre_abi_noabi_cleanup =
      !NoABI && opts.generic_static_devirtualize;
  opts.no_abi_mode = NoABI || use_pre_abi_noabi_cleanup;
  if (!DumpVirtualModel.empty())
    setEnvIfUnset("OMILL_DUMP_VIRTUAL_MODEL", DumpVirtualModel.c_str());
  if (auto v = parseBoolEnv("OMILL_SKIP_BLOCK_MERGE"); v.value_or(false)) {
    opts.merge_block_functions_after_fixpoint = false;
  }
  const bool preserve_lift_infrastructure = ResolveTargets && !NoABI;
  opts.preserve_lifted_semantics = preserve_lift_infrastructure;
  if (opts.generic_static_devirtualize) {
    errs() << "Generic static devirtualization enabled\n";
    events.emitInfo("generic_static_devirtualization_enabled",
                    "generic static devirtualization enabled",
                    {{"verify", opts.verify_generic_static_devirtualization}});
  }

  auto fixLiftedFunctionNamingCollisions = [&]() {
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto name = F.getName();
      if (!name.starts_with("sub_"))
        continue;
      for (int i = 1; i <= 20; ++i) {
        std::string def_name = (name + "." + llvm::Twine(i)).str();
        if (auto *def = module->getFunction(def_name)) {
          if (!def->isDeclaration()) {
            F.replaceAllUsesWith(def);
            F.eraseFromParent();
            def->setName(name);
            break;
          }
        }
      }
    }
  };

  auto tagNewlyLiftedFunctions =
      [&](llvm::StringRef attr_name,
          const llvm::DenseSet<llvm::Function *> &pre_lift_funcs) {
        for (auto &F : *module) {
          if (!pre_lift_funcs.count(&F) && !F.isDeclaration())
            F.addFnAttr(attr_name, "1");
        }
      };

  auto clearLiftRoundAttr = [&](llvm::StringRef attr_name) {
    for (auto &F : *module) {
      if (F.getFnAttribute(attr_name).isValid())
        F.removeFnAttr(attr_name);
    }
  };

  auto hasOpenOutputRootHazards = [&]() {
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            return true;

          auto name = callee->getName();
          if (omill::isDispatchIntrinsicName(name))
            return true;
          if (name.starts_with("blk_") && callee->isDeclaration())
            return true;
          if (name.starts_with("sub_") && !name.ends_with("_native") &&
              callee->isDeclaration())
            return true;
        }
      }
    }
    return false;
  };

  auto moduleHasStructuralOutputFrontierArtifacts = [&]() {
    if (devirtualization_plan.enable_devirtualization &&
        devirtualization_orchestrator.hasBlockingUnstableFrontierState(
            *module)) {
      return true;
    }

    auto has_live_uses = [&](llvm::StringRef name) {
      if (auto *F = module->getFunction(name))
        return !F->use_empty();
      return false;
    };

    if (has_live_uses("__omill_missing_block_handler")) {
      return true;
    }

    for (auto &F : *module) {
      if (F.isDeclaration() &&
          (F.getName().starts_with("blk_") ||
           F.getName().starts_with("block_"))) {
        return true;
      }
    }

    return hasOpenOutputRootHazards();
  };

  auto countDefinedOutputRoots = [&]() {
    unsigned count = 0;
    for (auto &F : *module) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        ++count;
    }
    return count;
  };

  auto pruneToDefinedOutputRootClosure = [&]() {
    auto isCodeAddressForPrune = [&](uint64_t target) {
      if (RawBinary)
        return target >= BaseAddress &&
               target < BaseAddress + raw_code.size();
      for (auto &sec : pe.code_sections) {
        if (target >= sec.va && target < sec.va + sec.size)
          return true;
      }
      return false;
    };
    auto lookupDefinedLiftedOrBlockTarget =
        [&](uint64_t target) -> llvm::Function * {
      for (llvm::StringRef prefix : {"blk_", "block_", "sub_"}) {
        std::string name = (prefix + llvm::utohexstr(target)).str();
        if (auto *fn = module->getFunction(name); fn && !fn->isDeclaration())
          return fn;
      }
      return nullptr;
    };

    llvm::SmallVector<llvm::Function *, 16> roots;
    for (auto &F : *module) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        roots.push_back(&F);
    }
    if (roots.empty())
      return;

    llvm::SmallVector<llvm::Function *, 32> worklist(roots.begin(), roots.end());
    auto patchable_targets = omill::collectOutputRootClosureTargets(
        *module,
        [&](uint64_t target) { return isCodeAddressForPrune(target); },
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(target) != nullptr;
        },
        [&](uint64_t target) { return target; },
        /*include_defined_targets=*/true);
    auto enqueuePatchableTargets = [&](const std::vector<uint64_t> &targets) {
      for (uint64_t target : targets) {
        if (auto *target_fn = lookupDefinedLiftedOrBlockTarget(target))
          worklist.push_back(target_fn);
      }
    };
    enqueuePatchableTargets(patchable_targets.constant_code_targets);
    enqueuePatchableTargets(patchable_targets.constant_calli_targets);
    enqueuePatchableTargets(patchable_targets.constant_dispatch_targets);
    enqueuePatchableTargets(
        patchable_targets.annotated_vm_continuation_targets);

    llvm::DenseSet<llvm::Function *> reachable;
    while (!worklist.empty()) {
      llvm::Function *F = worklist.pop_back_val();
      if (!F || F->isDeclaration() || !reachable.insert(F).second)
        continue;
      for (auto &BB : *F) {
        for (auto &I : BB) {
          for (llvm::Value *operand : I.operands()) {
            auto *callee = llvm::dyn_cast<llvm::Function>(operand);
            if (!callee || callee->isDeclaration())
              continue;
            worklist.push_back(callee);
          }
        }
      }
    }

    auto isPrunableLiftedOrDeadHelper = [&](llvm::Function &F) {
      if (reachable.count(&F))
        return false;
      if (F.hasFnAttribute("omill.output_root"))
        return false;
      if (F.getName().starts_with("__omill_compact_recursive_source_oracle"))
        return false;
      return F.getName().starts_with("blk_") || F.getName().starts_with("block_") ||
             F.getName().starts_with("sub_") ||
             F.getName().starts_with("vm_entry_") ||
             omill::isDispatchIntrinsicName(F.getName());
    };

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!isPrunableLiftedOrDeadHelper(F))
        continue;
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
    }

    {
      llvm::ModulePassManager DeadMPM;
      DeadMPM.addPass(llvm::GlobalDCEPass());
      DeadMPM.run(*module, MAM);
    }

    llvm::SmallVector<llvm::Function *, 32> dead_decls;
    for (auto &F : *module) {
      if (!F.isDeclaration() || !F.use_empty())
        continue;
      if (F.getName().starts_with("blk_") || F.getName().starts_with("block_") ||
          F.getName().starts_with("sub_") ||
          F.getName().starts_with("vm_entry_") ||
          omill::isDispatchIntrinsicName(F.getName())) {
        dead_decls.push_back(&F);
      }
    }
    for (llvm::Function *F : dead_decls)
      F->eraseFromParent();
  };

  std::function<void()> rerunLateNativeArgRepair = []() {};
  auto canonicalizeTerminalMissingBlockDispatchSuffixes = [&]() -> bool {
    if (!opts.no_abi_mode)
      return false;

    auto *trap = llvm::Intrinsic::getOrInsertDeclaration(
        module.get(), llvm::Intrinsic::trap);
    llvm::SmallVector<llvm::CallInst *, 8> terminal_calls;
    for (auto &F : *module) {
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

          bool saw_terminal_dispatch = false;
          bool conflict = false;
          for (llvm::Instruction *next = call->getNextNonDebugInstruction();
               next; next = next->getNextNonDebugInstruction()) {
            if (llvm::isa<llvm::ReturnInst>(next))
              break;
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
            if (next->isTerminator() && !llvm::isa<llvm::ReturnInst>(next)) {
              conflict = true;
              break;
            }
          }

          if (!conflict && saw_terminal_dispatch)
            terminal_calls.push_back(call);
        }
      }
    }

    bool changed = false;
    for (auto *call : terminal_calls) {
      auto *BB = call->getParent();
      llvm::IRBuilder<> ir(call);
      ir.CreateCall(trap);
      auto *new_term = ir.CreateUnreachable();
      while (&BB->back() != new_term) {
        auto &dead = BB->back();
        if (!dead.use_empty() && !dead.getType()->isVoidTy()) {
          dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
        }
        dead.eraseFromParent();
      }
      changed = true;
    }

    return changed;
  };
  auto runFinalOutputCleanup = [&]() {
    if (parseBoolEnv("OMILL_SKIP_OUTPUT_FINAL_CLEANUP").value_or(false))
      return;
    if (devirtualization_plan.enable_devirtualization)
      devirtualization_orchestrator.refreshSessionState(*module);
    if (canonicalizeTerminalMissingBlockDispatchSuffixes())
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    if (moduleHasStructuralOutputFrontierArtifacts())
      return;
    {
      llvm::ModulePassManager LateMPM;
      omill::buildLateCleanupPipeline(LateMPM, opts);
      LateMPM.run(*module, MAM);
    }
    llvm::PassBuilder PB;
    llvm::ModulePassManager MPM =
        PB.buildPerModuleDefaultPipeline(llvm::OptimizationLevel::O2);
    MPM.run(*module, MAM);
    if (canonicalizeTerminalMissingBlockDispatchSuffixes())
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    rerunLateNativeArgRepair();
    if (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr) {
      std::error_code ec;
      llvm::raw_fd_ostream os("after_final_output_cleanup.ll", ec,
                              llvm::sys::fs::OF_Text);
      if (!ec)
        module->print(os, nullptr);
    }
  };
  std::function<void()> rerunFocusedNativeHelperControlFlowRecovery = []() {};
  [[maybe_unused]] auto rewriteLocalNativeJumpTableDispatches = [&]() {
    auto parseNativeTargetPC = [&](llvm::StringRef name) -> uint64_t {
      if (uint64_t pc = omill::extractEntryVA(name); pc != 0)
        return pc;
      auto parsePrefixedHex = [&](llvm::StringRef prefix) -> uint64_t {
        if (!name.starts_with(prefix))
          return 0;
        auto rest = name.drop_front(prefix.size());
        size_t hex_len = 0;
        while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
          ++hex_len;
        if (hex_len == 0)
          return 0;
        uint64_t pc = 0;
        if (rest.substr(0, hex_len).getAsInteger(16, pc))
          return 0;
        return pc;
      };
      if (uint64_t pc = parsePrefixedHex("blk_"); pc != 0)
        return pc;
      if (uint64_t pc = parsePrefixedHex("block_"); pc != 0)
        return pc;
      return 0;
    };

    llvm::DenseMap<uint64_t, llvm::Function *> local_native_targets;
    llvm::SmallDenseSet<uint64_t, 16> local_case_pcs;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      if (uint64_t pc = parseNativeTargetPC(F.getName()); pc != 0)
        local_native_targets[pc] = &F;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *SI = llvm::dyn_cast<llvm::SwitchInst>(&I);
          if (!SI || !SI->getCondition()->getType()->isIntegerTy(64))
            continue;
          for (auto &Case : SI->cases())
            local_case_pcs.insert(Case.getCaseValue()->getZExtValue());
        }
      }
    }

    auto findStateOffsetPtr = [&](llvm::Function &F, uint64_t offset)
        -> llvm::Value * {
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
          if (!GEP || GEP->getNumOperands() < 2)
            continue;
          auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
          if (!idx || idx->getZExtValue() != offset)
            continue;
          return GEP;
        }
      }
      return nullptr;
    };

    unsigned rewrite_count = 0;
    unsigned void_rewrite_count = 0;
    const bool debug_public_root_seeds =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      auto *RetST = llvm::dyn_cast<llvm::StructType>(F.getReturnType());
      if (!RetST || RetST->getNumElements() != 8) {
        if (debug_public_root_seeds && F.getName() == "blk_18000227d_native")
          errs() << "[abi-post] local-jt skip ret-shape " << F.getName()
                 << "\n";
        continue;
      }

      llvm::CallBase *dispatch_call = nullptr;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Callee = CB ? CB->getCalledFunction() : nullptr;
          if (!Callee)
            continue;
          auto Name = Callee->getName();
          if (omill::isDispatchJumpName(Name)) {
            dispatch_call = CB;
            break;
          }
        }
        if (dispatch_call)
          break;
      }
      if (!dispatch_call) {
        if (debug_public_root_seeds && F.getName() == "blk_18000227d_native")
          errs() << "[abi-post] local-jt skip no-dispatch " << F.getName()
                 << "\n";
        continue;
      }

      auto *target_pc = dispatch_call->getArgOperand(1);
      auto *eax_ptr = findStateOffsetPtr(F, 2216);
      auto *arg2232_ptr = findStateOffsetPtr(F, 2232);
      auto *arg2280_ptr = findStateOffsetPtr(F, 2280);
      auto *arg2296_ptr = findStateOffsetPtr(F, 2296);
      auto *arg2328_ptr = findStateOffsetPtr(F, 2328);
      auto *arg2408_ptr = findStateOffsetPtr(F, 2408);
      auto *arg2440_ptr = findStateOffsetPtr(F, 2440);
      auto *arg2456_ptr = findStateOffsetPtr(F, 2456);
      if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
          !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
        if (debug_public_root_seeds && F.getName() == "blk_18000227d_native") {
          errs() << "[abi-post] local-jt skip ptrs " << F.getName()
                 << " eax=" << (eax_ptr != nullptr)
                 << " 2232=" << (arg2232_ptr != nullptr)
                 << " 2280=" << (arg2280_ptr != nullptr)
                 << " 2296=" << (arg2296_ptr != nullptr)
                 << " 2328=" << (arg2328_ptr != nullptr)
                 << " 2408=" << (arg2408_ptr != nullptr)
                 << " 2440=" << (arg2440_ptr != nullptr)
                 << " 2456=" << (arg2456_ptr != nullptr) << "\n";
        }
        continue;
      }

      auto *dispatch_block = dispatch_call->getParent();
      auto *load_block = dispatch_block->splitBasicBlock(
          std::next(dispatch_call->getIterator()), "resolved.dispatch.loads");
      auto *switch_block = dispatch_block->splitBasicBlock(
          dispatch_call->getIterator(), "resolved.dispatch.switch");
      switch_block->getTerminator()->eraseFromParent();

      llvm::IRBuilder<> Builder(switch_block);
      auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                           "tb.state2232");
      auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                           "tb.state2280");
      auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                           "tb.state2328");
      auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                           "tb.state2440");

      auto *switch_inst =
          Builder.CreateSwitch(target_pc, dispatch_block, local_case_pcs.size());

      for (uint64_t case_pc : local_case_pcs) {
        if (case_pc == 0)
          continue;

        if (auto it = local_native_targets.find(case_pc);
            it != local_native_targets.end()) {
          auto *CaseRetST =
              llvm::dyn_cast<llvm::StructType>(it->second->getReturnType());
          if (!CaseRetST || CaseRetST->getNumElements() != 8)
            continue;
          auto *case_block = llvm::BasicBlock::Create(
              ctx, "resolved.case." + llvm::utohexstr(case_pc), &F, load_block);
          llvm::IRBuilder<> case_builder(case_block);
          auto *case_call = case_builder.CreateCall(
              it->second->getFunctionType(), it->second,
              {state2232, state2280, state2328, state2440});
          case_call->setCallingConv(it->second->getCallingConv());
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {0}), eax_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {1}), arg2232_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {2}), arg2328_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {3}), arg2296_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {4}), arg2280_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {5}), arg2408_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {6}), arg2440_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {7}), arg2456_ptr);
          case_builder.CreateBr(load_block);
          switch_inst->addCase(case_builder.getInt64(case_pc), case_block);
        } else {
          auto *loop_block = llvm::BasicBlock::Create(
              ctx, "resolved.selfloop." + llvm::utohexstr(case_pc), &F,
              load_block);
          llvm::IRBuilder<> loop_builder(loop_block);
          loop_builder.CreateBr(loop_block);
          switch_inst->addCase(loop_builder.getInt64(case_pc), loop_block);
        }
      }

      ++rewrite_count;
      if (debug_public_root_seeds && F.getName() == "blk_18000227d_native")
        errs() << "[abi-post] local-jt rewrote " << F.getName() << "\n";
    }

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native") ||
          !F.getReturnType()->isVoidTy()) {
        continue;
      }

      bool already_rewritten = false;
      for (auto &BB : F) {
        auto BBName = BB.getName();
        if (BBName.starts_with("resolved.dispatch") ||
            BBName.starts_with("resolved.case.") ||
            BBName.starts_with("resolved.selfloop.")) {
          already_rewritten = true;
          break;
        }
      }
      if (already_rewritten)
        continue;

      llvm::CallBase *dispatch_call = nullptr;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Callee = CB ? CB->getCalledFunction() : nullptr;
          if (!Callee)
            continue;
          auto Name = Callee->getName();
          if (omill::isDispatchJumpName(Name)) {
            dispatch_call = CB;
            break;
          }
        }
        if (dispatch_call)
          break;
      }
      if (!dispatch_call)
        continue;

      auto *eax_ptr = findStateOffsetPtr(F, 2216);
      auto *arg2232_ptr = findStateOffsetPtr(F, 2232);
      auto *arg2280_ptr = findStateOffsetPtr(F, 2280);
      auto *arg2296_ptr = findStateOffsetPtr(F, 2296);
      auto *arg2328_ptr = findStateOffsetPtr(F, 2328);
      auto *arg2408_ptr = findStateOffsetPtr(F, 2408);
      auto *arg2440_ptr = findStateOffsetPtr(F, 2440);
      auto *arg2456_ptr = findStateOffsetPtr(F, 2456);
      if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
          !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
        continue;
      }

      auto *switch_block = dispatch_call->getParent();
      auto *after_block =
          switch_block->splitBasicBlock(dispatch_call->getIterator(),
                                       "resolved.dispatch.dynamic");
      switch_block->getTerminator()->eraseFromParent();

      llvm::IRBuilder<> Builder(switch_block);
      auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                           "tb.state2232");
      auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                           "tb.state2280");
      auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                           "tb.state2328");
      auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                           "tb.state2440");
      auto *switch_inst = Builder.CreateSwitch(dispatch_call->getArgOperand(1),
                                               after_block,
                                               local_case_pcs.size());

      for (uint64_t case_pc : local_case_pcs) {
        if (case_pc == 0)
          continue;

        if (auto it = local_native_targets.find(case_pc);
            it != local_native_targets.end()) {
          auto *CaseRetST =
              llvm::dyn_cast<llvm::StructType>(it->second->getReturnType());
          if (!CaseRetST || CaseRetST->getNumElements() != 8)
            continue;
          auto *case_block = llvm::BasicBlock::Create(
              ctx, "resolved.case." + llvm::utohexstr(case_pc), &F,
              after_block);
          llvm::IRBuilder<> case_builder(case_block);
          auto *case_call = case_builder.CreateCall(
              it->second->getFunctionType(), it->second,
              {state2232, state2280, state2328, state2440});
          case_call->setCallingConv(it->second->getCallingConv());
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {0}), eax_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {1}), arg2232_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {2}), arg2328_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {3}), arg2296_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {4}), arg2280_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {5}), arg2408_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {6}), arg2440_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {7}), arg2456_ptr);
          case_builder.CreateBr(after_block);
          switch_inst->addCase(case_builder.getInt64(case_pc), case_block);
        }
      }

      ++void_rewrite_count;
    }

    if ((rewrite_count > 0 || void_rewrite_count > 0) && debug_public_root_seeds) {
      errs() << "[abi-post] local-native-jumptable-rewrite count="
             << rewrite_count << " void_count=" << void_rewrite_count << "\n";
    }
  };

  auto liftedNameFor = [&](uint64_t pc, bool native) {
    std::string name = "sub_" + llvm::Twine::utohexstr(pc).str();
    if (native)
      name += "_native";
    return name;
  };

  auto blockNameFor = [&](uint64_t pc, bool native) {
    std::string name = "blk_" + llvm::Twine::utohexstr(pc).str();
    if (native)
      name += "_native";
    return name;
  };

  auto findLiftedOrBlockFunction = [&](uint64_t pc, bool native)
      -> llvm::Function * {
    if (auto *fn = module->getFunction(liftedNameFor(pc, native)))
      return fn;
    return module->getFunction(blockNameFor(pc, native));
  };

  auto nearbyLiftedEntrySearchWindow = [&]() -> uint64_t {
    switch (target_arch) {
      case omill::TargetArch::kAArch64:
        return 4;
      case omill::TargetArch::kX86_64:
      default:
        return 128;
    }
  };

  auto extractLiftedOrBlockEntryPC =
      [&](llvm::StringRef name, bool native) -> std::optional<uint64_t> {
    if (native) {
      if (!name.ends_with("_native"))
        return std::nullopt;
      name = name.drop_back(strlen("_native"));
    } else if (name.ends_with("_native")) {
      return std::nullopt;
    }

    if (uint64_t pc = omill::extractEntryVA(name); pc != 0)
      return pc;

    if (name.starts_with("blk_"))
      name = name.drop_front(4);
    else if (name.starts_with("block_"))
      name = name.drop_front(6);
    else
      return std::nullopt;

    size_t hex_len = 0;
    while (hex_len < name.size() && llvm::isHexDigit(name[hex_len]))
      ++hex_len;
    if (hex_len == 0)
      return std::nullopt;

    uint64_t pc = 0;
    if (name.substr(0, hex_len).getAsInteger(16, pc) || pc == 0)
      return std::nullopt;
    return pc;
  };

  auto findNearestDefinedLiftedOrBlockFunction =
      [&](uint64_t target_pc, bool native,
          uint64_t *resolved_pc = nullptr) -> llvm::Function * {
    if (!target_pc)
      return nullptr;

    const uint64_t window = nearbyLiftedEntrySearchWindow();
    llvm::Function *best = nullptr;
    uint64_t best_pc = 0;
    uint64_t best_distance = std::numeric_limits<uint64_t>::max();

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      auto entry_pc = extractLiftedOrBlockEntryPC(F.getName(), native);
      if (!entry_pc)
        continue;

      const uint64_t distance = (*entry_pc > target_pc)
                                    ? (*entry_pc - target_pc)
                                    : (target_pc - *entry_pc);
      if (distance == 0 || distance > window)
        continue;

      if (!best || distance < best_distance ||
          (distance == best_distance && *entry_pc < best_pc)) {
        best = &F;
        best_pc = *entry_pc;
        best_distance = distance;
      }
    }

    if (best && resolved_pc)
      *resolved_pc = best_pc;
    return best;
  };

  auto findExactOrNearbyLiftedOrBlockFunction =
      [&](uint64_t target_pc, bool native,
          uint64_t *resolved_pc = nullptr) -> llvm::Function * {
    if (auto *exact = findLiftedOrBlockFunction(target_pc, native)) {
      if (!exact->isDeclaration()) {
        if (resolved_pc)
          *resolved_pc = target_pc;
        return exact;
      }
    }
    return findNearestDefinedLiftedOrBlockFunction(target_pc, native,
                                                   resolved_pc);
  };

  auto collectConstantCodeCallTargets =
      [&](llvm::function_ref<bool(const llvm::Function &)> include_function) {
        llvm::DenseSet<uint64_t> targets;
        for (auto &F : *module) {
          if (!include_function(F))
            continue;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->getCalledFunction())
                continue;
              auto *callee_op = call->getCalledOperand();
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
                continue;
              uint64_t target = ci->getZExtValue();
              if (target == 0)
                continue;

              bool in_code = false;
              if (RawBinary) {
                in_code = (target >= BaseAddress &&
                           target < BaseAddress + raw_code.size());
              } else {
                for (auto &sec : pe.code_sections) {
                  if (target >= sec.va && target < sec.va + sec.size) {
                    in_code = true;
                    break;
                  }
                }
              }
              if (!in_code)
                continue;

              targets.insert(target);
            }
          }
        }
        return targets;
      };

  auto isCodeAddressInCurrentInput = [&](uint64_t target) {
    if (target == 0)
      return false;
    if (RawBinary) {
      return target >= BaseAddress && target < BaseAddress + raw_code.size();
    }
    for (auto &sec : pe.code_sections) {
      if (target >= sec.va && target < sec.va + sec.size)
        return true;
    }
    return false;
  };

  auto hasDefinedLiftedOrBlockTarget = [&](uint64_t target) {
    auto *lifted = omill::findLiftedOrCoveredFunctionByPC(*module, target);
    if (lifted && !lifted->isDeclaration())
      return true;
    if (!NoABI) {
      if (auto *modeled =
              omill::findStructuralCodeTargetFunctionByPC(*module, target);
          modeled && modeled->isDeclaration() &&
          (modeled->hasFnAttribute("omill.native_direct_target_pc") ||
           modeled->hasFnAttribute("omill.native_boundary_pc") ||
           modeled->hasFnAttribute("omill.vm_enter_target_pc") ||
           modeled->hasFnAttribute("omill.executable_target_pc"))) {
        return true;
      }
    }
    return false;
  };

  auto findDefinedStructuralCodeTargetFunction =
      [&](uint64_t pc) -> llvm::Function * {
        if (!pc)
          return nullptr;
        for (auto &F : *module) {
          if (F.isDeclaration())
            continue;
          if (omill::extractStructuralCodeTargetPC(F) == pc)
            return &F;
        }
        return nullptr;
      };

  auto findPreferredDefinedCodeTargetFunction =
      [&](uint64_t pc, bool native = false) -> llvm::Function * {
        if (auto *target_fn = findLiftedOrBlockFunction(pc, native);
            target_fn && !target_fn->isDeclaration()) {
          return target_fn;
        }
        if (!native) {
          if (auto *structural = findDefinedStructuralCodeTargetFunction(pc)) {
            return structural;
          }
        }
        return nullptr;
      };

  auto patchConstantIntToPtrCallsToNative =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched_local_target = 0;
        unsigned patched_boundary = 0;

        auto maybeGetConstantCodeTarget =
            [&](llvm::CallBase &call) -> std::optional<uint64_t> {
          if (call.getCalledFunction())
            return std::nullopt;

          auto *callee_op = call.getCalledOperand();
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

        auto rewriteCallTarget = [&](llvm::CallBase &call, llvm::Value *callee) {
          auto *old_callee = call.getCalledOperand();
          call.setCalledOperand(callee);
          if (auto *inst = llvm::dyn_cast<llvm::Instruction>(old_callee)) {
            if (inst->use_empty())
              inst->eraseFromParent();
          }
        };

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call)
                continue;

              auto pc = maybeGetConstantCodeTarget(*call);
              if (!pc || !target_set.contains(*pc) || *pc == 0)
                continue;

              if (auto *target_fn =
                      findPreferredDefinedCodeTargetFunction(*pc)) {
                rewriteCallTarget(*call, target_fn);
                ++patched_local_target;
                continue;
              }

              if (RawBinary)
                continue;

              auto boundary =
                  omill::classifyProtectedBoundary(pe.memory_map, *pc);
              if (!boundary)
                continue;

              auto callee =
                  omill::getOrInsertProtectedBoundaryDecl(*module,
                                                          call->getFunctionType(),
                                                          *boundary);
              rewriteCallTarget(*call, callee.getCallee());
              ++patched_boundary;
            }
          }
        }

        const unsigned patched = patched_local_target + patched_boundary;
        if (patched > 0) {
          errs() << "Patched " << patched
                 << " inttoptr call sites to direct calls";
          if (patched_boundary > 0)
            errs() << " (" << patched_local_target << " local, "
                   << patched_boundary << " protected-boundary)";
          errs() << "\n";
          if (events.detailed()) {
            events.emitInfo(event_name, event_message,
                            {{"patched_uses", static_cast<int64_t>(patched)},
                             {"patched_local_targets",
                              static_cast<int64_t>(patched_local_target)},
                             {"patched_boundaries",
                              static_cast<int64_t>(patched_boundary)}});
          }
          runPostPatchCleanup(event_name);
        }
        return patched;
      };

  auto collectConstantCalliTargets =
      [&](llvm::function_ref<bool(const llvm::Function &)> include_function) {
        llvm::DenseSet<uint64_t> targets;
        for (auto &F : *module) {
          if (!include_function(F))
            continue;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call || call->arg_size() < 3)
                continue;
              auto *callee = llvm::dyn_cast<llvm::Function>(
                  call->getCalledOperand()->stripPointerCasts());
              if (!callee || !callee->getName().contains("CALLI"))
                continue;
              auto *ci =
                  llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2));
              if (!ci)
                continue;
              const uint64_t target = ci->getZExtValue();
              if (!isCodeAddressInCurrentInput(target))
                continue;
              targets.insert(target);
            }
          }
        }
        return targets;
      };

  auto patchConstantCalliTargetsToDirectCalls =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched_local_target = 0;
        unsigned patched_boundary = 0;

        auto maybeGetConstantCalliTarget =
            [&](llvm::CallBase &call) -> std::optional<uint64_t> {
          if (call.arg_size() < 3)
            return std::nullopt;
          auto *callee = llvm::dyn_cast<llvm::Function>(
              call.getCalledOperand()->stripPointerCasts());
          if (!callee || !callee->getName().contains("CALLI"))
            return std::nullopt;
          auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call.getArgOperand(2));
          if (!ci)
            return std::nullopt;
          return ci->getZExtValue();
        };

        auto rewriteCalliToDirectCall = [&](llvm::CallBase &call,
                                           llvm::FunctionType *callee_ty,
                                           llvm::Value *callee) {
          llvm::IRBuilder<> Builder(&call);
          llvm::SmallVector<llvm::Value *, 3> args = {
              call.getArgOperand(1), call.getArgOperand(2),
              call.getArgOperand(0)};
          auto *new_call =
              Builder.CreateCall(callee_ty, callee, args, call.getName());
          new_call->setCallingConv(call.getCallingConv());
          if (auto *old_call = llvm::dyn_cast<llvm::CallInst>(&call))
            new_call->setTailCallKind(old_call->getTailCallKind());
          new_call->setDebugLoc(call.getDebugLoc());
          if (!call.use_empty()) {
            if (call.getType() == new_call->getType()) {
              call.replaceAllUsesWith(new_call);
            } else if (!call.getType()->isVoidTy()) {
              call.replaceAllUsesWith(
                  llvm::PoisonValue::get(call.getType()));
            }
          }
          call.eraseFromParent();
        };

        auto lifted_fn_ty = llvm::FunctionType::get(
            llvm::PointerType::getUnqual(ctx),
            {llvm::PointerType::getUnqual(ctx), llvm::Type::getInt64Ty(ctx),
             llvm::PointerType::getUnqual(ctx)},
            false);

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call)
                continue;

              auto pc = maybeGetConstantCalliTarget(*call);
              if (!pc || !target_set.contains(*pc) || *pc == 0)
                continue;

              if (auto *target_fn =
                      findPreferredDefinedCodeTargetFunction(*pc)) {
                rewriteCalliToDirectCall(*call, target_fn->getFunctionType(),
                                         target_fn);
                ++patched_local_target;
                continue;
              }

              if (RawBinary)
                continue;

              auto boundary =
                  omill::classifyProtectedBoundary(pe.memory_map, *pc);
              if (!boundary)
                continue;

              auto callee = omill::getOrInsertProtectedBoundaryDecl(
                  *module, lifted_fn_ty, *boundary);
              rewriteCalliToDirectCall(*call, lifted_fn_ty, callee.getCallee());
              ++patched_boundary;
            }
          }
        }

        const unsigned patched = patched_local_target + patched_boundary;
        if (patched > 0) {
          errs() << "Patched " << patched
                 << " constant CALLI site(s) to direct calls";
          if (patched_local_target > 0)
            errs() << " (local=" << patched_local_target << ")";
          if (patched_boundary > 0)
            errs() << " (boundary=" << patched_boundary << ")";
          errs() << "\n";
          if (events.detailed()) {
            events.emitInfo(
                event_name, event_message,
                {{"patched_calls", static_cast<int64_t>(patched)},
                 {"patched_local_targets",
                  static_cast<int64_t>(patched_local_target)},
                 {"patched_boundaries",
                  static_cast<int64_t>(patched_boundary)}});
          }
        }
        return patched;
      };

  auto patchConstantDispatchTargetsToDirectCalls =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched_local_target = 0;
        unsigned patched_boundary = 0;

        auto lifted_fn_ty = llvm::FunctionType::get(
            llvm::PointerType::getUnqual(ctx),
            {llvm::PointerType::getUnqual(ctx), llvm::Type::getInt64Ty(ctx),
             llvm::PointerType::getUnqual(ctx)},
            false);

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->arg_size() < 3)
                continue;
              auto *callee = call->getCalledFunction();
              if (!callee || !omill::isDispatchIntrinsicName(callee->getName()))
                continue;
              auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
              if (!ci)
                continue;
              const uint64_t target = ci->getZExtValue();
              if (!target_set.contains(target) || target == 0)
                continue;

              llvm::Value *direct_callee = nullptr;
              llvm::FunctionType *direct_ty = nullptr;
              if (auto *target_fn =
                      findPreferredDefinedCodeTargetFunction(target)) {
                direct_callee = target_fn;
                direct_ty = target_fn->getFunctionType();
                ++patched_local_target;
              } else if (!RawBinary) {
                auto boundary =
                    omill::classifyProtectedBoundary(pe.memory_map, target);
                if (!boundary)
                  continue;
                auto boundary_callee = omill::getOrInsertProtectedBoundaryDecl(
                    *module, lifted_fn_ty, *boundary);
                direct_callee = boundary_callee.getCallee();
                direct_ty = lifted_fn_ty;
                ++patched_boundary;
              } else {
                continue;
              }

              llvm::IRBuilder<> Builder(call);
              auto *new_call = Builder.CreateCall(
                  direct_ty, direct_callee,
                  {call->getArgOperand(0), call->getArgOperand(1),
                   call->getArgOperand(2)},
                  call->getName());
              new_call->setCallingConv(call->getCallingConv());
              new_call->setDebugLoc(call->getDebugLoc());
              if (!call->use_empty()) {
                if (call->getType() == new_call->getType()) {
                  call->replaceAllUsesWith(new_call);
                } else if (!call->getType()->isVoidTy()) {
                  call->replaceAllUsesWith(
                      llvm::PoisonValue::get(call->getType()));
                }
              }
              call->eraseFromParent();
            }
          }
        }

        const unsigned patched = patched_local_target + patched_boundary;
        if (patched > 0) {
          errs() << "Patched " << patched
                 << " constant dispatch site(s) to direct calls";
          if (patched_local_target > 0)
            errs() << " (local=" << patched_local_target << ")";
          if (patched_boundary > 0)
            errs() << " (boundary=" << patched_boundary << ")";
          errs() << "\n";
          if (events.detailed()) {
            events.emitInfo(
                event_name, event_message,
                {{"patched_calls", static_cast<int64_t>(patched)},
                 {"patched_local_targets",
                  static_cast<int64_t>(patched_local_target)},
                 {"patched_boundaries",
                  static_cast<int64_t>(patched_boundary)}});
          }
        }
        return patched;
      };

  auto patchDeclaredLiftedOrBlockCallsToDefinedTargets =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched = 0;

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call)
                continue;
              auto *callee = call->getCalledFunction();
              if (!callee || !callee->isDeclaration())
                continue;
              const uint64_t target_pc =
                  omill::extractStructuralCodeTargetPC(*callee);
              if (target_pc == 0 || !target_set.contains(target_pc))
                continue;
              auto *target_fn =
                  findPreferredDefinedCodeTargetFunction(target_pc);
              if (!target_fn || target_fn->isDeclaration() ||
                  target_fn == callee ||
                  target_fn->getFunctionType() != call->getFunctionType()) {
                continue;
              }
              call->setCalledFunction(target_fn);
              ++patched;
            }
          }
        }

        if (patched > 0) {
          errs() << "Patched " << patched
                 << " declared lifted/block call site(s) to defined targets\n";
          if (events.detailed()) {
            events.emitInfo(event_name, event_message,
                            {{"patched_calls", static_cast<int64_t>(patched)}});
          }
        }
        return patched;
      };

  auto collectDeclaredStructuralTargetsWithDefinedImplementations = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (auto &F : *module) {
      if (!F.isDeclaration())
        continue;
      const uint64_t target_pc = omill::extractStructuralCodeTargetPC(F);
      if (!target_pc)
        continue;
      auto *defined = findPreferredDefinedCodeTargetFunction(target_pc);
      if (!defined || defined->isDeclaration() || defined == &F)
        continue;
      targets.insert(target_pc);
    }
    return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
  };

  auto collectExecutablePlaceholderDeclarationTargets = [&]() {
    llvm::SmallVector<uint64_t, 16> targets;
    llvm::DenseSet<uint64_t> seen;
    for (auto &F : *module) {
      if (!F.isDeclaration())
        continue;
      auto fact = omill::readExecutableTargetFact(F);
      if (!fact)
        continue;
      if (fact->kind != omill::ExecutableTargetKind::kExecutablePlaceholder &&
          fact->kind != omill::ExecutableTargetKind::kInvalidatedExecutableEntry) {
        continue;
      }
      const uint64_t target_pc = fact->raw_target_pc;
      if (!target_pc || !isCodeAddressInCurrentInput(target_pc))
        continue;
      if (!seen.insert(target_pc).second)
        continue;
      targets.push_back(target_pc);
    }
    return targets;
  };

  auto rerunLateDiscoveryPipeline = [&](llvm::StringRef attr_name, bool run_abi,
                                        bool skip_missing_block_lift,
                                        bool clear_attr = true,
                                        bool include_closed_slice_context =
                                            true) {
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    llvm::DenseSet<llvm::Function *> pre_rerun_funcs;
    llvm::DenseSet<llvm::Function *> pre_rerun_defs;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);
    for (auto &F : *module) {
      pre_rerun_funcs.insert(&F);
      if (!F.isDeclaration())
        pre_rerun_defs.insert(&F);
    }

    omill::PipelineOptions late_opts = opts;
    late_opts.resolve_indirect_targets = false;
    late_opts.skip_closed_slice_missing_block_lift = skip_missing_block_lift;
    if (skip_missing_block_lift) {
      // The late missing-block wave already lifts a fixed target set. Avoid
      // re-entering the global block-discovery epoch here; it adds a large
      // amount of work and can chase unrelated continuations before the
      // explicit bounded continuation round below runs.
      late_opts.use_block_lifting = false;
      late_opts.merge_block_functions_after_fixpoint = false;
    }
    const bool use_closed_slice_context =
        include_closed_slice_context && !run_abi &&
        opts.generic_static_devirtualize && opts.use_block_lifting;
    late_opts.scope_predicate =
        [attr_name = attr_name.str(), use_closed_slice_context](
            llvm::Function &F) {
          if (F.getFnAttribute(attr_name).isValid())
            return true;
          return use_closed_slice_context &&
                 F.hasFnAttribute("omill.closed_root_slice");
        };
    late_opts.preserve_lifted_semantics = preserve_lift_infrastructure;

    auto runScopedLatePipeline = [&](const omill::PipelineOptions &rerun_opts,
                                     llvm::StringRef stage_name) {
      const bool debug_late_output_target_rerun =
          parseBoolEnv("OMILL_DEBUG_LATE_OUTPUT_ROOT_TARGET_RERUN")
              .value_or(false);
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] scoped-main-start stage="
               << stage_name << "\n";
      ModulePassManager MPM;
      omill::buildPipeline(MPM, rerun_opts);
      MPM.run(*module, MAM);
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] scoped-main-done stage="
               << stage_name << "\n";
      emitIterativeSessionEvents(events, iterative_session, stage_name);
      if (run_abi) {
        if (debug_late_output_target_rerun)
          errs() << "[late-output-target] scoped-abi-start stage="
                 << stage_name << "\n";
        ModulePassManager MPM;
        omill::buildABIRecoveryPipeline(MPM, rerun_opts);
        MPM.run(*module, MAM);
        if (debug_late_output_target_rerun)
          errs() << "[late-output-target] scoped-abi-done stage="
                 << stage_name << "\n";
      }
    };

    runScopedLatePipeline(late_opts, "late-discovery-rerun");

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      const bool is_new_function = !pre_rerun_funcs.count(&F);
      const bool became_defined = !is_new_function && !pre_rerun_defs.count(&F);
      if (!is_new_function && !became_defined)
        continue;
      F.addFnAttr(attr_name, "1");
      F.addFnAttr("omill.closed_root_slice", "1");
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
      if (debug_continuation_lifts) {
        errs() << "[late-rerun-new-fn] attr=" << attr_name
               << " fn=" << F.getName()
               << " existing_decl=" << (became_defined ? 1 : 0) << "\n";
      }
    }

    if (clear_attr)
      clearLiftRoundAttr(attr_name);
  };

  auto isInCode = [&](uint64_t target) {
    if (RawBinary)
      return target >= BaseAddress && target < BaseAddress + raw_code.size();
    for (auto &sec : pe.code_sections) {
      if (target >= sec.va && target < sec.va + sec.size)
        return true;
    }
    return false;
  };

  auto readCodeBytes = [&](uint64_t pc, uint8_t *buf, size_t size) {
    if (RawBinary) {
      if (pc < BaseAddress || pc >= BaseAddress + raw_code.size())
        return false;
      const auto offset = static_cast<size_t>(pc - BaseAddress);
      if (offset + size > raw_code.size())
        return false;
      std::memcpy(buf, raw_code.data() + offset, size);
      return true;
    }
    return pe.memory_map.read(pc, buf, size);
  };

  auto looksLikeLateMissingBlockRoot = [&](uint64_t pc) {
    __try {
      if (!isInCode(pc))
        return false;

      constexpr unsigned kMaxProbeInstructions = 12;
      uint64_t current_pc = pc;
      for (unsigned i = 0; i < kMaxProbeInstructions; ++i) {
        uint8_t probe_buf[15] = {};
        if (!readCodeBytes(current_pc, probe_buf, sizeof(probe_buf)))
          return false;

        std::string_view probe_bytes(
            reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
        remill::Instruction probe_inst;
        if (!arch->DecodeInstruction(current_pc, probe_bytes, probe_inst,
                                     arch->CreateInitialContext())) {
          return false;
        }

        switch (probe_inst.category) {
          case remill::Instruction::kCategoryInvalid:
          case remill::Instruction::kCategoryError:
          case remill::Instruction::kCategoryDirectFunctionCall:
          case remill::Instruction::kCategoryIndirectFunctionCall:
          case remill::Instruction::kCategoryConditionalDirectFunctionCall:
          case remill::Instruction::kCategoryConditionalIndirectFunctionCall:
            return false;

          case remill::Instruction::kCategoryDirectJump:
          case remill::Instruction::kCategoryIndirectJump:
          case remill::Instruction::kCategoryConditionalBranch:
          case remill::Instruction::kCategoryConditionalIndirectJump:
          case remill::Instruction::kCategoryFunctionReturn:
          case remill::Instruction::kCategoryConditionalFunctionReturn:
          case remill::Instruction::kCategoryAsyncHyperCall:
          case remill::Instruction::kCategoryConditionalAsyncHyperCall:
            return true;

          case remill::Instruction::kCategoryNormal:
          case remill::Instruction::kCategoryNoOp:
            current_pc = probe_inst.next_pc;
            break;
        }
      }

      return false;
    } __except (1) {
      return false;
    }
  };

  auto collectContinuationTargetsForScope =
      [&](llvm::function_ref<bool(const llvm::Function &)> include_fn) {
    llvm::DenseSet<uint64_t> targets;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);
    const bool debug_markers_enabled =
        std::getenv("OMILL_DEBUG_MARKER_FILE") != nullptr;

    auto parseContinuationPC =
        [&](llvm::StringRef name) -> std::optional<uint64_t> {
      if (name.starts_with("blk_")) {
        uint64_t pc = 0;
        if (!name.drop_front(4).getAsInteger(16, pc))
          return pc;
        return std::nullopt;
      }
      if (name.starts_with("block_")) {
        uint64_t pc = 0;
        if (!name.drop_front(6).getAsInteger(16, pc))
          return pc;
      }
      return std::nullopt;
    };

    for (auto &F : *module) {
      if (F.isDeclaration() || !include_fn(F))
        continue;
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:continuation_scan_fn:") +
                           F.getName())
                              .str()
                              .c_str());
      }
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || !callee->isDeclaration())
            continue;
          auto maybe_pc = parseContinuationPC(callee->getName());
          if (!maybe_pc)
            continue;
          if (debug_markers_enabled) {
            appendDebugMarker((llvm::Twine("late:continuation_candidate:") +
                               F.getName() + "->" + callee->getName() +
                               "@0x" + llvm::Twine::utohexstr(*maybe_pc))
                                  .str()
                                  .c_str());
          }
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg || pc_arg->getZExtValue() != *maybe_pc)
            continue;
          if (debug_markers_enabled) {
            appendDebugMarker((llvm::Twine("late:continuation_before_probe:0x") +
                               llvm::Twine::utohexstr(*maybe_pc))
                                  .str()
                                  .c_str());
          }
          const bool accepted = looksLikeLateMissingBlockRoot(*maybe_pc);
          if (debug_markers_enabled) {
            appendDebugMarker((llvm::Twine("late:continuation_after_probe:0x") +
                               llvm::Twine::utohexstr(*maybe_pc) + "=" +
                               llvm::Twine(accepted ? 1 : 0))
                                  .str()
                                  .c_str());
          }
          if (debug_continuation_lifts) {
            errs() << "[late-continuation-candidate] pc=0x"
                   << llvm::Twine::utohexstr(*maybe_pc)
                   << " caller=" << F.getName()
                   << " accepted=" << (accepted ? 1 : 0) << "\n";
          }
          if (!accepted)
            continue;
          targets.insert(*maybe_pc);
        }
      }
    }

    return targets;
  };

  auto collectClosedSliceContinuationTargets = [&]() {
    return collectContinuationTargetsForScope([](const llvm::Function &F) {
      return F.hasFnAttribute("omill.closed_root_slice");
    });
  };

  auto collectClosedSliceMissingBlockTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.closed_root_slice"))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg)
            continue;
          const uint64_t pc = pc_arg->getZExtValue();
          const bool looks_like_root =
              pc != 0 && looksLikeLateMissingBlockRoot(pc);
          if (debug_continuation_lifts) {
            errs() << "[late-missing-candidate] pc=0x"
                   << llvm::Twine::utohexstr(pc)
                   << " caller=" << F.getName()
                   << " accepted=" << (looks_like_root ? 1 : 0) << "\n";
          }
          if (!looks_like_root)
            continue;
          targets.insert(pc);
        }
      }
    }

    return targets;
  };

  auto collectOutputRootMissingBlockTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice_root"))
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg)
            continue;
          const uint64_t pc = pc_arg->getZExtValue();
          const bool looks_like_root =
              pc != 0 && looksLikeLateMissingBlockRoot(pc);
          const auto *existing = findLiftedOrBlockFunction(pc, /*native=*/false);
          if (debug_continuation_lifts) {
            errs() << "[late-output-boundary-candidate] pc=0x"
                   << llvm::Twine::utohexstr(pc)
                   << " caller=" << F.getName()
                   << " accepted=" << (looks_like_root ? 1 : 0)
                   << " existing=" << (existing && !existing->isDeclaration())
                   << "\n";
          }
          if (!looks_like_root)
            continue;
          if (existing && !existing->isDeclaration())
            continue;
          targets.insert(pc);
        }
      }
    }

    return targets;
  };

  auto collectAllConstantMissingBlockTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg || pc_arg->isZero())
            continue;
          targets.insert(pc_arg->getZExtValue());
        }
      }
    }
    return targets;
  };

  auto liftScopedTargets = [&](llvm::ArrayRef<uint64_t> targets,
                               llvm::StringRef attr_name, bool run_abi,
                               bool skip_missing_block_lift,
                               bool clear_attr = true,
                               bool mark_closed_root_slice = true,
                               bool use_direct_lifter = false,
                               bool include_closed_slice_context = true,
                               bool rerun_discovery = true) {
    const bool debug_markers_enabled =
        std::getenv("OMILL_DEBUG_MARKER_FILE") != nullptr;
    auto block_cb = iterative_session->blockLiftCallback();
    if (!use_direct_lifter && !block_cb)
      return false;

    llvm::DenseSet<llvm::Function *> pre_lift_funcs;
    for (auto &F : *module)
      pre_lift_funcs.insert(&F);

    unsigned lifted_any = 0;
    for (uint64_t pc : targets) {
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:before:0x") +
                           llvm::Twine::utohexstr(pc) + ":direct=" +
                           llvm::Twine(use_direct_lifter ? 1 : 0))
                              .str()
                              .c_str());
      }
      auto *existing = findLiftedOrBlockFunction(pc, /*native=*/false);
      if (existing && !existing->isDeclaration())
        continue;

      iterative_session->queueTarget(pc);
      bool lifted = false;
      const bool prefer_direct_lifter_for_structural_block_decl =
          !use_direct_lifter && existing && existing->isDeclaration() &&
          (existing->getName().starts_with("blk_") ||
           existing->getName().starts_with("block_"));
      if (use_direct_lifter || prefer_direct_lifter_for_structural_block_decl) {
        lifted = safeTraceLiftTarget(pc);
      } else if (block_cb(pc)) {
        lifted = true;
      }
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:after:0x") +
                           llvm::Twine::utohexstr(pc) + "=" +
                           llvm::Twine(lifted ? 1 : 0))
                              .str()
                              .c_str());
      }
      if (lifted)
        ++lifted_any;
    }

    if (!lifted_any)
      return false;

    fixLiftedFunctionNamingCollisions();
    tagNewlyLiftedFunctions(attr_name, pre_lift_funcs);
    for (auto &F : *module) {
      if (!F.getFnAttribute(attr_name).isValid())
        continue;
      if (mark_closed_root_slice)
        F.addFnAttr("omill.closed_root_slice", "1");
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
    }
    if (rerun_discovery) {
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:before_rerun:") +
                           attr_name)
                              .str()
                              .c_str());
      }
      rerunLateDiscoveryPipeline(attr_name, run_abi, skip_missing_block_lift,
                                 clear_attr, include_closed_slice_context);
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:after_rerun:") +
                           attr_name)
                              .str()
                              .c_str());
      }
    } else if (clear_attr) {
      clearLiftRoundAttr(attr_name);
    }
    return true;
  };

  auto liftLateTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    return liftScopedTargets(targets, "omill.late_newly_lifted",
                             /*run_abi=*/false,
                             /*skip_missing_block_lift=*/true,
                             /*clear_attr=*/true,
                             /*mark_closed_root_slice=*/true,
                             /*use_direct_lifter=*/false,
                             /*include_closed_slice_context=*/false,
                             /*rerun_discovery=*/true);
  };

  auto liftLateMissingBlockTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    bool changed = liftScopedTargets(targets, "omill.late_newly_lifted",
                                     /*run_abi=*/false,
                                     /*skip_missing_block_lift=*/true,
                                     /*clear_attr=*/true,
                                     /*mark_closed_root_slice=*/true,
                                     /*use_direct_lifter=*/true,
                                     /*include_closed_slice_context=*/false,
                                     /*rerun_discovery=*/false);

    llvm::SmallVector<uint64_t, 8> unresolved_exact_targets;
    for (uint64_t pc : targets) {
      auto *existing = findLiftedOrBlockFunction(pc, /*native=*/false);
      if (!existing || existing->isDeclaration())
        unresolved_exact_targets.push_back(pc);
    }

    if (!unresolved_exact_targets.empty()) {
      changed |= liftScopedTargets(unresolved_exact_targets,
                                   "omill.late_newly_lifted",
                                   /*run_abi=*/false,
                                   /*skip_missing_block_lift=*/true,
                                   /*clear_attr=*/true,
                                   /*mark_closed_root_slice=*/true,
                                   /*use_direct_lifter=*/false,
                                   /*include_closed_slice_context=*/false,
                                   /*rerun_discovery=*/false);
    }

    return changed;
  };

  auto liftLateTerminalBoundaryTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    return liftScopedTargets(targets, "omill.late_boundary_target_lifted",
                             /*run_abi=*/false,
                             /*skip_missing_block_lift=*/true,
                             /*clear_attr=*/true,
                             /*mark_closed_root_slice=*/false);
  };

  auto runLateContinuationRounds = [&](unsigned max_rounds) {
    constexpr unsigned kMaxTargetsPerRound = 8;

    for (unsigned round = 0; round < max_rounds; ++round) {
      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":before_collect")
              .str()
              .c_str());
      auto targets = collectClosedSliceContinuationTargets();
      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":after_collect targets=" + llvm::Twine(targets.size()))
              .str()
              .c_str());
      if (targets.empty())
        break;

      llvm::SmallVector<uint64_t, 16> ordered_targets(targets.begin(),
                                                      targets.end());
      llvm::sort(ordered_targets);
      if (ordered_targets.size() > kMaxTargetsPerRound)
        ordered_targets.resize(kMaxTargetsPerRound);

      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":before_lift targets=" + llvm::Twine(ordered_targets.size()))
              .str()
              .c_str());
      if (!liftLateTargets(ordered_targets))
        break;
      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":after_lift")
              .str()
              .c_str());
    }
  };

  auto hasClosedSlicePendingOpaqueEdges = [&]() {
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.closed_root_slice"))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          auto name = callee->getName();
          if (omill::isDispatchIntrinsicName(name)) {
            return true;
          }
          if ((name.starts_with("blk_") || name.starts_with("block_")) &&
              callee->isDeclaration()) {
            return true;
          }
        }
      }
    }
    return false;
  };

  auto rerunLateContinuationPipeline = [&]() {
    if (devirtualization_plan.enable_devirtualization)
      return;
    if (!opts.generic_static_devirtualize || !opts.use_block_lifting ||
        parseBoolEnv("OMILL_SKIP_LATE_CONTINUATION_RERUN").value_or(false)) {
      return;
    }

    // Keep the no-ABI late continuation wave opt-in. The current generic path
    // already closes the corpus roots without it, and reopening the graph here
    // can destabilize large samples after the slice is already semantically
    // closed. Use the env knob when explicitly experimenting on unresolved
    // cases.
    if (NoABI &&
        !parseBoolEnv("OMILL_ENABLE_NOABI_LATE_CONTINUATION_RERUN")
             .value_or(false)) {
      return;
    }

    runLateContinuationRounds(/*max_rounds=*/NoABI ? 1u : 3u);
    appendDebugMarker("late:after_continuation_rounds");

    if (NoABI ||
        parseBoolEnv("OMILL_SKIP_LATE_MISSING_BLOCK_RERUN").value_or(false)) {
      return;
    }

    constexpr unsigned kMaxMissingTargetRounds = 3;
    constexpr unsigned kMaxMissingTargetsPerRound = 8;
    for (unsigned round = 0; round < kMaxMissingTargetRounds; ++round) {
      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":before_collect")
              .str()
              .c_str());
      auto missing_targets = collectClosedSliceMissingBlockTargets();
      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":after_collect targets=" + llvm::Twine(missing_targets.size()))
              .str()
              .c_str());
      if (missing_targets.empty())
        break;

      llvm::SmallVector<uint64_t, 8> ordered_missing_targets(
          missing_targets.begin(), missing_targets.end());
      llvm::sort(ordered_missing_targets);
      if (ordered_missing_targets.size() > kMaxMissingTargetsPerRound)
        ordered_missing_targets.resize(kMaxMissingTargetsPerRound);

      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":before_lift targets=" + llvm::Twine(ordered_missing_targets.size()))
              .str()
              .c_str());
      if (!liftLateMissingBlockTargets(ordered_missing_targets))
        break;

      llvm::DenseSet<uint64_t> target_set(ordered_missing_targets.begin(),
                                          ordered_missing_targets.end());
      unsigned patched = 0;
      unsigned patched_nearby = 0;
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
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
            if (!target_set.contains(target_pc) || target_pc == 0)
              continue;

            uint64_t resolved_target_pc = 0;
            auto *target = findExactOrNearbyLiftedOrBlockFunction(
                target_pc, /*native=*/false, &resolved_target_pc);
            if (!target || target == &F || target->isDeclaration())
              continue;
            if (target->getFunctionType() != call->getFunctionType())
              continue;

            call->setCalledFunction(target);
            ++patched;
            patched_nearby +=
                static_cast<unsigned>(resolved_target_pc != target_pc);
          }
        }
      }
      if (patched > 0 && events.detailed()) {
        events.emitInfo("late_missing_block_patch",
                        "patched late missing-block calls to lifted targets",
                        {{"round", static_cast<int64_t>(round)},
                         {"patched_uses", static_cast<int64_t>(patched)},
                         {"patched_nearby_uses",
                          static_cast<int64_t>(patched_nearby)}});
      }
      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":after_lift patched=" + llvm::Twine(patched) +
           " nearby=" + llvm::Twine(patched_nearby))
              .str()
              .c_str());
    }
    appendDebugMarker("late:after_missing_block_lift");
  };

  auto patchConstantMissingBlockCallsToLiftedTargets =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched = 0;
        unsigned patched_nearby = 0;

        for (auto &F : *module) {
          if (F.isDeclaration())
            continue;
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
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
              if (!target_set.contains(target_pc) || target_pc == 0)
                continue;

              uint64_t resolved_target_pc = 0;
              auto *target = findExactOrNearbyLiftedOrBlockFunction(
                  target_pc, /*native=*/false, &resolved_target_pc);
              if (!target || target == &F || target->isDeclaration())
                continue;
              if (target->getFunctionType() != call->getFunctionType())
                continue;

              call->setCalledFunction(target);
              ++patched;
              patched_nearby +=
                  static_cast<unsigned>(resolved_target_pc != target_pc);
            }
          }
        }

        if (patched == 0)
          return;

        errs() << "Patched " << patched
               << " __remill_missing_block call sites to lifted targets\n";
        if (events.detailed()) {
          events.emitInfo(event_name, event_message,
                          {{"patched_uses", static_cast<int64_t>(patched)},
                           {"patched_nearby_uses",
                            static_cast<int64_t>(patched_nearby)}});
        }
      };

  auto rerunLateTerminalBoundaryTargetPipeline = [&]() {
    if (NoABI || !opts.use_block_lifting)
      return;
    if (parseBoolEnv("OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN")
            .value_or(false)) {
      return;
    }

    auto targets = collectOutputRootMissingBlockTargets();
    if (targets.empty())
      return;

    constexpr unsigned kMaxTargetsPerRound = 4;
    llvm::SmallVector<uint64_t, 8> ordered_targets(targets.begin(),
                                                   targets.end());
    llvm::sort(ordered_targets);
    if (ordered_targets.size() > kMaxTargetsPerRound)
      ordered_targets.resize(kMaxTargetsPerRound);

    if (!devirtualization_plan.enable_devirtualization) {
      if (!liftLateTerminalBoundaryTargets(ordered_targets))
        return;
    }

    patchConstantMissingBlockCallsToLiftedTargets(
        ordered_targets, "late_terminal_boundary_patch",
        "patched late terminal boundary missing-block calls");
  };

  auto normalizeKnownVmContinuationTarget = [&](uint64_t target) -> uint64_t {
    if (target == 0 || !isCodeAddressInCurrentInput(target))
      return target;
    if (opts.target_arch != omill::TargetArch::kX86_64)
      return target;

    llvm::SmallDenseSet<uint64_t, 8> visited;
    uint64_t current = target;
    bool recovered_overlap_entry = false;
    if (auto canonical =
            omill::canonicalizeLiftTargetForOverlap(&pe.memory_map, current,
                                                    opts.target_arch)) {
      recovered_overlap_entry = (*canonical != current);
      current = *canonical;
    }
    for (unsigned hop = 0; hop < 4; ++hop) {
      if (!visited.insert(current).second)
        break;
      uint8_t bytes[8] = {};
      if (!pe.memory_map.read(current, bytes, sizeof(bytes)))
        break;

      uint64_t next = 0;
      if (bytes[0] == 0xE9) {
        int32_t rel = 0;
        std::memcpy(&rel, &bytes[1], sizeof(rel));
        next = static_cast<uint64_t>(static_cast<int64_t>(current) + 5 +
                                     static_cast<int64_t>(rel));
      } else if (bytes[0] == 0xEB) {
        int8_t rel = static_cast<int8_t>(bytes[1]);
        next = static_cast<uint64_t>(static_cast<int64_t>(current) + 2 +
                                     static_cast<int64_t>(rel));
      } else {
        break;
      }

      if (next == 0 || !isCodeAddressInCurrentInput(next))
        break;
      current = next;
    }

    if (current >= 5 &&
        !omill::isExactX86DirectControlFlowFallthrough(&pe.memory_map,
                                                       current)) {
      uint8_t call_bytes[5] = {};
      const uint64_t call_pc = current - 5;
      if (isCodeAddressInCurrentInput(call_pc) &&
          pe.memory_map.read(call_pc, call_bytes, sizeof(call_bytes)) &&
          call_bytes[0] == 0xE8) {
        current = call_pc;
      }
    }

    if (auto canonical =
            omill::canonicalizeLiftTargetForOverlap(&pe.memory_map, current,
                                                    opts.target_arch)) {
      recovered_overlap_entry = recovered_overlap_entry ||
                                (*canonical != current);
      current = *canonical;
    }

    if (auto covered_pc =
            omill::findNearestCoveredLiftedOrBlockPC(*module, current, 0x20)) {
      uint64_t candidate = *covered_pc;
      if (candidate > current && (candidate - current) <= 8)
        return current;
      if (recovered_overlap_entry && candidate < current &&
          (current - candidate) <= 8)
        return current;
      if (auto canonical =
              omill::canonicalizeLiftTargetForOverlap(&pe.memory_map, candidate,
                                                      opts.target_arch)) {
        return *canonical;
      }
      return candidate;
    }
    return current;
  };

  auto collectOutputRootClosureSummary = [&]() {
    return omill::collectOutputRootClosureTargets(
        *module,
        [&](uint64_t target) { return isCodeAddressInCurrentInput(target); },
        [&](uint64_t target) { return hasDefinedLiftedOrBlockTarget(target); },
        [&](uint64_t target) {
          return normalizeKnownVmContinuationTarget(target);
        });
  };

  auto collectOutputRootConstantCodeCallTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target : collectOutputRootClosureSummary().constant_code_targets)
      targets.insert(target);
    return targets;
  };

  auto collectOutputRootConstantCalliTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target :
         collectOutputRootClosureSummary().constant_calli_targets) {
      targets.insert(target);
    }
    return targets;
  };

  auto collectOutputRootConstantDispatchTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target :
         collectOutputRootClosureSummary().constant_dispatch_targets) {
      targets.insert(target);
    }
    return targets;
  };

  auto collectOutputRootAnnotatedVmContinuationTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target :
         collectOutputRootClosureSummary().annotated_vm_continuation_targets) {
      targets.insert(target);
    }
    return targets;
  };

  auto rerunLateOutputRootTargetPipeline = [&]() {
    const bool enable_late_output_target_rerun =
        parseBoolEnv("OMILL_ENABLE_LATE_OUTPUT_ROOT_TARGET_RERUN")
            .value_or(false);
    if (!opts.use_block_lifting)
      return;
    if (!enable_late_output_target_rerun) {
      return;
    }
    if (parseBoolEnv("OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN")
            .value_or(false)) {
      return;
    }
    const bool debug_late_output_target_rerun =
        parseBoolEnv("OMILL_DEBUG_LATE_OUTPUT_ROOT_TARGET_RERUN")
            .value_or(false);

    constexpr unsigned kMaxRounds = 2;
    constexpr unsigned kMaxTargetsPerRound = 2;

    for (unsigned round = 0; round < kMaxRounds; ++round) {
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " collect\n";
      auto targets = collectOutputRootConstantCodeCallTargets();
      auto calli_targets = collectOutputRootConstantCalliTargets();
      targets.insert(calli_targets.begin(), calli_targets.end());
      auto dispatch_targets = collectOutputRootConstantDispatchTargets();
      targets.insert(dispatch_targets.begin(), dispatch_targets.end());
      auto vm_targets = collectOutputRootAnnotatedVmContinuationTargets();
      targets.insert(vm_targets.begin(), vm_targets.end());
      if (debug_late_output_target_rerun) {
        errs() << "[late-output-target] round=" << (round + 1)
               << " raw-code=" << collectOutputRootConstantCodeCallTargets().size()
               << " raw-calli=" << calli_targets.size()
               << " raw-dispatch=" << dispatch_targets.size()
               << " raw-vm=" << vm_targets.size()
               << " merged=" << targets.size() << "\n";
      }
      if (targets.empty())
        break;

      llvm::SmallVector<uint64_t, 8> ordered_targets(targets.begin(),
                                                     targets.end());
      llvm::sort(ordered_targets);
      ordered_targets.erase(
          std::remove_if(ordered_targets.begin(), ordered_targets.end(),
                         [&](uint64_t pc) {
                           auto *lifted =
                               findLiftedOrBlockFunction(pc, /*native=*/false);
                           auto *native =
                               findLiftedOrBlockFunction(pc, /*native=*/true);
                           return (lifted && !lifted->isDeclaration()) ||
                                  (native && !native->isDeclaration());
                         }),
          ordered_targets.end());
      if (ordered_targets.empty())
        break;
      if (ordered_targets.size() > kMaxTargetsPerRound)
        ordered_targets.resize(kMaxTargetsPerRound);
      bool vm_only_targets = !ordered_targets.empty();
      for (uint64_t pc : ordered_targets) {
        if (!vm_targets.count(pc)) {
          vm_only_targets = false;
          break;
        }
      }
      if (debug_late_output_target_rerun) {
        errs() << "[late-output-target] round=" << (round + 1)
               << " targets=";
        for (uint64_t pc : ordered_targets)
          errs() << " 0x" << llvm::Twine::utohexstr(pc);
        errs() << " mode=" << (vm_only_targets ? "iterative-vm" : "direct")
               << "\n";
      }

      ScopedEnvOverride skip_always_inline("OMILL_SKIP_ALWAYS_INLINE", "1");
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " lift+rerun\n";
      if (!liftScopedTargets(ordered_targets, "omill.late_output_target_lifted",
                             /*run_abi=*/!vm_only_targets,
                             /*skip_missing_block_lift=*/true,
                             /*clear_attr=*/true,
                             /*mark_closed_root_slice=*/false,
                             /*use_direct_lifter=*/!vm_only_targets && !NoABI)) {
        break;
      }

      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " patch\n";
      patchConstantIntToPtrCallsToNative(
          ordered_targets, "late_output_root_target_patch",
          "patched output-root constant inttoptr calls");
      patchConstantCalliTargetsToDirectCalls(
          ordered_targets, "late_output_root_calli_patch",
          "patched output-root constant CALLI callsites");
      patchConstantDispatchTargetsToDirectCalls(
          ordered_targets, "late_output_root_dispatch_patch",
          "patched output-root constant dispatch callsites");

      // The new targets may expose another constant callsite in the root.
      // Recompute analyses before the next bounded round.
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " done\n";
    }
  };

  auto rerunFinalClosedSlicePipeline = [&]() {
    if (devirtualization_plan.enable_devirtualization)
      return;
    if (!opts.generic_static_devirtualize || !opts.use_block_lifting || !NoABI ||
        parseBoolEnv("OMILL_SKIP_FINAL_CLOSED_SLICE_RERUN").value_or(false)) {
      return;
    }
    if (!hasClosedSlicePendingOpaqueEdges())
      return;

    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    omill::PipelineOptions late_opts = opts;
    late_opts.resolve_indirect_targets = false;
    late_opts.use_block_lifting = false;
    late_opts.merge_block_functions_after_fixpoint = false;
    late_opts.skip_closed_slice_missing_block_lift = true;
    late_opts.scope_predicate = [](llvm::Function &F) {
      return F.hasFnAttribute("omill.closed_root_slice");
    };
    late_opts.preserve_lifted_semantics = preserve_lift_infrastructure;

    ModulePassManager MPM;
    omill::buildPipeline(MPM, late_opts);
    MPM.run(*module, MAM);
    emitIterativeSessionEvents(events, iterative_session,
                               "late-closed-slice-rerun");
  };

  if (opts.no_abi_mode)
    module->setModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  events.emitInfo("pipeline_started", "main pipeline started");
  {
    ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);
    MPM.run(*module, MAM);
  }
  emitIterativeSessionEvents(events, iterative_session, "main-pipeline");
  errs() << "Main pipeline complete\n";
  events.emitInfo("pipeline_completed", "main pipeline completed");
  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_MAIN_PIPELINE",
                         "after_main_pipeline.ll");
  if (devirtualization_plan.enable_devirtualization) {
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kIncrementalBlockLift, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "main pipeline completed");
    emit_latest_devirtualization_epoch("main pipeline completed");
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kNormalizationCacheAdmission, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "normalized lift-unit cache refreshed");
    emit_latest_devirtualization_epoch("normalized lift-unit cache refreshed");
    if (opts.generic_static_devirtualize) {
      devirtualization_orchestrator.recordEpoch(
          omill::DevirtualizationEpoch::kCfgMaterialization, *module,
          devirtualization_request.output_mode, /*changed=*/true,
          "generic materialization completed");
      emit_latest_devirtualization_epoch("generic materialization completed");
    }
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kContinuationClosure, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "post-pipeline cleanup completed");
    emit_latest_devirtualization_epoch("post-pipeline cleanup completed");
  }

  bool noabi_output_root_targets_patched = false;
  auto runSharedLateStep = [&](llvm::StringRef label, auto &&fn) {
    const bool debug_late_steps =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    if (debug_late_steps) {
      errs() << "[late-step] begin " << label << "\n";
    }
    if (events.detailed()) {
      events.emitInfo("late_step_started", "late step started",
                      {{"label", label.str()}});
    }
    fn();
    if (events.detailed()) {
      events.emitInfo("late_step_completed", "late step completed",
                      {{"label", label.str()}});
    }
    if (debug_late_steps) {
      errs() << "[late-step] end " << label << "\n";
    }
  };

  appendDebugMarker("late:before_continuation");
  runSharedLateStep("rerun_late_continuation_pipeline", [&] {
    rerunLateContinuationPipeline();
  });
  appendDebugMarker("late:after_continuation");
  appendDebugMarker("late:before_terminal_boundary");
  runSharedLateStep("rerun_late_terminal_boundary_target_pipeline", [&] {
    rerunLateTerminalBoundaryTargetPipeline();
  });
  appendDebugMarker("late:after_terminal_boundary");
  appendDebugMarker("late:before_final_closed_slice");
  runSharedLateStep("rerun_final_closed_slice_pipeline", [&] {
    rerunFinalClosedSlicePipeline();
  });
  appendDebugMarker("late:after_final_closed_slice");
  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_LATE_RERUNS",
                         "after_late_reruns.ll");

  auto moduleFlagEnabled = [&](llvm::StringRef flag_name) {
    auto *md = module->getModuleFlag(flag_name);
    auto *constant_md = llvm::dyn_cast_or_null<llvm::ConstantAsMetadata>(md);
    auto *constant_int =
        constant_md
            ? llvm::dyn_cast<llvm::ConstantInt>(constant_md->getValue())
            : nullptr;
    return constant_int && constant_int->isOne();
  };

  auto countInternalSyntheticBlockCalls = [&]() {
    unsigned count = 0;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->isDeclaration())
            continue;
          auto name = callee->getName();
          if (!name.starts_with("blk_") && !name.starts_with("block_"))
            continue;
          ++count;
        }
      }
    }
    return count;
  };

  auto hasLiveDispatchReference = [&]() {
    for (auto &F : *module) {
      if (omill::isDispatchIntrinsicName(F.getName()) && !F.use_empty())
        return true;
    }
    return false;
  };

  auto hasLiveFunctionWithPrefix = [&](llvm::StringRef prefix) {
    for (auto &F : *module) {
      if (F.getName().starts_with(prefix) && !F.use_empty())
        return true;
    }
    return false;
  };

  auto rerunNoAbiClosedSliceCleanupReplay = [&]() {
    if (!NoABI ||
        (std::getenv("OMILL_SKIP_NOABI_POST_MAIN_CLEANUP_REPLAY") != nullptr))
      return;
    if (!moduleFlagEnabled("omill.closed_root_slice_scope"))
      return;
    if (hasLiveDispatchReference())
      return;
    if (hasLiveFunctionWithPrefix("vm_entry_"))
      return;

    const unsigned before_block_calls = countInternalSyntheticBlockCalls();
    auto countReachableLiveRemillMemoryIntrinsics = [&]() -> unsigned {
      llvm::DenseSet<llvm::Function *> reachable;
      llvm::SmallVector<llvm::Function *, 32> worklist;

      auto enqueue = [&](llvm::Function *F) {
        if (!F || F->isDeclaration() || !reachable.insert(F).second)
          return;
        worklist.push_back(F);
      };

      for (auto &F : *module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root") &&
            !F.hasFnAttribute("omill.internal_output_root")) {
          enqueue(&F);
        }
      }
      if (reachable.empty()) {
        for (auto &F : *module) {
          if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
            enqueue(&F);
        }
      }

      for (size_t i = 0; i < worklist.size(); ++i) {
        llvm::Function *F = worklist[i];
        for (auto &BB : *F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *callee = CB->getCalledFunction();
            if (!callee || callee->isDeclaration())
              continue;
            enqueue(callee);
          }
        }
      }

      unsigned count = 0;
      for (auto *F : reachable) {
        for (auto &BB : *F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *callee = CB->getCalledFunction();
            if (!callee)
              continue;
            auto name = callee->getName();
            if (name.starts_with("__remill_read_memory_") ||
                name.starts_with("__remill_write_memory_")) {
              ++count;
            }
          }
        }
      }
      return count;
    };

    if (before_block_calls == 0)
      return;
    const unsigned before_live_memory_intrinsics =
        countReachableLiveRemillMemoryIntrinsics();

    omill::PipelineOptions replay_opts = opts;
    replay_opts.generic_static_devirtualize = false;
    replay_opts.verify_generic_static_devirtualization = false;
    replay_opts.resolve_indirect_targets = false;
    replay_opts.interprocedural_const_prop = false;
    replay_opts.deobfuscate = false;
    replay_opts.recover_abi = false;
    replay_opts.use_block_lifting = false;
    replay_opts.no_abi_mode = true;
    replay_opts.preserve_lifted_semantics = false;

    events.emitInfo("noabi_cleanup_replay_started",
                    "post-main no-abi cleanup replay started",
                    {{"internal_blk_calls_before",
                     static_cast<int64_t>(before_block_calls)},
                     {"reachable_live_remill_memory_intrinsics_before",
                      static_cast<int64_t>(before_live_memory_intrinsics)}});
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    {
      ModulePassManager ReplayMPM;
      omill::buildPipeline(ReplayMPM, replay_opts);
      ReplayMPM.run(*module, MAM);
    }
    const unsigned after_block_calls = countInternalSyntheticBlockCalls();
    const unsigned after_live_memory_intrinsics =
        countReachableLiveRemillMemoryIntrinsics();
    events.emitInfo("noabi_cleanup_replay_completed",
                    "post-main no-abi cleanup replay completed",
                    {{"internal_blk_calls_before",
                      static_cast<int64_t>(before_block_calls)},
                     {"internal_blk_calls_after",
                      static_cast<int64_t>(after_block_calls)},
                     {"reachable_live_remill_memory_intrinsics_before",
                      static_cast<int64_t>(before_live_memory_intrinsics)},
                     {"reachable_live_remill_memory_intrinsics_after",
                      static_cast<int64_t>(after_live_memory_intrinsics)}});
  };

  rerunNoAbiClosedSliceCleanupReplay();

  if (VerifyEach && verifyModule(*module, nullptr)) {
    errs() << "ERROR: module verification failed after main pipeline\n";
    for (const auto &F : *module)
      if (!F.isDeclaration() && verifyFunction(F, nullptr))
        errs() << "  broken function: " << F.getName() << "\n";
    return fail(1, "module verification failed after main pipeline");
  }

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("after.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after.ll\n";
    }
  }

  // VM target discovery loop: after the pipeline resolves dispatch targets,
  // some are newly discovered (image_base + RVA where RVA wasn't in the
  // original binary scan).  Lift these new targets and re-run the pipeline.
  const bool allow_legacy_vm_discovery_loop =
      vm_mode && !force_devirtualize && !GenericStaticDevirtualize &&
      !opts.generic_static_devirtualize;
  if (allow_legacy_vm_discovery_loop) {
    for (unsigned vm_round = 0; vm_round < 4; ++vm_round) {
      if (events.detailed()) {
        events.emitInfo("vm_discovery_round_started", "vm discovery round started",
                        {{"round", static_cast<int64_t>(vm_round + 1)}});
      }
      // Extract discovered dispatch targets from named metadata.
      llvm::DenseSet<uint64_t> dispatch_targets;
      if (auto *named_md =
              module->getNamedMetadata("omill.vm_discovered_targets")) {
        for (unsigned i = 0; i < named_md->getNumOperands(); ++i) {
          auto *tuple = named_md->getOperand(i);
          if (tuple->getNumOperands() == 0)
            continue;
          if (auto *cmd = llvm::dyn_cast<llvm::ConstantAsMetadata>(
                  tuple->getOperand(0))) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(cmd->getValue())) {
              uint64_t va = ci->getZExtValue();
              std::string name =
                  "sub_" + llvm::Twine::utohexstr(va).str();
              auto *existing = module->getFunction(name);
              if (!existing || existing->isDeclaration())
                dispatch_targets.insert(va);
            }
          }
        }
        // Remove so next round starts fresh.
        module->eraseNamedMetadata(named_md);
      }

      // Scan for dispatch_call(state, ConstantInt(pc), mem) where pc
      // points to unlifted code.  These are calls whose target was folded
      // to a constant by GVN/InstCombine but wasn't in the module when
      // LowerFunctionCall ran, so they went through the dispatch stub.
      // RewriteLiftedCallsToNative (during ABI recovery) would turn them
      // into inttoptr indirect calls; lifting them NOW lets that pass
      // resolve them to direct calls instead.
      llvm::DenseSet<uint64_t> call_targets;
      auto findDispatchFunction = [&](bool want_jump) -> llvm::Function * {
        for (auto &F : *module) {
          if (want_jump ? omill::isDispatchJumpName(F.getName())
                        : omill::isDispatchCallName(F.getName())) {
            return &F;
          }
        }
        return nullptr;
      };
      auto *dispatch_fn = findDispatchFunction(false);
      auto *dispatch_jmp = findDispatchFunction(true);
      auto scanDispatchUses = [&](llvm::Function *dispatcher) {
        if (!dispatcher)
          return;
        for (auto *U : dispatcher->users()) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(U);
          if (!call || call->arg_size() < 2)
            continue;
          auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!ci)
            continue;
          uint64_t target = ci->getZExtValue();
          if (target == 0)
            continue;
          bool in_code = false;
          if (RawBinary) {
            in_code = (target >= BaseAddress &&
                       target < BaseAddress + raw_code.size());
          } else {
            for (auto &sec : pe.code_sections) {
              if (target >= sec.va && target < sec.va + sec.size) {
                in_code = true;
                break;
              }
            }
          }
          if (!in_code)
            continue;
          std::string name =
              "sub_" + llvm::Twine::utohexstr(target).str();
          auto *existing = module->getFunction(name);
          if (!existing || existing->isDeclaration())
            call_targets.insert(target);
        }
      };
      scanDispatchUses(dispatch_fn);
      scanDispatchUses(dispatch_jmp);
      // Remove targets already covered by dispatch discovery.
      for (uint64_t va : dispatch_targets)
        call_targets.erase(va);

      if (dispatch_targets.empty() && call_targets.empty())
        break;

      errs() << "VM discovery round " << (vm_round + 1) << ": "
             << dispatch_targets.size() << " dispatch + "
             << call_targets.size() << " call target(s)\n";
      events.emitInfo("vm_discovery_targets", "vm discovery targets found",
                      {{"round", static_cast<int64_t>(vm_round + 1)},
                       {"dispatch_targets", static_cast<int64_t>(dispatch_targets.size())},
                       {"call_targets", static_cast<int64_t>(call_targets.size())}});

      // Snapshot existing functions before lifting so we can tag ALL new ones
      // (not just the top-level targets) with omill.vm_newly_lifted.
      // Without this, callee functions created by the lifter's graph walk
      // miss Phase 1 intrinsic lowering (the scoped pipeline only processes
      // functions with the newly_lifted attribute).
      llvm::DenseSet<llvm::Function *> pre_lift_funcs;
      for (auto &F : *module)
        pre_lift_funcs.insert(&F);

      // Lift dispatch targets as VM handlers.
      unsigned lift_ok = 0, lift_fail = 0;
      for (uint64_t va : dispatch_targets) {
        if (lifter.Lift(va)) {
          ++lift_ok;
          std::string name =
              "sub_" + llvm::Twine::utohexstr(va).str();
          if (auto *fn = module->getFunction(name))
            fn->addFnAttr("omill.vm_handler");
        } else {
          ++lift_fail;
        }
      }
      // Lift call targets as regular functions (NOT vm_handler — they
      // get _native wrappers via RecoverFunctionSignatures).
      for (uint64_t va : call_targets) {
        if (lifter.Lift(va))
          ++lift_ok;
        else
          ++lift_fail;
      }

      // Tag ALL functions that were added by the lifter during this round.
      for (auto &F : *module) {
        if (!pre_lift_funcs.count(&F) && !F.isDeclaration())
          F.addFnAttr("omill.vm_newly_lifted");
      }

      // Fix DeclareLiftedFunction naming collisions.
      for (auto &F : llvm::make_early_inc_range(*module)) {
        if (!F.isDeclaration())
          continue;
        auto fname = F.getName();
        if (!fname.starts_with("sub_"))
          continue;
        for (int i = 1; i <= 20; ++i) {
          std::string def_name = (fname + "." + Twine(i)).str();
          if (auto *def = module->getFunction(def_name)) {
            if (!def->isDeclaration()) {
              F.replaceAllUsesWith(def);
              F.eraseFromParent();
              def->setName(fname);
              break;
            }
          }
        }
      }
      for (auto &F : llvm::make_early_inc_range(*module)) {
        if (!F.isDeclaration())
          continue;
        auto fname = F.getName();
        if (!fname.starts_with("sub_"))
          continue;
        size_t dot = fname.rfind('.');
        if (dot == StringRef::npos || dot + 1 >= fname.size())
          continue;
        auto suffix = fname.drop_front(dot + 1);
        unsigned clone_index = 0;
        if (suffix.getAsInteger(10, clone_index))
          continue;
        std::string base_name = fname.take_front(dot).str();
        if (auto *base = module->getFunction(base_name)) {
          if (!base->isDeclaration()) {
            F.replaceAllUsesWith(base);
            F.eraseFromParent();
          }
        }
      }

      errs() << "  lifted " << lift_ok;
      if (lift_fail > 0)
        errs() << " (" << lift_fail << " failed)";
      errs() << "\n";

      if (lift_ok == 0)
        break;

      // Re-run the pipeline on the updated module.  Use a lightweight
      // configuration that skips deobfuscation (Phase 5) and iterative
      // target resolution (Phase 3.6) — the outer VM discovery loop
      // handles the iteration, and deobf is deferred to post-ABI.
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      {
        omill::PipelineOptions vm_opts = opts;
        vm_opts.deobfuscate = false;
        vm_opts.resolve_indirect_targets = false;
        vm_opts.interprocedural_const_prop = false;
        vm_opts.scope_predicate = [](llvm::Function &F) {
          return F.hasFnAttribute("omill.vm_newly_lifted");
        };
        ModulePassManager MPM;
        omill::buildPipeline(MPM, vm_opts);
        MPM.run(*module, MAM);
        emitIterativeSessionEvents(events, iterative_session,
                                   "vm-discovery-rerun");
      }

      // Clear the newly-lifted tags so next round starts fresh.
      for (auto &F : *module) {
        if (F.hasFnAttribute("omill.vm_newly_lifted"))
          F.removeFnAttr("omill.vm_newly_lifted");
      }

      errs() << "  pipeline re-run complete\n";
      events.emitInfo("vm_discovery_round_completed", "vm discovery round completed",
                      {{"round", static_cast<int64_t>(vm_round + 1)},
                       {"lifted", static_cast<int64_t>(lift_ok)},
                       {"failed", static_cast<int64_t>(lift_fail)}});

      // Checkpoint: save LL after each VM discovery round.
      repairMalformedPHIs(*module);
      {
        std::string ckpt_name =
            "vm_round_" + std::to_string(vm_round + 1) + ".ll";
        std::error_code ec;
        raw_fd_ostream os(ckpt_name, ec, sys::fs::OF_Text);
        if (!ec) {
          module->print(os, nullptr);
          errs() << "  saved checkpoint: " << ckpt_name << "\n";
        }
      }
    }
  }

  std::optional<std::string> pre_abi_checkpoint_text;
  const bool enable_debug_sample_native_fixups =
      parseBoolEnv("OMILL_ENABLE_DEBUG_SAMPLE_NATIVE_FIXUPS")
          .value_or(false);

  // ABI recovery
  if (!NoABI) {
    appendDebugMarker("abi:enter");
    if (!opts.generic_static_devirtualize)
      restoreVMHandlerAttrs();
    appendDebugMarker("abi:after_restore_vm_attrs");

    bool cached_recover_abi_text_valid = false;
    std::string cached_recover_abi_text_input;
    std::optional<std::string> cached_recover_abi_text_output;

    auto repairDeclaredContinuationWrappersInModule =
        [&](llvm::Module &M) -> unsigned {
      auto findNearestDefinedLiftedOrBlockInModule =
          [&](uint64_t target_pc, bool native,
              uint64_t *resolved_pc = nullptr) -> llvm::Function * {
            if (!target_pc)
              return nullptr;

            const uint64_t window = nearbyLiftedEntrySearchWindow();
            llvm::Function *best = nullptr;
            uint64_t best_pc = 0;
            uint64_t best_distance = std::numeric_limits<uint64_t>::max();

            for (auto &F : M) {
              if (F.isDeclaration())
                continue;
              auto entry_pc = extractLiftedOrBlockEntryPC(F.getName(), native);
              if (!entry_pc)
                continue;
              const uint64_t distance = (*entry_pc > target_pc)
                                            ? (*entry_pc - target_pc)
                                            : (target_pc - *entry_pc);
              if (distance == 0 || distance > window)
                continue;
              if (!best || distance < best_distance ||
                  (distance == best_distance && *entry_pc < best_pc)) {
                best = &F;
                best_pc = *entry_pc;
                best_distance = distance;
              }
            }

            if (best && resolved_pc)
              *resolved_pc = best_pc;
            return best;
          };

      unsigned rewritten = 0;
      auto *i64_ty = llvm::Type::getInt64Ty(M.getContext());
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI || CI->arg_size() < 3)
              continue;
            auto *callee = CI->getCalledFunction();
            if (!callee || !callee->isDeclaration())
              continue;
            auto name = callee->getName();
            if (!(name.starts_with("blk_") || name.starts_with("block_")) ||
                name.ends_with("_native")) {
              continue;
            }
            auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
            if (!pc_ci)
              continue;

            uint64_t resolved_pc = 0;
            auto *target = findNearestDefinedLiftedOrBlockInModule(
                pc_ci->getZExtValue(), /*native=*/false, &resolved_pc);
            if (!target || target == callee || target->isDeclaration())
              continue;

            if (auto *helper =
                    llvm::dyn_cast<llvm::CallInst>(CI->getArgOperand(2))) {
              if (auto *helper_callee = helper->getCalledFunction();
                  helper_callee &&
                  omill::isDispatchIntrinsicName(helper_callee->getName()) &&
                  helper->arg_size() >= 3) {
                CI->setArgOperand(2, helper->getArgOperand(2));
                if (helper->use_empty())
                  helper->eraseFromParent();
              }
            }

            CI->setCalledFunction(target);
            CI->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
            ++rewritten;
          }
        }
      }

      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI || CI->arg_size() < 3)
              continue;
            auto *callee = CI->getCalledFunction();
            if (!callee || !callee->isDeclaration())
              continue;
            auto name = callee->getName();
            if (!omill::isDispatchIntrinsicName(name)) {
              continue;
            }
            auto *pc_ci =
                llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
            if (!pc_ci)
              continue;

            uint64_t resolved_pc = 0;
            auto *target = findNearestDefinedLiftedOrBlockInModule(
                pc_ci->getZExtValue(), /*native=*/false, &resolved_pc);
            if (!target || target->isDeclaration() ||
                target->getFunctionType()->getNumParams() != CI->arg_size()) {
              continue;
            }

            if (auto *helper =
                    llvm::dyn_cast<llvm::CallInst>(CI->getArgOperand(2))) {
              if (auto *helper_callee = helper->getCalledFunction();
                  helper_callee &&
                  omill::isDispatchIntrinsicName(helper_callee->getName()) &&
                  helper->arg_size() >= 3) {
                CI->setArgOperand(2, helper->getArgOperand(2));
                if (helper->use_empty())
                  helper->eraseFromParent();
              }
            }

            CI->setCalledFunction(target);
            CI->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
            ++rewritten;
          }
        }
      }
      return rewritten;
    };

    auto prepareIRTextForABIReplay =
        [&](llvm::StringRef abi_input_ir) -> std::string {
      llvm::SMDiagnostic parse_error;
      auto replay_module =
          llvm::parseAssemblyString(abi_input_ir, parse_error, ctx);
      if (!replay_module)
        return abi_input_ir.str();
      unsigned rewritten =
          repairDeclaredContinuationWrappersInModule(*replay_module);
      if (rewritten == 0)
        return abi_input_ir.str();
      std::string repaired_ir;
      llvm::raw_string_ostream os(repaired_ir);
      replay_module->print(os, nullptr);
      os.flush();
      errs() << "[abi-prep] repaired-declared-continuation-wrappers="
             << rewritten << "\n";
      return repaired_ir;
    };

    auto runExternalRecoverABIText =
        [&](llvm::StringRef abi_input_ir) -> std::optional<std::string> {
      if (abi_input_ir.empty())
        return std::nullopt;

      std::string prepared_input_ir = prepareIRTextForABIReplay(abi_input_ir);
      llvm::StringRef effective_input_ir(prepared_input_ir);
      dumpTextIfEnvEnabled(effective_input_ir,
                           "OMILL_DEBUG_DUMP_EXTERNAL_RECOVER_ABI_INPUT_IR",
                           "external_recover_abi_input.ll");

      if (cached_recover_abi_text_valid &&
          effective_input_ir == cached_recover_abi_text_input) {
        return cached_recover_abi_text_output;
      }

      llvm::SmallString<256> opt_path(argv[0]);
      llvm::sys::path::remove_filename(opt_path);
      llvm::sys::path::remove_filename(opt_path);
      llvm::sys::path::append(opt_path, "omill-opt", "omill-opt.exe");
      if (!llvm::sys::fs::exists(opt_path)) {
        cached_recover_abi_text_input = effective_input_ir.str();
        cached_recover_abi_text_output = std::nullopt;
        cached_recover_abi_text_valid = true;
        return std::nullopt;
      }

      llvm::SmallString<256> temp_in_path;
      llvm::SmallString<256> temp_out_path;
      if (llvm::sys::fs::createTemporaryFile("omill_pre_abi_replay_in", "ll",
                                             temp_in_path)) {
        cached_recover_abi_text_input = effective_input_ir.str();
        cached_recover_abi_text_output = std::nullopt;
        cached_recover_abi_text_valid = true;
        return std::nullopt;
      }
      if (llvm::sys::fs::createTemporaryFile("omill_pre_abi_replay_out", "ll",
                                             temp_out_path)) {
        llvm::sys::fs::remove(temp_in_path);
        cached_recover_abi_text_input = effective_input_ir.str();
        cached_recover_abi_text_output = std::nullopt;
        cached_recover_abi_text_valid = true;
        return std::nullopt;
      }

      {
        std::error_code ec;
        llvm::raw_fd_ostream os(temp_in_path, ec, llvm::sys::fs::OF_Text);
        if (ec) {
          llvm::sys::fs::remove(temp_in_path);
          llvm::sys::fs::remove(temp_out_path);
          cached_recover_abi_text_input = effective_input_ir.str();
          cached_recover_abi_text_output = std::nullopt;
          cached_recover_abi_text_valid = true;
          return std::nullopt;
        }
        os << effective_input_ir;
      }

      llvm::SmallVector<std::string, 8> arg_storage;
      arg_storage.emplace_back(opt_path.str().str());
      arg_storage.emplace_back("--only-recover-abi");
      arg_storage.emplace_back(temp_in_path.str().str());
      arg_storage.emplace_back("-o");
      arg_storage.emplace_back(temp_out_path.str().str());

      llvm::SmallVector<llvm::StringRef, 8> argv_refs;
      for (const auto &arg : arg_storage)
        argv_refs.push_back(arg);

      std::string err_msg;
      bool exec_failed = false;
      int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                         std::nullopt, {}, 180u, 0, &err_msg,
                                         &exec_failed);
      llvm::sys::fs::remove(temp_in_path);
      if (rc != 0 || exec_failed) {
        llvm::sys::fs::remove(temp_out_path);
        cached_recover_abi_text_input = effective_input_ir.str();
        cached_recover_abi_text_output = std::nullopt;
        cached_recover_abi_text_valid = true;
        return std::nullopt;
      }

      auto buf_or_err = llvm::MemoryBuffer::getFile(temp_out_path);
      llvm::sys::fs::remove(temp_out_path);
      cached_recover_abi_text_input = effective_input_ir.str();
      cached_recover_abi_text_valid = true;
      if (!buf_or_err) {
        cached_recover_abi_text_output = std::nullopt;
        return std::nullopt;
      }
      cached_recover_abi_text_output = (*buf_or_err)->getBuffer().str();
      return cached_recover_abi_text_output;
    };

    auto runExternalRecoverABIFromCurrentModuleBitcode =
        [&]() -> std::optional<std::string> {
      llvm::SmallString<256> opt_path(argv[0]);
      llvm::sys::path::remove_filename(opt_path);
      llvm::sys::path::remove_filename(opt_path);
      llvm::sys::path::append(opt_path, "omill-opt", "omill-opt.exe");
      if (!llvm::sys::fs::exists(opt_path))
        return std::nullopt;

      llvm::SmallString<256> temp_in_path;
      llvm::SmallString<256> temp_out_path;
      if (llvm::sys::fs::createTemporaryFile("omill_pre_abi_replay_in", "bc",
                                             temp_in_path))
        return std::nullopt;
      if (llvm::sys::fs::createTemporaryFile("omill_pre_abi_replay_out", "ll",
                                             temp_out_path)) {
        llvm::sys::fs::remove(temp_in_path);
        return std::nullopt;
      }

      {
        std::error_code ec;
        llvm::raw_fd_ostream os(temp_in_path, ec, llvm::sys::fs::OF_None);
        if (ec) {
          llvm::sys::fs::remove(temp_in_path);
          llvm::sys::fs::remove(temp_out_path);
          return std::nullopt;
        }
        llvm::WriteBitcodeToFile(*module, os);
      }

      llvm::SmallVector<std::string, 8> arg_storage;
      arg_storage.emplace_back(opt_path.str().str());
      arg_storage.emplace_back("--only-recover-abi");
      arg_storage.emplace_back(temp_in_path.str().str());
      arg_storage.emplace_back("-o");
      arg_storage.emplace_back(temp_out_path.str().str());

      llvm::SmallVector<llvm::StringRef, 8> argv_refs;
      for (const auto &arg : arg_storage)
        argv_refs.push_back(arg);

      std::string err_msg;
      bool exec_failed = false;
      int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                         std::nullopt, {}, 180u, 0, &err_msg,
                                         &exec_failed);
      llvm::sys::fs::remove(temp_in_path);
      if (rc != 0 || exec_failed) {
        llvm::sys::fs::remove(temp_out_path);
        return std::nullopt;
      }

      auto buf_or_err = llvm::MemoryBuffer::getFile(temp_out_path);
      llvm::sys::fs::remove(temp_out_path);
      if (!buf_or_err)
        return std::nullopt;
      return (*buf_or_err)->getBuffer().str();
    };

    auto buildFilteredABIRecoveryCheckpointText =
        [&]() -> std::optional<std::string> {
      if (countDefinedOutputRoots() > 1u)
        return std::nullopt;

      llvm::SmallPtrSet<const llvm::Function *, 32> kept_functions;
      llvm::SmallVector<const llvm::Function *, 64> worklist;
      auto seed_function = [&](const llvm::Function &F) {
        if (F.isDeclaration())
          return;
        if (kept_functions.insert(&F).second)
          worklist.push_back(&F);
      };

      for (const auto &F : *module) {
        if (F.hasFnAttribute("omill.output_root") ||
            F.hasFnAttribute("omill.closed_root_slice_root")) {
          seed_function(F);
        }
      }
      if (kept_functions.empty())
        return std::nullopt;

      llvm::SmallVector<const llvm::Function *, 64> root_layer(worklist.begin(),
                                                               worklist.end());
      for (const llvm::Function *F : root_layer) {
        for (const auto &BB : *F) {
          for (const auto &I : BB) {
            const auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!call)
              continue;
            const auto *callee = call->getCalledFunction();
            if (!callee || callee->isDeclaration())
              continue;
            kept_functions.insert(callee);
          }
        }
      }

      llvm::ValueToValueMapTy VMap;
      auto should_clone_def = [&](const llvm::GlobalValue *GV) -> bool {
        if (const auto *F = llvm::dyn_cast<llvm::Function>(GV))
          return F->isDeclaration() || kept_functions.contains(F);
        return true;
      };
      auto filtered_module = llvm::CloneModule(*module, VMap, should_clone_def);
      if (!filtered_module || verifyModule(*filtered_module, nullptr))
        return std::nullopt;

      std::string filtered_ir;
      llvm::raw_string_ostream os(filtered_ir);
      filtered_module->print(os, nullptr);
      os.flush();
      events.emitInfo("filtered_pre_abi_checkpoint_built",
                      "filtered pre-ABI checkpoint built",
                      {{"kept_functions",
                        static_cast<int64_t>(kept_functions.size())},
                       {"filtered_ir_bytes",
                        static_cast<int64_t>(filtered_ir.size())}});
      return filtered_ir;
    };

    auto requiresHiddenEntrySeedPreservation = [&]() {
      for (auto &F : *module) {
        if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
          continue;
        auto attr = F.getFnAttribute("omill.export_entry_seed_exprs");
        if (attr.isValid() && attr.isStringAttribute() &&
            !attr.getValueAsString().empty()) {
          return true;
        }
      }
      return false;
    };

    auto ensureRecoveredModuleHasOutputRoot =
        [&](llvm::Module &M, uint64_t expected_root_va) -> llvm::Function * {
      auto pickUnique = [](llvm::ArrayRef<llvm::Function *> candidates)
          -> llvm::Function * {
        return candidates.size() == 1 ? candidates.front() : nullptr;
      };

      std::string target_hex = llvm::utohexstr(expected_root_va);
      llvm::SmallVector<llvm::Function *, 8> exact_target_roots;
      llvm::SmallVector<llvm::Function *, 8> exact_target_lifted_roots;
      llvm::SmallVector<llvm::Function *, 8> exact_target_native_roots;
      llvm::SmallVector<llvm::Function *, 8> output_roots;
      llvm::SmallVector<llvm::Function *, 8> lifted_functions;
      llvm::SmallVector<llvm::Function *, 8> native_functions;
      llvm::SmallVector<llvm::Function *, 8> defined_functions;
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        defined_functions.push_back(&F);
        if (F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
        if (!F.getName().ends_with("_native"))
          lifted_functions.push_back(&F);
        if (F.getName().ends_with("_native"))
          native_functions.push_back(&F);
        if (expected_root_va == 0)
          continue;
        const bool is_exact_lifted =
            (F.getName() == ("sub_" + target_hex)) ||
            (F.getName() == ("blk_" + target_hex)) ||
            (F.getName().contains(target_hex) &&
             !F.getName().ends_with("_native"));
        const bool is_exact_native =
            (F.getName() == ("sub_" + target_hex + "_native")) ||
            (F.getName() == ("blk_" + target_hex + "_native")) ||
            (F.getName().contains(target_hex) &&
             F.getName().ends_with("_native"));
        if (is_exact_lifted)
          exact_target_lifted_roots.push_back(&F);
        if (is_exact_native)
          exact_target_native_roots.push_back(&F);
        if (is_exact_lifted || is_exact_native) {
          exact_target_roots.push_back(&F);
        }
      }

      llvm::Function *root = nullptr;
      if (auto *F = pickUnique(exact_target_lifted_roots))
        root = F;
      else if (auto *F = pickUnique(exact_target_roots))
        root = F;
      else if (auto *F = pickUnique(output_roots))
        root = F;
      else if (auto *F = pickUnique(lifted_functions))
        root = F;
      else if (auto *F = pickUnique(native_functions))
        root = F;
      if (!root)
        root = pickUnique(defined_functions);
      if (!root)
        return nullptr;
      for (auto &F : M) {
        if (&F == root)
          continue;
        F.removeFnAttr("omill.output_root");
      }
      root->addFnAttr("omill.output_root");
      return root;
    };

    auto tryDirectReplayABIText = [&](llvm::StringRef abi_input_ir,
                                      llvm::StringRef event_name,
                                      llvm::StringRef event_message) -> bool {
      auto replayed_text = runExternalRecoverABIText(abi_input_ir);
      if (!replayed_text)
        return false;

      llvm::SMDiagnostic parse_error;
      auto replayed_module =
          llvm::parseAssemblyString(*replayed_text, parse_error, ctx);
      if (!replayed_module)
        return false;
      if (verifyModule(*replayed_module, nullptr))
        return false;
      const bool requires_hidden_entry_seed_preservation =
          requiresHiddenEntrySeedPreservation();

      auto *resolved_root =
          ensureRecoveredModuleHasOutputRoot(*replayed_module, func_va);
      if (!resolved_root)
        return false;
      if (requires_hidden_entry_seed_preservation) {
        auto attr = resolved_root->getFnAttribute("omill.export_entry_seed_exprs");
        if (!attr.isValid() || !attr.isStringAttribute() ||
            attr.getValueAsString().empty()) {
          return false;
        }
      }

      unsigned defined_output_roots = 0;
      bool has_unresolved_output_control_transfer = false;
      for (auto &F : *replayed_module) {
        if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
          continue;
        ++defined_output_roots;
        if (hasUnresolvedLiftedControlTransferInClosure(F))
          has_unresolved_output_control_transfer = true;
      }
      if (defined_output_roots == 0 || has_unresolved_output_control_transfer)
        return false;

      module = std::move(replayed_module);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      repairMalformedPHIs(*module);
      errs() << "ABI recovery replayed from closed pre-ABI checkpoint\n";
      events.emitInfo(event_name, event_message,
                      {{"defined_output_roots",
                        static_cast<int64_t>(defined_output_roots)}});
      return true;
    };

    auto runExternalMainRootNoABIChildIR = [&]() -> std::optional<std::string> {
      if (!use_pre_abi_noabi_cleanup || func_va == 0)
        return std::nullopt;

      llvm::SmallString<256> temp_ll_path;
      if (llvm::sys::fs::createTemporaryFile("omill_main_root_noabi", "ll",
                                             temp_ll_path)) {
        return std::nullopt;
      }

      llvm::SmallVector<std::string, 16> arg_storage;
      arg_storage.emplace_back(argv[0]);
      arg_storage.emplace_back(InputFilename);
      arg_storage.emplace_back("--va");
      arg_storage.emplace_back(llvm::utohexstr(func_va));
      if (opts.use_block_lifting)
        arg_storage.emplace_back("--block-lift");
      if (devirtualization_plan.enable_devirtualization)
        arg_storage.emplace_back("--devirtualize");
      if (opts.generic_static_devirtualize)
        arg_storage.emplace_back("--generic-static-devirtualize");
      arg_storage.emplace_back("--no-abi");
      arg_storage.emplace_back("-o");
      arg_storage.emplace_back(temp_ll_path.str().str());

      llvm::SmallVector<llvm::StringRef, 16> argv_refs;
      for (const auto &arg : arg_storage)
        argv_refs.push_back(arg);

      std::string err_msg;
      bool exec_failed = false;
      std::string recovery_root_va_text = llvm::utohexstr(func_va);
      ScopedEnvOverride skip_nested_probe(
          "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
      ScopedEnvOverride enable_late_output_target_rerun(
          "OMILL_ENABLE_LATE_OUTPUT_ROOT_TARGET_RERUN", "1");
      ScopedEnvOverride skip_late_boundary_rerun(
          "OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN", "1");
      ScopedEnvOverride enable_noabi_late_continuation_rerun(
          "OMILL_ENABLE_NOABI_LATE_CONTINUATION_RERUN", "1");
      ScopedEnvOverride enable_call_frontier_dispatch_override(
          "OMILL_ENABLE_CALL_FRONTIER_DISPATCH_OVERRIDE", "1");
      ScopedEnvOverride enable_terminal_boundary_recovery(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY", "1");
      ScopedEnvOverride terminal_boundary_recovery_root(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA",
          recovery_root_va_text.c_str());
      ScopedEnvOverride terminal_boundary_recovery_max_reachable(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE", "32");
      ScopedEnvOverride terminal_boundary_recovery_max_iterations(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_ITERATIONS", "14");
      ScopedEnvOverride terminal_boundary_recovery_max_new_target_rounds(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_NEW_TARGET_ROUNDS", "14");
      int rc = llvm::sys::ExecuteAndWait(
          argv_refs.front(), argv_refs, std::nullopt, {},
          parseUnsignedEnv("OMILL_MAIN_ROOT_NOABI_CHILD_TIMEOUT_SECONDS")
              .value_or(900u),
          0, &err_msg, &exec_failed);
      if (rc != 0 || exec_failed) {
        llvm::sys::fs::remove(temp_ll_path);
        return std::nullopt;
      }

      auto buf_or_err = llvm::MemoryBuffer::getFile(temp_ll_path);
      llvm::sys::fs::remove(temp_ll_path);
      if (!buf_or_err)
        return std::nullopt;
      return (*buf_or_err)->getBuffer().str();
    };

    {
      unsigned rewritten_live_pre_abi =
          repairDeclaredContinuationWrappersInModule(*module);
      if (rewritten_live_pre_abi != 0) {
        errs() << "[abi-prep] repaired-live-pre-abi-edges="
               << rewritten_live_pre_abi << "\n";
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        repairMalformedPHIs(*module);
      }
    }

    auto moduleReadableEnoughForDirectWrite = [&](const llvm::Module &M) {
      bool has_state_alloca = false;
      bool has_large_stack_alloca = false;
      bool uses_stacksave = false;
      bool calls_local_lifted_helper = false;
      unsigned defined_lifted_function_count = 0;
      const auto &DL = M.getDataLayout();
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        if ((F.getName().starts_with("sub_") || F.getName().starts_with("blk_") ||
             F.getName().starts_with("block_")) &&
            !F.getName().ends_with("_native")) {
          ++defined_lifted_function_count;
        }
        for (auto &BB : F) {
          for (auto &I : BB) {
            if (auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
              if (auto *allocated_struct =
                      llvm::dyn_cast<llvm::StructType>(
                          alloca->getAllocatedType());
                  allocated_struct && allocated_struct->hasName() &&
                  allocated_struct->getName() == "struct.State") {
                has_state_alloca = true;
              }
              if (auto *AT =
                      llvm::dyn_cast<llvm::ArrayType>(alloca->getAllocatedType())) {
                if (DL.getTypeAllocSize(AT) >= 4096)
                  has_large_stack_alloca = true;
              }
            }
            auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
            auto *callee = call ? call->getCalledFunction() : nullptr;
            if (callee && callee->getName() == "llvm.stacksave.p0")
              uses_stacksave = true;
            if (callee && !callee->isDeclaration() &&
                !callee->getName().ends_with("_native") &&
                (callee->getName().starts_with("sub_") ||
                 callee->getName().starts_with("blk_") ||
                 callee->getName().starts_with("block_"))) {
              calls_local_lifted_helper = true;
            }
          }
        }
      }
      return !has_state_alloca && !has_large_stack_alloca &&
             !uses_stacksave && !calls_local_lifted_helper &&
             defined_lifted_function_count == 0;
    };

    auto writeFinalOutputTextAndExit = [&](llvm::StringRef final_ir_text,
                                           llvm::StringRef event_name,
                                           llvm::StringRef event_message)
        -> std::optional<int> {
      llvm::LLVMContext verify_ctx;
      llvm::SMDiagnostic parse_error;
      auto verify_module =
          llvm::parseAssemblyString(final_ir_text, parse_error, verify_ctx);
      if (!verify_module || verifyModule(*verify_module, nullptr) ||
          !moduleReadableEnoughForDirectWrite(*verify_module)) {
        return std::nullopt;
      }

      std::error_code direct_ec;
      events.emitInfo("output_write_started", "writing final output",
                      {{"path", OutputFilename}});
      ToolOutputFile direct_out(OutputFilename, direct_ec, sys::fs::OF_Text);
      if (direct_ec) {
        errs() << "Error opening output: " << direct_ec.message() << "\n";
        return fail(1, "failed to open output file");
      }
      direct_out.os() << final_ir_text;
      direct_out.keep();
      events.emitInfo(event_name, event_message);
      events.emitInfo("output_write_completed", "output write complete",
                      {{"path", OutputFilename}});
      events.emitTerminalSuccess(OutputFilename);
      return 0;
    };

    const bool debug_small_replay =
        parseBoolEnv("OMILL_DEBUG_SMALL_REPLAY").value_or(false);

    const bool force_external_main_root_child_replay =
        parseBoolEnv("OMILL_FORCE_MAIN_ROOT_NOABI_CHILD_REPLAY").value_or(false);
    const bool enable_external_main_root_child_replay =
        parseBoolEnv("OMILL_ENABLE_MAIN_ROOT_NOABI_CHILD_REPLAY")
            .value_or(false);
    const bool prefer_external_main_root_child_replay =
        use_pre_abi_noabi_cleanup &&
        !parseBoolEnv("OMILL_SKIP_MAIN_ROOT_NOABI_CHILD_REPLAY")
             .value_or(false) &&
        countDefinedOutputRoots() <= 1u &&
        (force_external_main_root_child_replay ||
         (enable_external_main_root_child_replay &&
          moduleHasStructuralOutputFrontierArtifacts()));

    if (prefer_external_main_root_child_replay) {
      errs() << "Attempting external main-root no-ABI replay fallback\n";
      events.emitInfo("main_root_noabi_child_replay_started",
                      "external main-root no-ABI replay fallback started");
      if (auto noabi_child_ir = runExternalMainRootNoABIChildIR()) {
        events.emitInfo("main_root_noabi_child_completed",
                        "external main-root no-ABI child completed");
        dumpTextIfEnvEnabled(*noabi_child_ir,
                             "OMILL_DEBUG_DUMP_MAIN_ROOT_NOABI_CHILD_IR",
                             "main_root_noabi_child.ll");
        if (auto replayed_text = runExternalRecoverABIText(*noabi_child_ir)) {
          auto summary = parseTerminalBoundaryRecoveryIRSummary(*replayed_text);
          const bool has_unresolved_pc_text =
              replayed_text->find("pc.canonical") != std::string::npos ||
              replayed_text->find("pc.norm") != std::string::npos;
          const bool clean_text_fallback =
              summary.has_output_root && !has_unresolved_pc_text &&
              summary.metrics.dispatch_call == 0 &&
              summary.metrics.dispatch_jump == 0 &&
              summary.metrics.declare_blk == 0 &&
              summary.metrics.missing_block_handler == 0;
          if (clean_text_fallback) {
            if (auto direct_exit = writeFinalOutputTextAndExit(
                    *replayed_text,
                    "abi_recovery_replayed_from_main_root_noabi_child",
                    "ABI recovery replayed from external main-root no-ABI child")) {
              return *direct_exit;
            }
          }
          errs() << "External main-root no-ABI replay fallback rejected clean="
                 << (clean_text_fallback ? 1 : 0) << "\n";
          events.emitInfo("main_root_noabi_child_replay_rejected",
                          "external main-root no-ABI replay fallback rejected",
                          {{"clean_text_fallback",
                            static_cast<int64_t>(clean_text_fallback ? 1 : 0)},
                           {"dispatch_call",
                            static_cast<int64_t>(summary.metrics.dispatch_call)},
                           {"dispatch_jump",
                            static_cast<int64_t>(summary.metrics.dispatch_jump)},
                           {"declare_blk",
                            static_cast<int64_t>(summary.metrics.declare_blk)},
                           {"missing_block",
                            static_cast<int64_t>(
                                summary.metrics.missing_block_handler)}});
        }
      } else {
        errs() << "External main-root no-ABI child failed\n";
        events.emitInfo("main_root_noabi_child_failed",
                        "external main-root no-ABI child failed");
      }
    }

    const bool force_direct_replay =
        parseBoolEnv("OMILL_FORCE_PRE_ABI_DIRECT_REPLAY").value_or(false);
    const bool skip_pre_abi_direct_replay_for_vm_like_root =
        root_local_generic_static_devirtualization_shape &&
        opts.generic_static_devirtualize;
    const bool skip_pre_abi_direct_replay_for_hidden_entry_seeds =
        export_root_has_hidden_entry_seed_exprs;
    const bool skip_pre_abi_direct_replay =
        skip_pre_abi_direct_replay_for_hidden_entry_seeds ||
        skip_pre_abi_direct_replay_for_vm_like_root;
    const bool prefer_direct_replay =
        use_pre_abi_noabi_cleanup && force_direct_replay &&
        !skip_pre_abi_direct_replay &&
        !parseBoolEnv("OMILL_SKIP_PRE_ABI_DIRECT_REPLAY").value_or(false);

    if (use_pre_abi_noabi_cleanup &&
        parseBoolEnv("OMILL_FORCE_PRE_ABI_BITCODE_REPLAY").value_or(false) &&
        countDefinedOutputRoots() <= 1u) {
      appendDebugMarker("abi:before_bitcode_replay");
      errs() << "Attempting pre-ABI bitcode replay fallback\n";
      if (auto replayed_text = runExternalRecoverABIFromCurrentModuleBitcode()) {
        appendDebugMarker("abi:after_bitcode_replay");
        auto summary = parseTerminalBoundaryRecoveryIRSummary(*replayed_text);
        const bool has_unresolved_pc_text =
            replayed_text->find("pc.canonical") != std::string::npos ||
            replayed_text->find("pc.norm") != std::string::npos;
        const bool clean_text_fallback =
            summary.has_output_root && !has_unresolved_pc_text &&
            summary.metrics.dispatch_call == 0 &&
            summary.metrics.dispatch_jump == 0 &&
            summary.metrics.declare_blk == 0 &&
            summary.metrics.missing_block_handler == 0;
        errs() << "Pre-ABI bitcode replay fallback clean="
               << (clean_text_fallback ? 1 : 0) << "\n";
        if (clean_text_fallback) {
          if (auto direct_exit = writeFinalOutputTextAndExit(
                  *replayed_text,
                  "abi_recovery_replayed_from_pre_abi_bitcode",
                  "ABI recovery replayed from pre-ABI bitcode checkpoint")) {
            return *direct_exit;
          }
        }
      } else {
        appendDebugMarker("abi:bitcode_replay_failed");
        errs() << "Pre-ABI bitcode replay fallback failed\n";
      }
    }

    if (prefer_direct_replay &&
        tryDirectReplayABIText(*pre_abi_checkpoint_text,
                               "abi_recovery_replayed_from_main_checkpoint",
                               "ABI recovery replayed from main pre-ABI checkpoint")) {
      appendDebugMarker("abi:after_prefer_direct_replay");
      dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_ABI_CORE",
                             "after_abi_core.ll");
    } else {
      appendDebugMarker("abi:before_live_abi_branch");
      if (use_pre_abi_noabi_cleanup) {
        // The pre-ABI generic cleanup reuses the safer no-ABI closed-slice path
        // to flatten the slice before signature recovery. Clear the marker before
        // ABI recovery so ABI-only rewrites do not inherit no-ABI mode.
        module->setModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 0u);
      }
      events.emitInfo("abi_recovery_started", "abi recovery started");
      {
        auto checkpoint_patch_targets = collectAllConstantMissingBlockTargets();
        if (!checkpoint_patch_targets.empty()) {
          llvm::SmallVector<uint64_t, 16> ordered_targets(
              checkpoint_patch_targets.begin(), checkpoint_patch_targets.end());
          llvm::sort(ordered_targets);
          patchConstantMissingBlockCallsToLiftedTargets(
              ordered_targets, "abi_pre_checkpoint_missing_block_patch",
              "patched pre-ABI missing-block calls to lifted targets");
        }
      }
      appendDebugMarker("abi:before_raw_checkpoint_print");
      {
        if (use_pre_abi_noabi_cleanup && countDefinedOutputRoots() <= 1u &&
            !parseBoolEnv("OMILL_SKIP_FILTERED_PRE_ABI_CHECKPOINT")
                 .value_or(false)) {
          pre_abi_checkpoint_text = buildFilteredABIRecoveryCheckpointText();
        }
        if (!pre_abi_checkpoint_text) {
          std::string checkpoint_ir;
          llvm::raw_string_ostream checkpoint_os(checkpoint_ir);
          module->print(checkpoint_os, nullptr);
          checkpoint_os.flush();
          pre_abi_checkpoint_text = std::move(checkpoint_ir);
        }
      }
      appendDebugMarker("abi:after_raw_checkpoint_print");
      {
        std::error_code ec;
        raw_fd_ostream os("before_abi.ll", ec, sys::fs::OF_Text);
        if (!ec) {
          os << *pre_abi_checkpoint_text;
          errs() << "Saved before_abi.ll\n";
        }
      }
      bool accepted_small_checkpoint_replay = false;
      auto replayedModuleReadableEnoughForFastPlainFallback =
          [&](const llvm::Module &M) {
            if (!fast_plain_export_root_fallback)
              return true;
            bool has_state_alloca = false;
            bool has_large_stack_alloca = false;
            bool uses_stacksave = false;
            bool calls_local_lifted_helper = false;
            unsigned defined_lifted_function_count = 0;
            const auto &DL = M.getDataLayout();
            for (auto &F : M) {
              if (F.isDeclaration())
                continue;
              if ((F.getName().starts_with("sub_") ||
                   F.getName().starts_with("blk_") ||
                   F.getName().starts_with("block_")) &&
                  !F.getName().ends_with("_native")) {
                ++defined_lifted_function_count;
              }
              for (auto &BB : F) {
                for (auto &I : BB) {
                  auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I);
                  if (alloca) {
                    auto *allocated_struct =
                        llvm::dyn_cast<llvm::StructType>(
                            alloca->getAllocatedType());
                    if (allocated_struct && allocated_struct->hasName() &&
                        allocated_struct->getName() == "struct.State") {
                      has_state_alloca = true;
                    }
                    if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(
                            alloca->getAllocatedType())) {
                      if (DL.getTypeAllocSize(AT) >= 4096)
                        has_large_stack_alloca = true;
                    }
                  }
                  auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
                  auto *callee = call ? call->getCalledFunction() : nullptr;
                  if (callee && callee->getName() == "llvm.stacksave.p0")
                    uses_stacksave = true;
                  if (callee && !callee->isDeclaration() &&
                      !callee->getName().ends_with("_native") &&
                      (callee->getName().starts_with("sub_") ||
                       callee->getName().starts_with("blk_") ||
                       callee->getName().starts_with("block_"))) {
                    calls_local_lifted_helper = true;
                  }
                }
              }
            }
            return !has_state_alloca && !has_large_stack_alloca &&
                   !uses_stacksave && !calls_local_lifted_helper &&
                   defined_lifted_function_count == 0;
          };
      constexpr size_t kMaxAutoDirectReplayCheckpointBytes = 32ull << 20;
      if (pre_abi_checkpoint_text &&
          pre_abi_checkpoint_text->size() <=
              kMaxAutoDirectReplayCheckpointBytes &&
          !skip_pre_abi_direct_replay &&
          !parseBoolEnv("OMILL_SKIP_PRE_ABI_DIRECT_REPLAY").value_or(false)) {
        if (debug_small_replay) {
          errs() << "[small-replay] checkpoint-bytes="
                 << pre_abi_checkpoint_text->size() << "\n";
        }
        if (auto replayed_text = runExternalRecoverABIText(*pre_abi_checkpoint_text)) {
          const bool has_unresolved_pc_text =
              replayed_text->find("pc.canonical") != std::string::npos ||
              replayed_text->find("pc.norm") != std::string::npos;
          llvm::SMDiagnostic parse_error;
          auto replayed_module =
              llvm::parseAssemblyString(*replayed_text, parse_error, ctx);
          if (replayed_module && !verifyModule(*replayed_module, nullptr) &&
              !has_unresolved_pc_text) {
            auto ensureRecoveredModuleHasOutputRoot =
                [&](llvm::Module &M,
                    uint64_t expected_root_va) -> llvm::Function * {
                  auto pickUnique =
                      [](llvm::ArrayRef<llvm::Function *> candidates)
                      -> llvm::Function * {
                    return candidates.size() == 1 ? candidates.front()
                                                  : nullptr;
                  };

                  std::string target_hex = llvm::utohexstr(expected_root_va);
                  llvm::SmallVector<llvm::Function *, 8> exact_target_roots;
                  llvm::SmallVector<llvm::Function *, 8> output_roots;
                  llvm::SmallVector<llvm::Function *, 8> native_functions;
                  llvm::SmallVector<llvm::Function *, 8> defined_functions;
                  for (auto &F : M) {
                    if (F.isDeclaration())
                      continue;
                    defined_functions.push_back(&F);
                    if (F.hasFnAttribute("omill.output_root"))
                      output_roots.push_back(&F);
                    if (F.getName().ends_with("_native"))
                      native_functions.push_back(&F);
                    if (expected_root_va != 0 &&
                        ((F.getName() == ("sub_" + target_hex + "_native")) ||
                         (F.getName() ==
                          ("blk_" + target_hex + "_native")) ||
                         (F.getName().contains(target_hex) &&
                          F.getName().ends_with("_native")))) {
                      exact_target_roots.push_back(&F);
                    }
                  }

                  llvm::Function *root = nullptr;
                  if (auto *F = pickUnique(exact_target_roots))
                    root = F;
                  else if (auto *F = pickUnique(output_roots))
                    root = F;
                  else if (auto *F = pickUnique(native_functions))
                    root = F;
                  else if (auto *F = pickUnique(defined_functions))
                    root = F;
                  if (!root)
                    return nullptr;
                  for (auto &F : M) {
                    if (&F == root)
                      continue;
                    F.removeFnAttr("omill.output_root");
                  }
                  root->addFnAttr("omill.output_root");
                  return root;
                };
            if (!ensureRecoveredModuleHasOutputRoot(*replayed_module, func_va))
              replayed_module.reset();
          }
          if (replayed_module && !verifyModule(*replayed_module, nullptr) &&
              !has_unresolved_pc_text) {
            unsigned defined_output_roots = 0;
            bool has_dispatch = false;
            bool has_missing_block_handler = false;
            unsigned declared_blk_count = 0;
            unsigned call_blk_count = 0;
            bool has_state_alloca = false;
            unsigned defined_lifted_function_count = 0;
            for (auto &F : *replayed_module) {
              if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
                ++defined_output_roots;
              if (omill::isDispatchIntrinsicName(F.getName())) {
                has_dispatch |= !F.use_empty();
              }
              if (F.isDeclaration() &&
                  (F.getName().starts_with("blk_") ||
                   F.getName().starts_with("block_"))) {
                ++declared_blk_count;
              }
              if (F.getName() == "__omill_missing_block_handler") {
                has_missing_block_handler |= !F.use_empty();
              }
              if (F.isDeclaration())
                continue;
              if ((F.getName().starts_with("sub_") ||
                   F.getName().starts_with("blk_") ||
                   F.getName().starts_with("block_")) &&
                  !F.getName().ends_with("_native")) {
                ++defined_lifted_function_count;
              }
              for (auto &BB : F) {
                for (auto &I : BB) {
                  if (auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
                    auto *allocated_type = alloca->getAllocatedType();
                    auto *allocated_struct =
                        llvm::dyn_cast<llvm::StructType>(allocated_type);
                    if (allocated_struct &&
                        allocated_struct->hasName() &&
                        allocated_struct->getName() == "struct.State") {
                      has_state_alloca = true;
                    }
                  }
                  auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
                  auto *callee = call ? call->getCalledFunction() : nullptr;
                  if (callee &&
                      (callee->getName().starts_with("blk_") ||
                       callee->getName().starts_with("block_"))) {
                    ++call_blk_count;
                  }
                }
              }
            }
            if (debug_small_replay) {
              errs() << "[small-replay] roots=" << defined_output_roots
                     << " dispatch=" << (has_dispatch ? 1 : 0)
                     << " missing=" << (has_missing_block_handler ? 1 : 0)
                     << " state_alloca=" << (has_state_alloca ? 1 : 0)
                     << " defined_lifted=" << defined_lifted_function_count
                     << " declare_blk=" << declared_blk_count
                     << " call_blk=" << call_blk_count << "\n";
            }
            const bool readable_enough_for_fast_plain_direct_replay =
                replayedModuleReadableEnoughForFastPlainFallback(*replayed_module);
            const bool structurally_clean_enough_for_direct_write =
                defined_output_roots > 0 && !has_dispatch &&
                !has_missing_block_handler &&
                !has_state_alloca &&
                defined_lifted_function_count == 0 &&
                readable_enough_for_fast_plain_direct_replay &&
                declared_blk_count <= 4u &&
                call_blk_count <= 16u;
            const bool structurally_small_enough_to_adopt =
                defined_output_roots > 0 && !has_dispatch &&
                !has_missing_block_handler &&
                !has_state_alloca &&
                readable_enough_for_fast_plain_direct_replay &&
                declared_blk_count <= 16u &&
                call_blk_count <= 32u;
            if (structurally_clean_enough_for_direct_write ||
                structurally_small_enough_to_adopt) {
              if (debug_small_replay)
                errs() << "[small-replay] adopted-for-post-cleanup\n";
              module = std::move(replayed_module);
              MAM.invalidate(*module, llvm::PreservedAnalyses::none());
              repairMalformedPHIs(*module);
              accepted_small_checkpoint_replay = true;
              errs() << "ABI recovery adopted from small pre-ABI checkpoint\n";
              events.emitInfo("abi_recovery_adopted_from_small_checkpoint",
                              "ABI recovery adopted from small pre-ABI checkpoint",
                              {{"defined_output_roots",
                                static_cast<int64_t>(defined_output_roots)},
                               {"declared_blk_count",
                                static_cast<int64_t>(declared_blk_count)},
                               {"call_blk_count",
                                static_cast<int64_t>(call_blk_count)}});
            }
          } else if (debug_small_replay) {
            errs() << "[small-replay] parse-or-verify-failed unresolved_pc="
                   << (has_unresolved_pc_text ? 1 : 0) << "\n";
          }
        } else if (debug_small_replay) {
          errs() << "[small-replay] external-recover-abi failed\n";
        }
      }
      if (!accepted_small_checkpoint_replay &&
          !skip_pre_abi_direct_replay &&
          !parseBoolEnv("OMILL_SKIP_PRE_ABI_DIRECT_REPLAY").value_or(false)) {
        if (auto replayed_text =
                runExternalRecoverABIText(*pre_abi_checkpoint_text)) {
          auto summary = parseTerminalBoundaryRecoveryIRSummary(*replayed_text);
          const bool has_unresolved_pc_text =
              replayed_text->find("pc.canonical") != std::string::npos ||
              replayed_text->find("pc.norm") != std::string::npos;
          const bool clean_text_fallback =
              summary.has_output_root && !has_unresolved_pc_text &&
              summary.metrics.dispatch_call == 0 &&
              summary.metrics.dispatch_jump == 0 &&
              summary.metrics.declare_blk == 0 &&
              summary.metrics.missing_block_handler == 0;
          if (clean_text_fallback) {
            llvm::SMDiagnostic parse_error;
            auto replayed_module =
                llvm::parseAssemblyString(*replayed_text, parse_error, ctx);
            if (replayed_module && !verifyModule(*replayed_module, nullptr) &&
                replayedModuleReadableEnoughForFastPlainFallback(
                    *replayed_module)) {
              module = std::move(replayed_module);
              MAM.invalidate(*module, llvm::PreservedAnalyses::none());
              repairMalformedPHIs(*module);
              errs() << "ABI recovery replayed from raw pre-ABI checkpoint\n";
              events.emitInfo("abi_recovery_replayed_from_raw_pre_abi",
                              "ABI recovery replayed from raw pre-ABI checkpoint",
                              {{"defined_output_roots", 1}});
            }
          }
        }
      }
      if (!accepted_small_checkpoint_replay) {
        // Repair broken PHIs before saving checkpoint (otherwise LLVM parser
        // rejects the LL on reload).
        appendDebugMarker("abi:before_repair_phis");
        repairMalformedPHIs(*module);
        appendDebugMarker("abi:after_repair_phis");
        {
          std::string checkpoint_ir;
          llvm::raw_string_ostream checkpoint_os(checkpoint_ir);
          module->print(checkpoint_os, nullptr);
          checkpoint_os.flush();
          pre_abi_checkpoint_text = std::move(checkpoint_ir);
        }
      }
      if (!accepted_small_checkpoint_replay &&
          use_pre_abi_noabi_cleanup && countDefinedOutputRoots() <= 1u &&
          !skip_pre_abi_direct_replay &&
          !parseBoolEnv("OMILL_SKIP_PRE_ABI_DIRECT_REPLAY").value_or(false)) {
        if (auto replayed_text =
                runExternalRecoverABIText(*pre_abi_checkpoint_text)) {
          auto summary = parseTerminalBoundaryRecoveryIRSummary(*replayed_text);
          const bool has_unresolved_pc_text =
              replayed_text->find("pc.canonical") != std::string::npos ||
              replayed_text->find("pc.norm") != std::string::npos;
          const bool clean_text_fallback =
              summary.has_output_root && !has_unresolved_pc_text &&
              summary.metrics.dispatch_call == 0 &&
              summary.metrics.dispatch_jump == 0 &&
              summary.metrics.declare_blk == 0 &&
              summary.metrics.missing_block_handler == 0;
          if (clean_text_fallback) {
            llvm::SMDiagnostic parse_error;
            auto replayed_module =
                llvm::parseAssemblyString(*replayed_text, parse_error, ctx);
            if (replayed_module && !verifyModule(*replayed_module, nullptr) &&
                replayedModuleReadableEnoughForFastPlainFallback(
                    *replayed_module)) {
              module = std::move(replayed_module);
              MAM.invalidate(*module, llvm::PreservedAnalyses::none());
              repairMalformedPHIs(*module);
              errs() << "ABI recovery replayed from pre-ABI checkpoint\n";
              events.emitInfo("abi_recovery_replayed_from_pre_abi",
                              "ABI recovery replayed from pre-ABI checkpoint",
                              {{"defined_output_roots", 1}});
            }
          }
        }
      }
      auto tryDirectReplayABIFromPreABICheckpoint = [&]() -> bool {
        if (accepted_small_checkpoint_replay)
          return true;
        if (!use_pre_abi_noabi_cleanup)
          return false;
        if (!pre_abi_checkpoint_text || pre_abi_checkpoint_text->empty())
          return false;
        if (skip_pre_abi_direct_replay)
          return false;
        if (parseBoolEnv("OMILL_SKIP_PRE_ABI_DIRECT_REPLAY").value_or(false))
          return false;
        if (countDefinedOutputRoots() > 1u &&
            !parseBoolEnv("OMILL_FORCE_PRE_ABI_DIRECT_REPLAY").value_or(false)) {
          return false;
        }

        return tryDirectReplayABIText(*pre_abi_checkpoint_text,
                                      "abi_recovery_replayed_from_pre_abi",
                                      "ABI recovery replayed from pre-ABI checkpoint");
      };

      if (!tryDirectReplayABIFromPreABICheckpoint()) {
        // ABI recovery relies on fresh module analyses. Reusing analysis state
        // from the pre-ABI main pipeline can miscompile recovered roots, because
        // the module shape changed substantially during lifting/devirtualization.
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        ModulePassManager MPM;
          omill::buildABIRecoveryPipeline(MPM, opts);
        MPM.run(*module, MAM);
        errs() << "ABI recovery complete\n";
        events.emitInfo("abi_recovery_completed", "abi recovery completed");
        dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_ABI_CORE",
                               "after_abi_core.ll");
      }
    }

    if (VerifyEach && verifyModule(*module, nullptr)) {
      errs() << "ERROR: module verification failed after ABI recovery\n";
      for (const auto &F : *module)
        if (!F.isDeclaration() && verifyFunction(F, nullptr))
          errs() << "  broken function: " << F.getName() << "\n";
      return fail(1, "module verification failed after ABI recovery");
    }

    // Patch B3 call sites: after ABI recovery created _native wrappers,
    // scan for inttoptr(i64 X to ptr) call targets where @sub_X_native
    // exists, and rewrite them to direct calls.  This resolves constant
    // targets that were discovered during VM discovery or optimization
    // but couldn't be resolved at the time (the target wasn't lifted yet
    // when RewriteLiftedCallsToNative ran).
    if (!devirtualization_plan.enable_devirtualization &&
        !parseBoolEnv("OMILL_SKIP_ABI_POSTPATCH_CONSTANT_CALL_PATCH")
             .value_or(false)) {
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] patchConstantIntToPtrCallsToNative:start\n";
      auto targets_to_patch =
          collectConstantCodeCallTargets([](const llvm::Function &) {
            return true;
          });
      llvm::SmallVector<uint64_t, 32> ordered_targets(targets_to_patch.begin(),
                                                      targets_to_patch.end());
      patchConstantIntToPtrCallsToNative(
          ordered_targets, "abi_patch_callsites",
          "patched inttoptr callsites");
      auto calli_targets_to_patch =
          collectConstantCalliTargets([](const llvm::Function &) {
            return true;
          });
      llvm::SmallVector<uint64_t, 32> ordered_calli_targets(
          calli_targets_to_patch.begin(), calli_targets_to_patch.end());
      patchConstantCalliTargetsToDirectCalls(
          ordered_calli_targets, "abi_patch_calli_callsites",
          "patched constant CALLI callsites");
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] patchConstantIntToPtrCallsToNative:end\n";
    }

    // Legacy wrapper-oriented ABI post-fixups were retired with the
    // `_native` compatibility pipeline. The direct canonical ABI path keeps
    // the lightweight constant-target patch above and skips the wrapper-only
    // B3/native repair machinery entirely.
#if 0
    auto fixupB3DispatchArgMismatches = [&]() {
      // Fixup B3 direct calls whose resolved _native callee ended up with a
      // different signature. B3 materializes ABI regs plus callee-saved regs;
      // late discovery can also introduce under-passed direct calls once the
      // real _native prototype becomes available. Rebuild the call arguments
      // by matching param State offsets instead of trusting positional order.
      omill::StateFieldMap sfm(*module);
      auto arch_abi =
          omill::ArchABI::get(omill::TargetArch::kX86_64, "windows");

      // Build B3 arg-to-State-offset table (ABI regs then callee-saved).
      llvm::SmallVector<unsigned, 16> b3_arg_offsets;
      for (auto &reg : arch_abi.param_regs) {
        auto f = sfm.fieldByName(reg);
        if (f) b3_arg_offsets.push_back(f->offset);
      }
      for (auto &cs : arch_abi.callee_saved) {
        auto f = sfm.fieldByName(cs);
        if (f) b3_arg_offsets.push_back(f->offset);
      }

      auto *i64_ty = llvm::Type::getInt64Ty(ctx);
      unsigned fixup_count = 0;
      bool debug_public_root_seeds =
          parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
      auto parseHiddenSeedExprMap = [&](llvm::StringRef seed_text) {
        llvm::DenseMap<unsigned, std::string> result;
        llvm::SmallVector<llvm::StringRef, 16> seed_entries;
        seed_text.split(seed_entries, ';', -1, false);
        for (auto entry : seed_entries) {
          entry = entry.trim();
          if (entry.empty())
            continue;
          auto pair = entry.split('=');
          if (pair.first.empty() || pair.second.empty())
            continue;
          auto field = sfm.fieldByName(pair.first.trim());
          if (!field.has_value())
            continue;
          result[field->offset] = pair.second.trim().str();
        }
        return result;
      };

      for (auto &F : *module) {
        if (!F.getName().ends_with("_native")) continue;
        if (debug_public_root_seeds) {
          errs() << "[post-abi-fixup] scanning-function=" << F.getName()
                 << " args=" << F.arg_size()
                 << " decl=" << F.isDeclaration() << "\n";
        }
        const bool is_requested_export_native_root =
            requested_root_is_export && batch_vas.empty() && func_va != 0 &&
            omill::extractEntryVA(F.getName()) == func_va;
        if (debug_public_root_seeds &&
            F.getName().contains("sub_1800020e0_native")) {
          errs() << "[post-abi-fixup] saw " << F.getName()
                 << " requested_export_native_root="
                 << is_requested_export_native_root
                 << " output_root=" << F.hasFnAttribute("omill.output_root")
                 << "\n";
        }
        llvm::SmallVector<int, 16> caller_param_offsets;
        if (auto attr = F.getFnAttribute("omill.param_state_offsets");
            attr.isValid() && attr.isStringAttribute()) {
          llvm::SmallVector<llvm::StringRef, 16> caller_offset_strs;
          attr.getValueAsString().split(caller_offset_strs, ',');
          for (auto &off_str : caller_offset_strs) {
            if (off_str == "stack" || off_str == "xmm") {
              caller_param_offsets.push_back(-1);
              continue;
            }
            unsigned off = 0;
            if (off_str.getAsInteger(10, off))
              caller_param_offsets.push_back(-1);
            else
              caller_param_offsets.push_back(static_cast<int>(off));
          }
        }
        llvm::DenseMap<unsigned, std::string> caller_hidden_seed_exprs;
        if (auto attr = F.getFnAttribute("omill.export_entry_seed_exprs");
            attr.isValid() && attr.isStringAttribute()) {
          caller_hidden_seed_exprs =
              parseHiddenSeedExprMap(attr.getValueAsString());
        }
        auto getCallerParamValue = [&](llvm::IRBuilder<> &Builder,
                                       unsigned arg_index) -> llvm::Value * {
          if (arg_index >= F.arg_size())
            return llvm::ConstantInt::get(i64_ty, 0);
          auto *arg = F.getArg(arg_index);
          if (arg->getType()->isPointerTy()) {
            return Builder.CreatePtrToInt(arg, i64_ty,
                                          arg->getName() + ".i64");
          }
          if (arg->getType()->isIntegerTy(64))
            return arg;
          if (arg->getType()->isIntegerTy())
            return Builder.CreateIntCast(arg, i64_ty, false,
                                         arg->getName() + ".i64");
          return llvm::ConstantInt::get(i64_ty, 0);
        };

        std::function<llvm::Value *(llvm::IRBuilder<> &, llvm::StringRef)>
            evalSeedExpr;
        evalSeedExpr = [&](llvm::IRBuilder<> &Builder,
                           llvm::StringRef text) -> llvm::Value * {
          text = text.trim();
          if (text.starts_with("param(") && text.ends_with(")")) {
            unsigned idx = 0;
            if (!text.drop_front(6).drop_back().getAsInteger(10, idx))
              return getCallerParamValue(Builder, idx);
            return nullptr;
          }
          if (text.starts_with("const(") && text.ends_with(")")) {
            auto body = text.drop_front(6).drop_back();
            uint64_t value = 0;
            if (body.starts_with("0x")) {
              if (!body.drop_front(2).getAsInteger(16, value))
                return llvm::ConstantInt::get(i64_ty, value);
            } else if (!body.getAsInteger(10, value)) {
              return llvm::ConstantInt::get(i64_ty, value);
            }
            return nullptr;
          }

          auto parseCallArgs = [&](llvm::StringRef body)
              -> std::optional<std::pair<llvm::StringRef, llvm::StringRef>> {
            int depth = 0;
            for (size_t idx = 0; idx < body.size(); ++idx) {
              char c = body[idx];
              if (c == '(')
                ++depth;
              else if (c == ')')
                --depth;
              else if (c == ',' && depth == 0) {
                return std::pair(body.take_front(idx),
                                 body.drop_front(idx + 1));
              }
            }
            return std::nullopt;
          };

          auto evalUnary = [&](llvm::StringRef op) -> llvm::Value * {
            if (!text.starts_with(op) || !text.ends_with(")"))
              return nullptr;
            auto arg = text.drop_front(op.size()).drop_back();
            auto *v = evalSeedExpr(Builder, arg);
            if (!v)
              return nullptr;
            return Builder.CreateAnd(v,
                                     llvm::ConstantInt::get(i64_ty,
                                                            0xffffffffull));
          };

          auto evalBinary = [&](llvm::StringRef op,
                                auto &&fn) -> llvm::Value * {
            if (!text.starts_with(op) || !text.ends_with(")"))
              return nullptr;
            auto body = text.drop_front(op.size()).drop_back();
            auto parts = parseCallArgs(body);
            if (!parts)
              return nullptr;
            auto *lhs = evalSeedExpr(Builder, parts->first);
            auto *rhs = evalSeedExpr(Builder, parts->second);
            if (!lhs || !rhs)
              return nullptr;
            return fn(lhs, rhs);
          };

          if (auto *v = evalUnary("zext32("))
            return v;
          if (auto *v = evalBinary("add64(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     return Builder.CreateAdd(lhs, rhs);
                                   }))
            return v;
          if (auto *v = evalBinary("xor64(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     return Builder.CreateXor(lhs, rhs);
                                   }))
            return v;
          if (auto *v = evalBinary("xor32(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     auto *x = Builder.CreateXor(lhs, rhs);
                                     return Builder.CreateAnd(
                                         x,
                                         llvm::ConstantInt::get(i64_ty,
                                                                0xffffffffull));
                                   }))
            return v;
          if (auto *v = evalBinary("and32(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     auto *x = Builder.CreateAnd(lhs, rhs);
                                     return Builder.CreateAnd(
                                         x,
                                         llvm::ConstantInt::get(i64_ty,
                                                                0xffffffffull));
                                   }))
            return v;
          return nullptr;
        };

        if (is_requested_export_native_root && !caller_hidden_seed_exprs.empty() &&
            !F.empty()) {
          llvm::SmallDenseSet<unsigned, 8> rewritten_root_seed_offsets;
          for (auto &I : llvm::make_early_inc_range(F.front())) {
            auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
            if (!SI || !SI->getValueOperand()->getType()->isIntegerTy(64))
              continue;
            auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(
                SI->getPointerOperand()->stripPointerCasts());
            if (!gep || gep->getNumIndices() != 1)
              continue;
            auto *idx_ci =
                llvm::dyn_cast<llvm::ConstantInt>(gep->idx_begin()->get());
            if (!idx_ci)
              continue;
            unsigned target_off = static_cast<unsigned>(idx_ci->getZExtValue());
            auto it = caller_hidden_seed_exprs.find(target_off);
            if (it == caller_hidden_seed_exprs.end())
              continue;
            llvm::IRBuilder<> Builder(SI);
            if (auto *seed_value = evalSeedExpr(Builder, it->second)) {
              SI->setOperand(0, seed_value);
              rewritten_root_seed_offsets.insert(target_off);
              ++fixup_count;
              if (debug_public_root_seeds) {
                errs() << "[post-abi-fixup] rewrote-root-seed-store fn="
                       << F.getName() << " offset=" << target_off
                       << " expr=" << it->second << "\n";
              }
            }
          }

          llvm::Instruction *insertion_point = nullptr;
          for (auto &I : F.front()) {
            if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
              if (auto *callee = CB->getCalledFunction();
                  callee && !callee->isDeclaration()) {
                insertion_point = &I;
                break;
              }
            }
          }
          if (!insertion_point)
            insertion_point = F.front().getTerminator();

          llvm::Value *state_ptr = nullptr;
          for (auto &I : F.front()) {
            auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
            if (!AI)
              continue;
            if (AI->getAllocatedType()->isStructTy() &&
                AI->getAllocatedType()->getStructName().contains("State")) {
              state_ptr = AI;
              break;
            }
          }

          if (state_ptr && insertion_point) {
            for (const auto &entry : caller_hidden_seed_exprs) {
              unsigned target_off = entry.first;
              if (rewritten_root_seed_offsets.count(target_off))
                continue;
              llvm::IRBuilder<> Builder(insertion_point);
              auto *offset_ptr = Builder.CreateInBoundsGEP(
                  Builder.getInt8Ty(), state_ptr, Builder.getInt64(target_off),
                  F.getName() + ".seed.ptr");
              if (auto *seed_value = evalSeedExpr(Builder, entry.second)) {
                Builder.CreateStore(seed_value, offset_ptr);
                rewritten_root_seed_offsets.insert(target_off);
                ++fixup_count;
                if (debug_public_root_seeds) {
                  errs() << "[post-abi-fixup] inserted-root-seed-store fn="
                         << F.getName() << " offset=" << target_off
                         << " expr=" << entry.second << "\n";
                }
              }
            }
          }
        }
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI) continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (!callee || !callee->getName().ends_with("_native"))
              continue;
            if (debug_public_root_seeds) {
              errs() << "[post-abi-fixup] consider-call caller=" << F.getName()
                     << " callee=" << callee->getName()
                     << " call_args=" << CI->arg_size()
                     << " callee_args=" << callee->arg_size() << "\n";
            }
            if (callee->hasFnAttribute("omill.vm_handler") &&
                (F.hasFnAttribute("omill.vm_wrapper") ||
                 F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()))
              continue;
            auto callHasSuspiciousSameArityOperands = [&]() {
              for (unsigned i = 0; i < CI->arg_size(); ++i) {
                auto *arg = CI->getArgOperand(i);
                if (llvm::isa<llvm::PoisonValue>(arg) ||
                    llvm::isa<llvm::UndefValue>(arg))
                  return true;
              }
              return false;
            };
            bool allow_same_arity_rewrite =
                (!caller_hidden_seed_exprs.empty() &&
                 is_requested_export_native_root) ||
                callHasSuspiciousSameArityOperands();
            if (debug_public_root_seeds &&
                is_requested_export_native_root &&
                callee->getName().ends_with("_native")) {
              errs() << "[post-abi-fixup] caller=" << F.getName()
                     << " callee=" << callee->getName()
                     << " same_arity=" << (CI->arg_size() == callee->arg_size())
                     << " allow_same_arity=" << allow_same_arity_rewrite
                     << " caller_hidden_seeds="
                     << caller_hidden_seed_exprs.size() << "\n";
            }
            if (CI->arg_size() == callee->arg_size() &&
                !allow_same_arity_rewrite)
              continue;

            auto attr =
                callee->getFnAttribute("omill.param_state_offsets");
            if (!attr.isValid() || !attr.isStringAttribute()) continue;

            llvm::SmallVector<llvm::StringRef, 16> callee_offset_strs;
            attr.getValueAsString().split(callee_offset_strs, ',');
            if (callee_offset_strs.size() != callee->arg_size()) continue;

            auto defaultMissingI64Arg = [&]() -> llvm::Value * {
              // Late ABI call repair should fail conservatively. Using poison
              // here turns unmapped helper params into immediate UB in the
              // final recovered artifact, which is worse than preserving a
              // deterministic zero/default state.
              return llvm::ConstantInt::get(i64_ty, 0);
            };

            // Match each callee param to a B3 arg by State offset.
            llvm::SmallVector<llvm::Value *, 16> new_args;
            bool ok = true;
            llvm::IRBuilder<> Builder(CI);
            for (auto &off_str : callee_offset_strs) {
              if (off_str == "stack" || off_str == "xmm") {
                if (new_args.size() < CI->arg_size())
                  new_args.push_back(CI->getArgOperand(new_args.size()));
                else
                  new_args.push_back(defaultMissingI64Arg());
                continue;
              }
              unsigned target_off;
              if (off_str.getAsInteger(10, target_off)) {
                ok = false;
                break;
              }
              bool found = false;
              if (is_requested_export_native_root) {
                for (unsigned i = 0;
                     i < caller_param_offsets.size() && i < F.arg_size(); ++i) {
                  if (caller_param_offsets[i] ==
                      static_cast<int>(target_off)) {
                    new_args.push_back(F.getArg(i));
                    found = true;
                    break;
                  }
                }
                if (auto it = caller_hidden_seed_exprs.find(target_off);
                    it != caller_hidden_seed_exprs.end()) {
                  if (auto *seed_value = evalSeedExpr(Builder, it->second)) {
                    new_args.push_back(seed_value);
                    found = true;
                  }
                }
              } else {
                for (unsigned i = 0;
                     i < b3_arg_offsets.size() && i < CI->arg_size(); ++i) {
                  if (b3_arg_offsets[i] == target_off) {
                    new_args.push_back(CI->getArgOperand(i));
                    found = true;
                    break;
                  }
                }
                if (!found) {
                  for (unsigned i = 0;
                       i < caller_param_offsets.size() && i < F.arg_size();
                       ++i) {
                    if (caller_param_offsets[i] ==
                        static_cast<int>(target_off)) {
                      new_args.push_back(F.getArg(i));
                      found = true;
                      break;
                    }
                  }
                }
                if (!found) {
                  if (auto it = caller_hidden_seed_exprs.find(target_off);
                      it != caller_hidden_seed_exprs.end()) {
                    if (auto *seed_value = evalSeedExpr(Builder, it->second)) {
                      new_args.push_back(seed_value);
                      found = true;
                    }
                  }
                }
              }
              if (!found) {
                if (new_args.size() < CI->arg_size())
                  new_args.push_back(CI->getArgOperand(new_args.size()));
                else
                  new_args.push_back(defaultMissingI64Arg());
              }
            }
            if (!ok) continue;

            bool changed_args = (CI->arg_size() != new_args.size());
            if (!changed_args && CI->arg_size() == new_args.size()) {
              for (unsigned i = 0; i < CI->arg_size(); ++i) {
                if (new_args[i] != CI->getArgOperand(i)) {
                  changed_args = true;
                  break;
                }
              }
            }
            if (!changed_args)
              continue;

            if (debug_public_root_seeds &&
                is_requested_export_native_root) {
              errs() << "[post-abi-fixup] rewriting caller=" << F.getName()
                     << " callee=" << callee->getName()
                     << " args=" << CI->arg_size() << "\n";
            }

            for (unsigned i = 0; i < new_args.size() && i < CI->arg_size(); ++i) {
              auto *current = CI->getArgOperand(i);
              auto *replacement = new_args[i];
              if (replacement->getType() == current->getType())
                continue;
              if (replacement->getType()->isIntegerTy() &&
                  current->getType()->isIntegerTy()) {
                new_args[i] = Builder.CreateIntCast(
                    replacement, current->getType(), false,
                    callee->getName() + ".arg.cast");
              } else if (replacement->getType()->isPointerTy() &&
                         current->getType()->isIntegerTy()) {
                new_args[i] = Builder.CreatePtrToInt(
                    replacement, current->getType(),
                    callee->getName() + ".arg.pti");
              } else if (replacement->getType()->isIntegerTy() &&
                         current->getType()->isPointerTy()) {
                new_args[i] = Builder.CreateIntToPtr(
                    replacement, current->getType(),
                    callee->getName() + ".arg.itp");
              }
            }

            auto *new_call = llvm::CallInst::Create(
                callee->getFunctionType(), callee, new_args,
                callee->getReturnType()->isVoidTy() ? "" : CI->getName(),
                CI->getIterator());
            new_call->setCallingConv(CI->getCallingConv());
            new_call->setAttributes(CI->getAttributes());
            // Handle return type mismatch (B3 returns i64, callee may
            // return struct).
            if (!CI->use_empty()) {
              if (CI->getType() == new_call->getType()) {
                CI->replaceAllUsesWith(new_call);
              } else if (llvm::isa<llvm::StructType>(
                             new_call->getType())) {
                auto *ev = llvm::ExtractValueInst::Create(
                    new_call, {0}, "ret.primary",
                    std::next(new_call->getIterator()));
                CI->replaceAllUsesWith(ev);
              } else {
                CI->replaceAllUsesWith(
                    llvm::PoisonValue::get(CI->getType()));
              }
            }
            CI->eraseFromParent();
            ++fixup_count;
          }
        }
      }
      if (fixup_count > 0)
        errs() << "Fixed " << fixup_count
               << " B3 dispatch calls with mismatched arg counts\n";
    };
    if (!parseBoolEnv("OMILL_SKIP_ABI_POSTPATCH_B3_FIXUP").value_or(false)) {
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:start\n";
      fixupB3DispatchArgMismatches();
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:end\n";
    }
    auto repairSyntheticStackTopStateArgs = [&]() {
      auto syntheticStateArgIndex = [&](llvm::Function &Callee)
          -> std::optional<unsigned> {
        for (unsigned i = 0; i < Callee.arg_size(); ++i) {
          auto *arg = Callee.getArg(i);
          for (auto *U : arg->users()) {
            auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
            if (!BO || BO->getOpcode() != llvm::Instruction::Add)
              continue;
            auto *lhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
            auto *rhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
            if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
                (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
              return i;
            }
          }
        }
        return std::nullopt;
      };

      auto rebuildSyntheticStackBase = [&](llvm::Value *V,
                                           llvm::IRBuilder<> &Builder)
          -> llvm::Value * {
        auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(V);
        if (!PTI)
          return nullptr;
        auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(
            PTI->getPointerOperand()->stripPointerCasts());
        if (!GEP || GEP->getNumOperands() < 2)
          return nullptr;
        auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
        if (!idx || idx->getZExtValue() < 65504)
          return nullptr;
        auto *base_ptr = GEP->getPointerOperand();
        return Builder.CreatePtrToInt(base_ptr, V->getType(),
                                      "synthetic.stack.base");
      };

      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native"))
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            auto *Callee = CI ? CI->getCalledFunction() : nullptr;
            if (!Callee || Callee->isDeclaration() ||
                !Callee->getName().ends_with("_native")) {
              continue;
            }
            if (Callee == &F || Callee->getName() == F.getName())
              continue;
            auto state_arg_index = syntheticStateArgIndex(*Callee);
            if (!state_arg_index || *state_arg_index >= CI->arg_size())
              continue;
            llvm::IRBuilder<> Builder(CI);
            auto *replacement = rebuildSyntheticStackBase(
                CI->getArgOperand(*state_arg_index), Builder);
            if (!replacement)
              continue;
            CI->setArgOperand(*state_arg_index, replacement);
          }
        }
      }
    };

    auto materializeZeroedSyntheticStateArgs = [&]() {
      auto syntheticStateArgIndex = [&](llvm::Function &Callee)
          -> std::optional<unsigned> {
        for (unsigned i = 0; i < Callee.arg_size(); ++i) {
          auto *arg = Callee.getArg(i);
          for (auto *U : arg->users()) {
            auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
            if (!BO || BO->getOpcode() != llvm::Instruction::Add)
              continue;
            auto *lhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
            auto *rhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
            if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
                (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
              return i;
            }
          }
        }
        return std::nullopt;
      };

      constexpr uint64_t kSyntheticStateBytes = 69632;
      auto *stack_ty = llvm::ArrayType::get(
          llvm::Type::getInt8Ty(ctx), kSyntheticStateBytes);

      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native") ||
            F.empty()) {
          continue;
        }
        auto &entry = F.getEntryBlock();
        llvm::Instruction *entry_ip = &*entry.getFirstInsertionPt();
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            auto *Callee = CI ? CI->getCalledFunction() : nullptr;
            if (!Callee || Callee->isDeclaration() ||
                !Callee->getName().ends_with("_native")) {
              continue;
            }
            if (Callee == &F || Callee->getName() == F.getName())
              continue;
            auto state_arg_index = syntheticStateArgIndex(*Callee);
            if (!state_arg_index || *state_arg_index >= CI->arg_size())
              continue;
            auto *zero_ci =
                llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(*state_arg_index));
            if (!zero_ci || !zero_ci->isZero())
              continue;

            llvm::IRBuilder<> EntryBuilder(entry_ip);
            auto *alloca = EntryBuilder.CreateAlloca(
                stack_ty, nullptr,
                Callee->getName() + ".synthetic_state");

            llvm::IRBuilder<> Builder(CI);
            Builder.CreateMemSet(alloca, Builder.getInt8(0),
                                 kSyntheticStateBytes, llvm::MaybeAlign(16));
            auto *replacement = Builder.CreatePtrToInt(
                alloca, CI->getArgOperand(*state_arg_index)->getType(),
                Callee->getName() + ".synthetic_state.i64");
            CI->setArgOperand(*state_arg_index, replacement);
          }
        }
      }
    };

    rerunLateNativeArgRepair = [&]() {
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:late-rerun:start\n";
      fixupB3DispatchArgMismatches();
      repairSyntheticStackTopStateArgs();
      materializeZeroedSyntheticStateArgs();
      repairMalformedPHIs(*module);
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:late-rerun:end\n";
    };

    {
      rerunFocusedNativeHelperControlFlowRecovery = [&]() {
      auto in_output_root_native_closure = [&](llvm::Function &Candidate) {
        if (Candidate.isDeclaration() || !Candidate.getName().ends_with("_native"))
          return false;

        llvm::SmallVector<llvm::Function *, 32> worklist;
        llvm::SmallPtrSet<llvm::Function *, 32> seen;
        for (auto &F : *module) {
          if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
              !F.getName().ends_with("_native")) {
            continue;
          }
          if (seen.insert(&F).second)
            worklist.push_back(&F);
        }

        while (!worklist.empty()) {
          llvm::Function *Current = worklist.pop_back_val();
          if (Current == &Candidate)
            return true;
          for (auto &BB : *Current) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!CB)
                continue;
              auto *Callee = CB->getCalledFunction();
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
      };

      auto needs_recovery = [&](llvm::Function &F) {
        if (!in_output_root_native_closure(F))
          return false;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *Callee = CB->getCalledFunction();
            if (!Callee)
              continue;
            auto Name = Callee->getName();
            if (omill::isDispatchIntrinsicName(Name) ||
                Name == "__remill_function_return") {
              return true;
            }
          }
        }
        return false;
      };

      bool has_candidates = false;
      for (auto &F : *module) {
        if (needs_recovery(F)) {
          has_candidates = true;
          break;
        }
      }
      if (!has_candidates)
        return;

      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] focused-native-cf-recovery:start\n";

      llvm::ModulePassManager FocusedMPM;
      FocusedMPM.addPass(
          llvm::RequireAnalysisPass<omill::LiftedFunctionAnalysis,
                                    llvm::Module>());
      llvm::FunctionPassManager FPM;
      FPM.addPass(
          omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Phase3));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(omill::JumpTableConcretizerPass());
      FPM.addPass(omill::ResolveAndLowerControlFlowPass(
          omill::ResolvePhases::RecoverTables |
          omill::ResolvePhases::SymbolicSolve |
          omill::ResolvePhases::ResolveTargets));
      FPM.addPass(omill::LowerRemillIntrinsicsPass(
          omill::LowerCategories::ResolvedDispatch));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      FocusedMPM.addPass(
          llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      FocusedMPM.run(*module, MAM);

      auto canonicalizeDispatchDecl = [&](llvm::StringRef dispatch_name,
                                          llvm::StringRef remill_name) {
        auto *dispatch = module->getFunction(dispatch_name);
        auto *remill = module->getFunction(remill_name);
        if (!dispatch || !remill)
          return;
        auto *expected_ty = remill->getFunctionType();
        if (dispatch->getFunctionType() == expected_ty)
          return;

        auto *replacement = llvm::Function::Create(
            expected_ty, dispatch->getLinkage(), dispatch_name + ".fixed",
            module.get());
        replacement->copyAttributesFrom(dispatch);

        llvm::SmallVector<llvm::CallBase *, 16> calls;
        for (auto *U : dispatch->users()) {
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
            calls.push_back(CB);
        }

        for (auto *CB : calls) {
          llvm::IRBuilder<> Builder(CB);
          llvm::SmallVector<llvm::Value *, 8> args;
          args.reserve(CB->arg_size());
          for (auto &Arg : CB->args())
            args.push_back(Arg.get());
          auto *new_call = Builder.CreateCall(expected_ty, replacement, args);
          new_call->setCallingConv(CB->getCallingConv());
          new_call->setAttributes(CB->getAttributes());
          if (!CB->use_empty()) {
            if (new_call->getType() == CB->getType()) {
              CB->replaceAllUsesWith(new_call);
            } else if (!CB->getType()->isVoidTy()) {
              CB->replaceAllUsesWith(
                  llvm::PoisonValue::get(CB->getType()));
            }
          }
          CB->eraseFromParent();
        }

        dispatch->eraseFromParent();
        replacement->setName(dispatch_name);
      };

      canonicalizeDispatchDecl("__omill_dispatch_jump", "__remill_jump");
      canonicalizeDispatchDecl("__omill_dispatch_call", "__remill_function_call");

      auto rewriteVoidNativeJumpTableDispatches = [&]() {
        auto parseNativeTargetPC = [&](llvm::StringRef name) -> uint64_t {
          if (uint64_t pc = omill::extractEntryVA(name); pc != 0)
            return pc;
          auto parsePrefixedHex = [&](llvm::StringRef prefix) -> uint64_t {
            if (!name.starts_with(prefix))
              return 0;
            auto rest = name.drop_front(prefix.size());
            size_t hex_len = 0;
            while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
              ++hex_len;
            if (hex_len == 0)
              return 0;
            uint64_t pc = 0;
            if (rest.substr(0, hex_len).getAsInteger(16, pc))
              return 0;
            return pc;
          };
          if (uint64_t pc = parsePrefixedHex("blk_"); pc != 0)
            return pc;
          if (uint64_t pc = parsePrefixedHex("block_"); pc != 0)
            return pc;
          return 0;
        };

        llvm::DenseMap<uint64_t, llvm::Function *> local_native_targets;
        llvm::SmallDenseSet<uint64_t, 16> local_case_pcs;
        for (auto &F : *module) {
          if (F.isDeclaration() || !F.getName().ends_with("_native") ||
              !in_output_root_native_closure(F)) {
            continue;
          }
          if (uint64_t pc = parseNativeTargetPC(F.getName()); pc != 0)
            local_native_targets[pc] = &F;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *SI = llvm::dyn_cast<llvm::SwitchInst>(&I);
              if (!SI || !SI->getCondition()->getType()->isIntegerTy(64))
                continue;
              for (auto &Case : SI->cases())
                local_case_pcs.insert(Case.getCaseValue()->getZExtValue());
            }
          }
        }

        auto findLocalNativeTarget = [&](uint64_t case_pc)
            -> llvm::Function * {
          if (auto it = local_native_targets.find(case_pc);
              it != local_native_targets.end()) {
            return it->second;
          }
          llvm::Function *best = nullptr;
          uint64_t best_distance = UINT64_MAX;
          for (auto &[target_pc, target_fn] : local_native_targets) {
            uint64_t distance =
                target_pc > case_pc ? (target_pc - case_pc) : (case_pc - target_pc);
            if (distance > 0x80)
              continue;
            if (distance < best_distance) {
              best_distance = distance;
              best = target_fn;
            }
          }
          return best;
        };

        auto findStateOffsetPtr = [&](llvm::Function &F, uint64_t offset)
            -> llvm::Value * {
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
              if (!GEP || GEP->getNumOperands() < 2)
                continue;
              auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
              if (!idx || idx->getZExtValue() != offset)
                continue;
              return GEP;
            }
          }
          return nullptr;
        };

        unsigned rewrite_count = 0;
        for (auto &F : *module) {
          if (F.isDeclaration() || !F.getName().ends_with("_native") ||
              !in_output_root_native_closure(F) || !F.getReturnType()->isVoidTy()) {
            continue;
          }

          bool already_rewritten = false;
          for (auto &BB : F) {
            auto BBName = BB.getName();
            if (BBName.starts_with("resolved.dispatch") ||
                BBName.starts_with("resolved.case.") ||
                BBName.starts_with("resolved.selfloop.")) {
              already_rewritten = true;
              break;
            }
          }
          if (already_rewritten)
            continue;

          llvm::CallBase *dispatch_call = nullptr;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              auto *Callee = CB ? CB->getCalledFunction() : nullptr;
              if (!Callee)
                continue;
              auto Name = Callee->getName();
              if (omill::isDispatchJumpName(Name)) {
                dispatch_call = CB;
                break;
              }
            }
            if (dispatch_call)
              break;
          }
          if (!dispatch_call)
            continue;

          auto *eax_ptr = findStateOffsetPtr(F, 2216);
          auto *arg2232_ptr = findStateOffsetPtr(F, 2232);
          auto *arg2280_ptr = findStateOffsetPtr(F, 2280);
          auto *arg2296_ptr = findStateOffsetPtr(F, 2296);
          auto *arg2328_ptr = findStateOffsetPtr(F, 2328);
          auto *arg2408_ptr = findStateOffsetPtr(F, 2408);
          auto *arg2440_ptr = findStateOffsetPtr(F, 2440);
          auto *arg2456_ptr = findStateOffsetPtr(F, 2456);
          if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
              !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
            continue;
          }

          auto *switch_block = dispatch_call->getParent();
          auto *target_pc = dispatch_call->getArgOperand(1);
          auto *after_block =
              switch_block->splitBasicBlock(dispatch_call->getIterator(),
                                           "resolved.dispatch.dynamic");
          switch_block->getTerminator()->eraseFromParent();
          dispatch_call->eraseFromParent();

          llvm::IRBuilder<> Builder(switch_block);
          auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                               "tb.state2232");
          auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                               "tb.state2280");
          auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                               "tb.state2328");
          auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                               "tb.state2440");
          auto *switch_inst =
              Builder.CreateSwitch(target_pc, after_block, local_case_pcs.size());

          auto buildStateArgsForCallee =
              [&](llvm::IRBuilder<> &CaseBuilder, llvm::Function &Callee) {
                llvm::SmallVector<llvm::Value *, 16> args;
                auto attr = Callee.getFnAttribute("omill.param_state_offsets");
                if (!attr.isValid() || !attr.isStringAttribute()) {
                  if (Callee.arg_size() >= 1)
                    args.push_back(state2232);
                  if (Callee.arg_size() >= 2)
                    args.push_back(state2280);
                  if (Callee.arg_size() >= 3)
                    args.push_back(state2328);
                  if (Callee.arg_size() >= 4)
                    args.push_back(state2440);
                  while (args.size() < Callee.arg_size())
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                  return args;
                }

                llvm::SmallVector<llvm::StringRef, 16> offset_strs;
                attr.getValueAsString().split(offset_strs, ',');
                if (offset_strs.size() != Callee.arg_size()) {
                  while (args.size() < Callee.arg_size())
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                  return args;
                }

                for (auto token : offset_strs) {
                  token = token.trim();
                  if (token == "stack" || token == "xmm") {
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                    continue;
                  }
                  unsigned offset = 0;
                  if (token.getAsInteger(10, offset)) {
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                    continue;
                  }
                  auto *state_ptr = findStateOffsetPtr(F, offset);
                  if (!state_ptr) {
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                    continue;
                  }
                  args.push_back(CaseBuilder.CreateLoad(Builder.getInt64Ty(),
                                                        state_ptr,
                                                        "resolved.arg." + token));
                }
                return args;
              };

          for (uint64_t case_pc : local_case_pcs) {
            if (case_pc == 0)
              continue;
            if (auto *target_fn = findLocalNativeTarget(case_pc)) {
              auto *case_block = llvm::BasicBlock::Create(
                  ctx, "resolved.case." + llvm::utohexstr(case_pc), &F,
                  after_block);
              llvm::IRBuilder<> case_builder(case_block);
              auto case_args = buildStateArgsForCallee(case_builder, *target_fn);
              auto *case_call = case_builder.CreateCall(
                  target_fn->getFunctionType(), target_fn, case_args);
              case_call->setCallingConv(target_fn->getCallingConv());
              if (auto *CaseRetST =
                      llvm::dyn_cast<llvm::StructType>(target_fn->getReturnType());
                  CaseRetST && CaseRetST->getNumElements() == 8) {
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {0}), eax_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {1}), arg2232_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {2}), arg2328_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {3}), arg2296_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {4}), arg2280_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {5}), arg2408_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {6}), arg2440_ptr);
                case_builder.CreateStore(
                    case_builder.CreateExtractValue(case_call, {7}), arg2456_ptr);
              }
              case_builder.CreateBr(after_block);
              switch_inst->addCase(case_builder.getInt64(case_pc), case_block);
            } else {
              auto *loop_block = llvm::BasicBlock::Create(
                  ctx, "resolved.selfloop." + llvm::utohexstr(case_pc), &F,
                  after_block);
              llvm::IRBuilder<> loop_builder(loop_block);
              loop_builder.CreateBr(loop_block);
              switch_inst->addCase(loop_builder.getInt64(case_pc), loop_block);
            }
          }

          ++rewrite_count;
        }

        if (rewrite_count > 0 &&
            parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
          errs() << "[abi-post] void-native-jumptable-rewrite count="
                 << rewrite_count << "\n";
        }
      };
      rewriteVoidNativeJumpTableDispatches();

      if (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr) {
        std::error_code ec;
        llvm::raw_fd_ostream os("after_focused_native_cf_recovery.ll", ec,
                                llvm::sys::fs::OF_Text);
        if (!ec)
          module->print(os, nullptr);
      }

      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] focused-native-cf-recovery:end\n";
      };
      rerunFocusedNativeHelperControlFlowRecovery();
    }

    dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_ABI_POSTPATCH",
                           "after_abi_postpatch.ll");
    if (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr) {
      std::error_code ec;
      llvm::raw_fd_ostream os("after_b3_fixup.ll", ec, llvm::sys::fs::OF_Text);
      if (!ec)
        module->print(os, nullptr);
    }

    if (enable_debug_sample_native_fixups) {
      if (auto *flattened_root = module->getFunction("sub_1800020e0_native");
          flattened_root && !flattened_root->isDeclaration()) {
        if (auto *flattened_case301 =
                module->getFunction("sub_180002301_native");
            flattened_case301 && !flattened_case301->isDeclaration()) {
          flattened_case301->removeFnAttr(llvm::Attribute::AlwaysInline);
          flattened_case301->addFnAttr(llvm::Attribute::NoInline);
        }
      }
    }

#endif
    auto shouldRunPostABIDeobfOn = [&](llvm::Function &F) {
      if (F.isDeclaration())
        return false;
      return F.hasFnAttribute("omill.output_root") ||
             F.hasFnAttribute("omill.closed_root_slice");
    };

    // Post-ABI deobfuscation runs directly on the canonical recovered roots.
    if (Deobfuscate || ResolveTargets) {
      llvm::FunctionPassManager FPM;
      omill::buildDeobfuscationPipeline(FPM, opts);
      for (auto &F : *module) {
        if (!shouldRunPostABIDeobfOn(F))
          continue;
        auto &FAM =
            MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(*module)
                .getManager();
        auto PA = FPM.run(F, FAM);
        if (!PA.areAllPreserved())
          FAM.invalidate(F, PA);
      }
      errs() << "Post-ABI deobfuscation complete\n";
      events.emitInfo("post_abi_deobf_completed", "post-ABI deobfuscation completed");
      dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_POST_ABI_DEOBF",
                             "after_post_abi_deobf.ll");
      rerunFocusedNativeHelperControlFlowRecovery();
    }

    rerunLateOutputRootTargetPipeline();

    [[maybe_unused]] auto patchTraceNativeWrapperCalls = [&]() {
      if (!vm_mode || !vm_graph || vm_graph->empty())
        return;

      auto parseHashAttr = [&](llvm::Function &F,
                               llvm::StringRef attr_name)
          -> std::optional<uint64_t> {
        auto attr = F.getFnAttribute(attr_name);
        if (!attr.isValid() || !attr.isStringAttribute())
          return std::nullopt;
        uint64_t value = 0;
        auto text = attr.getValueAsString();
        if (text.getAsInteger(16, value))
          return std::nullopt;
        return value;
      };

      auto parseNativeVA = [&](llvm::Function &F) -> std::optional<uint64_t> {
        if (!F.getName().ends_with("_native"))
          return std::nullopt;
        auto base_name = F.getName().drop_back(strlen("_native"));
        if (!base_name.starts_with("sub_"))
          return std::nullopt;
        uint64_t va = 0;
        if (base_name.drop_front(4).getAsInteger(16, va) || va == 0)
          return std::nullopt;
        return va;
      };

      unsigned patched = 0;
      unsigned skipped = 0;
      for (auto &F : *module) {
        if (F.isDeclaration() || !F.hasFnAttribute("omill.vm_wrapper"))
          continue;
        auto wrapper_va = parseNativeVA(F);
        if (!wrapper_va)
          continue;

        std::optional<uint64_t> seed_hash =
            parseHashAttr(F, "omill.vm_trace_in_hash");
        if (!seed_hash) {
          auto records = vm_graph->getTraceRecords(*wrapper_va);
          if (records.size() == 1)
            seed_hash = records.front().incoming_hash;
        }
        if (!seed_hash) {
          errs() << "Trace-native patch: no seed hash for " << F.getName()
                 << "\n";
          continue;
        }

        auto flat = vm_graph->followFlatTrace(*wrapper_va, *seed_hash);
        llvm::SmallVector<uint64_t, 4> trace_native_targets;
        for (const auto &record : flat.records) {
          if (record.native_target_va != 0)
            trace_native_targets.push_back(record.native_target_va);
        }
        if (trace_native_targets.empty()) {
          errs() << "Trace-native patch: wrapper " << F.getName()
                 << " seed=0x" << Twine::utohexstr(*seed_hash)
                 << " flat_records=" << flat.records.size()
                 << " stop_reason=" << static_cast<unsigned>(flat.stop_reason)
                 << " produced no native targets\n";
          continue;
        }

        llvm::SmallVector<llvm::CallInst *, 4> indirect_calls;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            if (llvm::isa<llvm::Function>(
                    CI->getCalledOperand()->stripPointerCasts()))
              continue;
            indirect_calls.push_back(CI);
          }
        }
        if (indirect_calls.empty()) {
          errs() << "Trace-native patch: wrapper " << F.getName()
                 << " has no indirect calls to rewrite\n";
          continue;
        }
        if (indirect_calls.size() != trace_native_targets.size()) {
          errs() << "Trace-native patch skipped for " << F.getName()
                 << " (indirect_calls=" << indirect_calls.size()
                 << ", trace_native_targets=" << trace_native_targets.size()
                 << ")\n";
          ++skipped;
          continue;
        }

        for (unsigned i = 0; i < indirect_calls.size(); ++i) {
          uint64_t target_va = trace_native_targets[i];
          std::string target_name =
              "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
          auto *target_fn = module->getFunction(target_name);
          if (!target_fn || target_fn->isDeclaration()) {
            errs() << "Trace-native patch missing target " << target_name
                   << " for wrapper " << F.getName() << "\n";
            break;
          }

          auto *CI = indirect_calls[i];
          llvm::SmallVector<llvm::Value *, 16> args;
          for (auto &Arg : CI->args())
            args.push_back(Arg.get());

          llvm::IRBuilder<> Builder(CI);
          llvm::Value *direct_callee = target_fn;
          if (target_fn->getType() != CI->getCalledOperand()->getType()) {
            direct_callee = Builder.CreateBitCast(
                target_fn, CI->getCalledOperand()->getType(),
                target_name + ".cast");
          }
          auto *new_call = Builder.CreateCall(
              CI->getFunctionType(), direct_callee, args, CI->getName());
          new_call->setCallingConv(CI->getCallingConv());
          new_call->setAttributes(CI->getAttributes());
          if (!CI->use_empty())
            CI->replaceAllUsesWith(new_call);
          CI->eraseFromParent();
          ++patched;
        }
      }

      if (patched > 0) {
        errs() << "Patched " << patched
               << " VM wrapper indirect call(s) from imported trace\n";
        runPostPatchCleanup("trace_native_wrapper_calls");
      } else if (skipped > 0) {
        errs() << "Trace-native wrapper patch skipped " << skipped
               << " wrapper(s)\n";
      }
    };
    // Legacy wrapper cloning/patching was removed with the `_native`
    // compatibility pipeline.

    // Per-callsite specialization of VM native call targets.
    // Clone functions like sub_1400dcbf8_native per call site, bake in
    // emulator-derived GPR constants so hash-based import resolution succeeds.
    if (false && vm_mode && !native_call_infos.empty()) {
      // Build State-offset → emulator RegIdx lookup.
      // Remill GPR order in State: RAX,RBX,RCX,RDX,RSI,RDI,RSP,RBP,R8..R15.
      // x86 encoding order (EmuState): RAX=0,RCX=1,RDX=2,RBX=3,RSP=4,...
      // State offsets: each GPR at 2208 + N*16 + 8 where N is remill order.
      const unsigned kRemillGPRToRegIdx[] = {
        0,  // RAX → RegIdx 0
        3,  // RBX → RegIdx 3
        1,  // RCX → RegIdx 1
        2,  // RDX → RegIdx 2
        6,  // RSI → RegIdx 6
        7,  // RDI → RegIdx 7
        4,  // RSP → RegIdx 4
        5,  // RBP → RegIdx 5
        8,  // R8  → RegIdx 8
        9, 10, 11, 12, 13, 14, 15  // R9..R15
      };
      llvm::DenseMap<unsigned, unsigned> stateOffsetToRegIdx;
      for (unsigned i = 0; i < 16; ++i) {
        unsigned state_offset = 2208 + i * 16 + 8;
        stateOffsetToRegIdx[state_offset] = kRemillGPRToRegIdx[i];
      }

      // Find the wrapper's _native function.
      std::string wrapper_native_name =
          "sub_" + llvm::Twine::utohexstr(vm_wrapper_va).str() + "_native";
      auto *wrapper_fn = module->getFunction(wrapper_native_name);

      if (wrapper_fn && !wrapper_fn->isDeclaration()) {
        // Group NativeCallInfos by target VA.
        llvm::DenseMap<uint64_t, llvm::SmallVector<unsigned, 4>>
            target_to_info_indices;
        for (unsigned i = 0; i < native_call_infos.size(); ++i)
          target_to_info_indices[native_call_infos[i].target_va].push_back(i);

        auto *i64_ty = llvm::Type::getInt64Ty(module->getContext());

        for (auto &[target_va, info_indices] : target_to_info_indices) {
          // Only specialize targets that appear multiple times (worth cloning).
          if (info_indices.size() < 2)
            continue;

          std::string target_name =
              "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
          auto *target_fn = module->getFunction(target_name);
          if (!target_fn || target_fn->isDeclaration())
            continue;

          // Parse param_state_offsets attribute.
          auto offsets_attr =
              target_fn->getFnAttribute("omill.param_state_offsets");
          if (!offsets_attr.isValid() || !offsets_attr.isStringAttribute())
            continue;

          llvm::SmallVector<int, 16> param_reg_idx;
          llvm::StringRef offsets_str = offsets_attr.getValueAsString();
          while (!offsets_str.empty()) {
            llvm::StringRef token;
            std::tie(token, offsets_str) = offsets_str.split(',');
            if (token == "stack" || token == "xmm") {
              param_reg_idx.push_back(-1);  // Not a GPR.
            } else {
              unsigned offset = 0;
              if (token.getAsInteger(10, offset)) {
                param_reg_idx.push_back(-1);
              } else {
                auto it = stateOffsetToRegIdx.find(offset);
                if (it != stateOffsetToRegIdx.end())
                  param_reg_idx.push_back(static_cast<int>(it->second));
                else
                  param_reg_idx.push_back(-1);
              }
            }
          }

          // Determine the number of "standard" params that the caller actually
          // passes (typically 4 for Win64: RCX, RDX, R8, R9).
          unsigned num_caller_args = 0;
          for (auto &BB : *wrapper_fn) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call)
                continue;
              if (call->getCalledFunction() != target_fn)
                continue;
              num_caller_args = call->arg_size();
              goto found_call;
            }
          }
          found_call:

          // Collect all calls to the target in the wrapper (in IR order).
          llvm::SmallVector<llvm::CallInst *, 32> target_calls;
          for (auto &BB : *wrapper_fn) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call)
                continue;
              if (call->getCalledFunction() != target_fn)
                continue;
              target_calls.push_back(call);
            }
          }

          if (target_calls.size() != info_indices.size()) {
            errs() << "VM clone: call count mismatch for "
                   << target_name << " (IR: " << target_calls.size()
                   << " vs infos: " << info_indices.size() << "), skipping\n";
            continue;
          }

          errs() << "VM clone: specializing " << target_name
                 << " (" << info_indices.size() << " call sites)\n";

          // Create per-callsite clones.
          auto &FAM =
              MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(*module)
                  .getManager();

          for (unsigned ci = 0; ci < info_indices.size(); ++ci) {
            const auto &info = native_call_infos[info_indices[ci]];
            std::string clone_name = target_name + "_" + std::to_string(ci);

            // Clone the function.
            llvm::ValueToValueMapTy VMap;
            auto *clone = llvm::CloneFunction(target_fn, VMap);
            clone->setName(clone_name);
            clone->setLinkage(llvm::GlobalValue::InternalLinkage);

            // Replace extra params with emulator constants.
            for (unsigned pi = num_caller_args;
                 pi < clone->arg_size() && pi < param_reg_idx.size(); ++pi) {
              int reg_idx = param_reg_idx[pi];
              if (reg_idx < 0 || reg_idx >= 16)
                continue;
              auto *arg = clone->getArg(pi);
              arg->replaceAllUsesWith(
                  llvm::ConstantInt::get(i64_ty, info.gprs[reg_idx]));
            }

            // Inject vmcontext memory into BinaryMemoryMap.
            bool injected_vmctx = false;
            if (!info.vmcontext_snapshot.empty() && info.r12_base != 0) {
              pe.memory_map.addRegion(info.r12_base,
                                      info.vmcontext_snapshot.data(),
                                      info.vmcontext_snapshot.size(),
                                      /*read_only=*/true,
                                      /*executable=*/false);
              injected_vmctx = true;
            }

            // Targeted inlining of helper functions into this clone.
            bool inlined_any = true;
            while (inlined_any) {
              inlined_any = false;
              for (auto &BB : *clone) {
                for (auto &I : llvm::make_early_inc_range(BB)) {
                  auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
                  if (!call || !call->getCalledFunction())
                    continue;
                  auto callee_name = call->getCalledFunction()->getName();
                  // Inline VM wrapper helpers into the clone.
                  if (!callee_name.ends_with("_native") ||
                      callee_name == clone_name)
                    continue;
                  // Only inline internal helpers, not the wrapper or other
                  // clones.
                  auto *callee = call->getCalledFunction();
                  if (callee->isDeclaration())
                    continue;
                  // Skip the wrapper function itself.
                  if (callee == wrapper_fn)
                    continue;
                  llvm::InlineFunctionInfo IFI;
                  auto result = llvm::InlineFunction(*call, IFI);
                  if (result.isSuccess())
                    inlined_any = true;
                }
              }
            }

            // Run deobf pipeline on the specialized clone.
            {
              llvm::FunctionPassManager FPM;
              omill::buildDeobfuscationPipeline(FPM, opts);
              auto PA = FPM.run(*clone, FAM);
              if (!PA.areAllPreserved())
                FAM.invalidate(*clone, PA);
            }

            // Remove injected vmcontext region.
            if (injected_vmctx)
              pe.memory_map.removeRegion(info.r12_base);

            // Update the wrapper's call to point to the clone.
            auto *orig_call = target_calls[ci];
            // Build args matching the clone's signature (only the first
            // num_caller_args, since extra params are baked in).
            llvm::SmallVector<llvm::Value *, 4> clone_args;
            for (unsigned ai = 0; ai < num_caller_args; ++ai)
              clone_args.push_back(orig_call->getArgOperand(ai));

            llvm::IRBuilder<> Builder(orig_call);
            auto *clone_call =
                Builder.CreateCall(clone, clone_args, clone_name + ".result");
            clone_call->setCallingConv(orig_call->getCallingConv());
            clone_call->setAttributes(orig_call->getAttributes());
            orig_call->replaceAllUsesWith(clone_call);
            orig_call->eraseFromParent();
          }

          errs() << "VM clone: created " << info_indices.size()
                 << " specialized clones of " << target_name << "\n";
        }
      }
    }
  }

  // Late target discovery: after ABI recovery folds MBA chains (via
  // EliminateStateStruct + RecoverStackFrame + SROA + GVN), scan for
  // constant inttoptr call targets that point to unlifted code addresses.
  // Lift them directly into the current module/session, rerun the pipeline
  // + ABI on just the newly-lifted slice, and keep cleanup of Remill
  // infrastructure deferred until iterative discovery is fully closed.
  const bool run_post_abi_late_discovery =
      opts.resolve_indirect_targets && !NoABI &&
      !(opts.use_block_lifting && !opts.vm_devirtualize);
  if (run_post_abi_late_discovery) {
    llvm::DenseMap<uint64_t, uint64_t> nested_vm_helper_targets;
    llvm::DenseMap<uint64_t, uint64_t> nested_vm_helper_deltas;
    struct NestedHelperCallsite {
      std::string caller_name;
      std::string helper_name;
      unsigned ordinal = 0;
      std::optional<uint64_t> hash;
    };
    struct HashResolvedCall {
      std::string caller_name;
      std::string helper_name;
      unsigned ordinal = 0;
      uint64_t hash = 0;
      uint64_t target_va = 0;
    };
    // --- Virtual callee registry (formal, first-class) ---
    // VirtualCalleeRecord is the canonical data structure.  We keep a
    // separate Function* cache because VirtualCalleeRecord is serializable
    // (no LLVM pointers) while the Function* is session-local.
    llvm::StringMap<omill::VirtualCalleeRecord> outlined_virtual_callee_records;
    llvm::StringMap<llvm::Function *> outlined_virtual_callee_fns;
    bool verbose_vm_outlined = (std::getenv("OMILL_VM_VERBOSE") != nullptr);

    auto ensureOutlinedVirtualCallee = [&](llvm::Function *base_fn,
                                           const std::string &clone_name,
                                           llvm::StringRef caller_name,
                                           std::optional<uint64_t> hash,
                                           llvm::StringRef kind,
                                           unsigned round_index,
                                           uint64_t handler_va = 0,
                                           std::optional<uint64_t> trace_hash = std::nullopt)
        -> std::pair<llvm::Function *, bool> {
      if (!base_fn || base_fn->isDeclaration())
        return {nullptr, false};

      auto fn_it = outlined_virtual_callee_fns.find(clone_name);
      if (fn_it != outlined_virtual_callee_fns.end()) {
        if (fn_it->second)
          return {fn_it->second, false};
      }

      llvm::Function *clone = base_fn->getParent()->getFunction(clone_name);
      bool created = false;
      if (!clone) {
        llvm::ValueToValueMapTy VMap;
        clone = llvm::CloneFunction(base_fn, VMap);
        clone->setName(clone_name);
        created = true;
      }

      // Boundary markers — these are the minimal attrs that downstream passes
      // check for inlining/outlining decisions.  Detail data lives in the
      // registry metadata, not duplicated as attrs.
      clone->setLinkage(llvm::GlobalValue::InternalLinkage);
      clone->addFnAttr(llvm::Attribute::NoInline);
      clone->addFnAttr("omill.vm_outlined_virtual_call", "1");
      // Trace linkage attrs — propagated through ABI wrapper generation by
      // RecoverFunctionSignatures so the registry can reconstruct trace keys
      // from the _native function after the pipeline.
      if (handler_va != 0)
        clone->addFnAttr("omill.vm_handler_va",
                         llvm::utohexstr(handler_va));
      if (trace_hash)
        clone->addFnAttr("omill.vm_trace_hash",
                         llvm::utohexstr(*trace_hash));
      if (hash)
        clone->addFnAttr("omill.vm_helper_hash", llvm::utohexstr(*hash));
      else
        clone->removeFnAttr("omill.vm_helper_hash");

      outlined_virtual_callee_fns[clone_name] = clone;

      auto &record = outlined_virtual_callee_records[clone_name];
      if (record.clone_name.empty()) {
        record.clone_name = clone_name;
        record.base_name = base_fn->getName().str();
        record.caller_name = caller_name.str();
        record.kind = kind.str();
        record.hash = hash;
        record.first_round = round_index;
        record.handler_va = handler_va;
        record.trace_hash = trace_hash;
      }

      if (created && verbose_vm_outlined) {
        errs() << "Outlined virtual callee " << clone_name
               << " kind=" << kind
               << " base=" << base_fn->getName();
        if (hash)
          errs() << " hash=0x" << Twine::utohexstr(*hash);
        if (handler_va != 0)
          errs() << " handler_va=0x" << Twine::utohexstr(handler_va);
        if (trace_hash)
          errs() << " trace_hash=0x" << Twine::utohexstr(*trace_hash);
        errs() << " caller=" << caller_name
               << " round=" << round_index << "\n";
      }

      return {clone, created};
    };


    auto syncOutlinedVirtualCalleeRegistry = [&]() {
      std::vector<omill::VirtualCalleeRecord> records;
      records.reserve(outlined_virtual_callee_records.size());
      for (const auto &entry : outlined_virtual_callee_records) {
        records.push_back(entry.getValue());
      }
      omill::setVirtualCalleeRegistryMetadata(*module, records);
    };


    auto collectNestedVMHelperTargets = [&]() {
      nested_vm_helper_targets.clear();
      nested_vm_helper_deltas.clear();
      if (!vm_mode || RawBinary || has_external_vm_trace || true)
        return;

      auto followJmpThunks = [&](uint64_t va) {
        uint64_t resolved = va;
        for (unsigned hop = 0; hop < 4; ++hop) {
          uint8_t thunk_buf[16];
          if (!pe.memory_map.read(resolved, thunk_buf, sizeof(thunk_buf)))
            break;
          if (thunk_buf[0] == 0xE9) {
            int32_t rel = 0;
            std::memcpy(&rel, &thunk_buf[1], 4);
            resolved = resolved + 5 + static_cast<int64_t>(rel);
            continue;
          }
          if (thunk_buf[0] == 0xEB) {
            int8_t rel = static_cast<int8_t>(thunk_buf[1]);
            resolved = resolved + 2 + rel;
            continue;
          }
          break;
        }
        return resolved;
      };

      uint64_t seg_start = vm_entry_va;
      uint64_t seg_end = vm_entry_va + 0x2000000;
      pe.memory_map.forEachRegion(
          [&](uint64_t base, const uint8_t *, size_t size) {
            if (vm_entry_va >= base && vm_entry_va < base + size) {
              seg_start = base;
              seg_end = base + size;
            }
          });

      omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                         vm_entry_va, vm_exit_va);
      solver.setHandlerSegmentRange(seg_start, seg_end);

      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native") ||
            F.hasFnAttribute("omill.vm_wrapper")) {
          continue;
        }

        auto base_name = F.getName().drop_back(strlen("_native"));
        if (!base_name.starts_with("sub_"))
          continue;

        uint64_t helper_va = 0;
        if (base_name.drop_front(4).getAsInteger(16, helper_va) ||
            helper_va == 0) {
          continue;
        }

        llvm::SmallVector<llvm::CallInst *, 2> indirect_calls;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            if (llvm::isa<llvm::Function>(
                    CI->getCalledOperand()->stripPointerCasts())) {
              continue;
            }
            indirect_calls.push_back(CI);
          }
        }
        if (indirect_calls.size() != 1)
          continue;

        uint64_t wrapper_va = followJmpThunks(helper_va);
        if (wrapper_va == 0 || wrapper_va == helper_va ||
            wrapper_va == vm_wrapper_va) {
          continue;
        }

        auto trace = solver.traceFromWrapper(wrapper_va);
        if (trace.empty() || trace.front().successors.empty())
          continue;

        uint64_t target_va = trace.front().successors.front();
        if (target_va == 0)
          continue;

        nested_vm_helper_targets[helper_va] = target_va;
        nested_vm_helper_deltas[helper_va] = solver.lastDelta();
      }
    };

    struct HashBufferInfo {
      uint64_t hash = 0;
      std::array<uint32_t, 5> words = {};
      std::vector<std::pair<int64_t, uint64_t>> scratch_qwords;
      std::vector<std::pair<int64_t, uint64_t>> precall_qwords;
      uint64_t return_seed = 0;
    };

    auto getAddConst = [&](llvm::Value *V) -> std::optional<int64_t> {
      auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
      if (!BO)
        return std::nullopt;
      auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
      if (!C || C->getBitWidth() > 64)
        return std::nullopt;
      if (BO->getOpcode() == llvm::Instruction::Add)
        return C->getSExtValue();
      if (BO->getOpcode() == llvm::Instruction::Sub)
        return -C->getSExtValue();
      return std::nullopt;
    };

    auto getStackDisp = [&](llvm::Value *V) -> std::optional<int64_t> {
      if (auto disp = getAddConst(V))
        return disp;
      auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(V);
      if (!GEP)
        return std::nullopt;
      llvm::APInt offset(64, 0, true);
      if (!GEP->accumulateConstantOffset(module->getDataLayout(), offset))
        return std::nullopt;
      return static_cast<int64_t>(offset.getSExtValue()) - 65504;
    };

    auto decodeHashBuffer =
        [&](llvm::CallInst *CI) -> std::optional<HashBufferInfo> {
      constexpr int64_t kSnapshotSpan = 0x2000;
      uint32_t words[5] = {};
      unsigned found = 0;
      std::vector<std::pair<int64_t, uint64_t>> scratch_qwords;
      std::vector<std::pair<int64_t, uint64_t>> precall_qwords;
      for (auto It = CI->getIterator(); It != CI->getParent()->begin();) {
        --It;
        if (llvm::isa<llvm::CallBase>(&*It))
          break;
        auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*It);
        if (!SI)
          continue;
        auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand());
        if (!C)
          continue;
        auto disp = getStackDisp(SI->getPointerOperand());
        if (C->getBitWidth() == 32 && found < 5) {
          if (disp && *disp < 0 && *disp >= -0x1000)
            words[found++] = C->getZExtValue();
          continue;
        }
        if (C->getBitWidth() == 64 && disp &&
            *disp >= -0x1000 && *disp < kSnapshotSpan) {
          precall_qwords.emplace_back(*disp, C->getZExtValue());
          if (*disp < 0)
            scratch_qwords.emplace_back(*disp, C->getZExtValue());
        }
      }
      if (found != 5)
        return std::nullopt;
      std::reverse(std::begin(words), std::end(words));
      uint64_t return_seed = scratch_qwords.empty()
                                 ? 0
                                 : scratch_qwords.front().second;
      std::reverse(scratch_qwords.begin(), scratch_qwords.end());
      std::reverse(precall_qwords.begin(), precall_qwords.end());
      HashBufferInfo info;
      for (unsigned i = 0; i < 5; ++i)
        info.words[i] = words[i];
      info.hash = static_cast<uint64_t>(words[0]) |
                  (static_cast<uint64_t>(words[1]) << 32);
      info.scratch_qwords = std::move(scratch_qwords);
      info.precall_qwords = std::move(precall_qwords);
      info.return_seed = return_seed;
      return info;
    };

    auto collectHashResolvedCalls = [&]() {
      llvm::SmallVector<HashResolvedCall, 8> resolved_calls;
      if (!vm_mode || RawBinary || true)
        return resolved_calls;
      llvm::DenseMap<llvm::Value *, uint64_t> helper_value_cache;
      llvm::DenseMap<uint64_t, std::optional<uint64_t>> per_wrapper_seed;

      auto followJmpThunks = [&](uint64_t va) {
        uint64_t resolved = va;
        for (unsigned hop = 0; hop < 4; ++hop) {
          uint8_t thunk_buf[16];
          if (!pe.memory_map.read(resolved, thunk_buf, sizeof(thunk_buf)))
            break;
          if (thunk_buf[0] == 0xE9) {
            int32_t rel = 0;
            std::memcpy(&rel, &thunk_buf[1], 4);
            resolved = resolved + 5 + static_cast<int64_t>(rel);
            continue;
          }
          if (thunk_buf[0] == 0xEB) {
            int8_t rel = static_cast<int8_t>(thunk_buf[1]);
            resolved = resolved + 2 + rel;
            continue;
          }
          break;
        }
        return resolved;
      };

      uint64_t seg_start = vm_entry_va;
      uint64_t seg_end = vm_entry_va + 0x2000000;
      pe.memory_map.forEachRegion(
          [&](uint64_t base, const uint8_t *, size_t size) {
            if (vm_entry_va >= base && vm_entry_va < base + size) {
              seg_start = base;
              seg_end = base + size;
            }
          });

      auto getConstI64 = [&](llvm::Value *V) -> std::optional<uint64_t> {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
          return CI->getZExtValue();
        return std::nullopt;
      };
      auto resolveNestedHelperValue =
          [&](llvm::Value *V) -> std::optional<uint64_t> {
        if (auto it = helper_value_cache.find(V); it != helper_value_cache.end())
          return it->second;
        auto *CI = llvm::dyn_cast<llvm::CallInst>(V);
        if (!CI)
          return std::nullopt;
        auto *callee = llvm::dyn_cast<llvm::Function>(
            CI->getCalledOperand()->stripPointerCasts());
        if (!callee || !callee->getName().ends_with("_native"))
          return std::nullopt;
        auto base = callee->getName().drop_back(strlen("_native"));
        if (!base.starts_with("sub_"))
          return std::nullopt;
        uint64_t callee_va = 0;
        if (base.drop_front(4).getAsInteger(16, callee_va) || callee_va == 0)
          return std::nullopt;
        // Only resolve if the callee is a known wrapper.
        if (!nested_vm_helper_targets.count(callee_va))
          return std::nullopt;
        auto &seed = per_wrapper_seed[callee_va];
        if (!seed) {
          uint64_t wrapper_va = followJmpThunks(callee_va);
          if (wrapper_va == 0) wrapper_va = callee_va;
          omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                             vm_entry_va, vm_exit_va);
          solver.setHandlerSegmentRange(seg_start, seg_end);
          auto results = solver.traceFromWrapper(wrapper_va);
          auto targets = solver.nativeCallTargets();
          if (targets.size() == 1) {
            seed = targets.front();
          } else {
            for (auto &entry : results) {
              if (entry.handler_va == wrapper_va || entry.successors.empty())
                continue;
              seed = entry.successors.front();
              break;
            }
          }
        }
        if (!seed)
          return std::nullopt;
        helper_value_cache[V] = *seed;
        return *seed;
      };
      auto getConcreteI64 = [&](llvm::Value *V) -> std::optional<uint64_t> {
        if (auto c = getConstI64(V))
          return c;
        return resolveNestedHelperValue(V);
      };

      auto buildVMWrapperSnapshot =
          [&](llvm::CallInst *CI, const HashBufferInfo &buffer_info)
              -> std::vector<uint8_t> {
        constexpr size_t kSnapshotSize = 0x2000;
        constexpr uint64_t kSub1402A110ERet = 0xFFFFFFFFFFD61E74ull;

        std::vector<uint8_t> snapshot(kSnapshotSize, 0);
        auto putI64 = [&](size_t off, uint64_t value) {
          if (off + sizeof(value) > snapshot.size())
            return;
          std::memcpy(snapshot.data() + off, &value, sizeof(value));
        };
        auto putBufferWord = [&](size_t off, uint32_t value) {
          if (off + sizeof(value) > snapshot.size())
            return;
          std::memcpy(snapshot.data() + off, &value, sizeof(value));
        };
        auto getArgConcreteOr = [&](unsigned index, uint64_t fallback) {
          if (index >= CI->arg_size())
            return fallback;
          if (auto value = getConcreteI64(CI->getArgOperand(index)))
            return *value;
          return fallback;
        };

        uint64_t synthetic_vm_base =
            omill::VMTraceEmulator::syntheticVMContextBase();
        uint64_t synthetic_saved_rsp = synthetic_vm_base + 0x1800;
        auto mapScratchDisp = [&](int64_t disp, int64_t fallback) {
          if (disp >= 0 || disp < -0x1000)
            disp = fallback;
          return synthetic_saved_rsp + disp;
        };
        int64_t buffer_disp = -0x150;
        if (CI->arg_size() > 1) {
          if (auto disp = getAddConst(CI->getArgOperand(1)))
            buffer_disp = *disp;
        }
        uint64_t synthetic_buffer = mapScratchDisp(buffer_disp, -0x150);
        size_t buffer_off =
            static_cast<size_t>(synthetic_buffer - synthetic_vm_base);
        for (unsigned i = 0; i < buffer_info.words.size(); ++i)
          putBufferWord(buffer_off + i * sizeof(uint32_t),
                        buffer_info.words[i]);
        bool has_explicit_1c0 = false;
        bool has_explicit_1c8 = false;
        for (auto &[disp, value] : buffer_info.precall_qwords) {
          if (disp >= 0) {
            size_t off = static_cast<size_t>(disp);
            putI64(off, value);
            has_explicit_1c0 |= (off == 0x1C0);
            has_explicit_1c8 |= (off == 0x1C8);
            continue;
          }
          uint64_t addr = mapScratchDisp(disp, disp);
          size_t off = static_cast<size_t>(addr - synthetic_vm_base);
          putI64(off, value);
        }

        int64_t scratch_disp = -0x78;
        if (CI->arg_size() > 7) {
          if (auto disp = getAddConst(CI->getArgOperand(7)))
            scratch_disp = *disp;
        }
        uint64_t synthetic_scratch = mapScratchDisp(scratch_disp, -0x78);

        // After ABI recovery, the VM wrapper performs a small setup
        // around the vmentry and then tail-calls the first handler.
        // Seed the synthetic register and home-space slots from that
        // nested callsite, not from the helper's original wrapper arguments.
        uint64_t chain_rcx = getArgConcreteOr(2, 0);
        uint64_t chain_rdx = getArgConcreteOr(3, 0);
        uint64_t chain_r8 = getArgConcreteOr(8, 0);
        uint64_t home_rcx = chain_rcx;
        uint64_t home_rdx = chain_rdx;
        uint64_t home_r8 = chain_r8;
        uint64_t home_r9 = 0;
        putI64(0x30, getArgConcreteOr(7, 0));                // RBP
        putI64(0x38, synthetic_buffer);                      // RDX
        putI64(0x40, getArgConcreteOr(4, 0));                // RBX
        putI64(0x50, home_rcx);                              // pre-shift [rsp+8]
        putI64(0x58, home_rdx);                              // pre-shift [rsp+10]
        putI64(0x60, home_r8);                               // pre-shift [rsp+18]
        putI64(0x68, home_r9);                               // pre-shift [rsp+20]
        putI64(0x78, home_r8);                               // R8
        putI64(0x80, home_r9);                               // R9
        putI64(0x88, getArgConcreteOr(9, 0));                // R13
        putI64(0x90, home_rcx);                              // RCX
        putI64(0x98, getArgConcreteOr(8, 0));                // R12
        putI64(0xB8, synthetic_scratch);                     // helper scratch
        putI64(0xC0, synthetic_saved_rsp);                   // saved RSP-ish
        putI64(0xE0, kSub1402A110ERet);                      // sub_1402A110E
        putI64(0x108, 0);                                    // RAX
        putI64(0x110, getArgConcreteOr(10, 0));              // R14
        putI64(0x128, getArgConcreteOr(5, 0));               // RSI
        putI64(0x140, getArgConcreteOr(11, 0));              // R15
        putI64(0x158, 0);                                    // R10 scratch
        putI64(0x170, getArgConcreteOr(6, 0));               // RDI
        putI64(0x188, 0);                                    // R11 scratch
        // The wrapper stores [vmctx+0x38] to [*[vmctx+0xB8] + 0x10]
        // before tail-calling the first handler.
        putI64(static_cast<size_t>(synthetic_scratch - synthetic_vm_base) +
                   0x10,
               synthetic_buffer);
        // The first handler frame-shift re-bases [vmctx+0xB8] by -0x178
        // before the next stage consumes [*[vmctx+0xB8] + 0x10]. Seed the
        // shifted alias as well so the buffer pointer survives that move.
        if (synthetic_scratch >= synthetic_vm_base + 0x168) {
          putI64(static_cast<size_t>(synthetic_scratch - synthetic_vm_base) -
                     0x168,
                 synthetic_buffer);
        }
        if (!has_explicit_1c0 && buffer_info.return_seed != 0)
          putI64(0x1C0, buffer_info.return_seed);
        else if (!has_explicit_1c0)
          putI64(0x1C0, 0);
        if (!has_explicit_1c8)
          putI64(0x1C8, home_rcx);
        putI64(0x1D0, home_rdx);
        putI64(0x1D8, home_r8);
        putI64(0x1E0, home_r9);

        return snapshot;
      };

      for (auto &[helper_va, handler_va] : nested_vm_helper_targets) {
        (void)handler_va;
        uint64_t delta = nested_vm_helper_deltas.lookup(helper_va);
        if (delta == 0)
          continue;

        std::string helper_name =
            "sub_" + llvm::Twine::utohexstr(helper_va).str() + "_native";
        uint64_t wrapper_va = followJmpThunks(helper_va);
        if (wrapper_va == 0)
          wrapper_va = helper_va;
        for (auto &F : *module) {
          unsigned ordinal = 0;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!CI)
                continue;
              auto *callee = llvm::dyn_cast<llvm::Function>(
                  CI->getCalledOperand()->stripPointerCasts());
              if (!callee || callee->getName() != helper_name)
                continue;

              auto buffer_info = decodeHashBuffer(CI);
              if (!buffer_info) {
                ++ordinal;
                continue;
              }

              omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                                 vm_entry_va, vm_exit_va);
              solver.setHandlerSegmentRange(seg_start, seg_end);
              auto snapshot = buildVMWrapperSnapshot(CI, *buffer_info);
              (void)delta;
              (void)handler_va;
              (void)solver.traceFromWrapperWithSnapshot(wrapper_va, snapshot);
              auto targets = solver.nativeCallTargets();
              if (targets.size() != 1) {
                errs() << "Trace-emulated resolve for " << helper_name
                       << " hash=0x" << Twine::utohexstr(buffer_info->hash)
                       << " produced "
                       << targets.size() << " native target(s)\n";
                if (getenv("OMILL_DEBUG_CHAIN")) {
                  errs() << "  call: ";
                  CI->print(errs());
                  errs() << "\n";
                  errs() << "  precall qwords:";
                  for (auto &[disp, value] : buffer_info->precall_qwords)
                    errs() << " [" << disp << "]=0x"
                           << Twine::utohexstr(value);
                  errs() << "\n";
                }
                ++ordinal;
                continue;
              }

              HashResolvedCall resolved;
              resolved.caller_name = F.getName().str();
              resolved.helper_name = helper_name;
              resolved.ordinal = ordinal;
              resolved.hash = buffer_info->hash;
              resolved.target_va = targets.front();
              resolved_calls.push_back(std::move(resolved));
              ++ordinal;
            }
          }
        }
      }

      return resolved_calls;
    };

    auto collectNestedHelperCallsites = [&]() {
      llvm::SmallVector<NestedHelperCallsite, 8> callsites;
      if (!vm_mode || RawBinary || true)
        return callsites;

      llvm::DenseSet<uint64_t> helper_vas;
      for (auto &[helper_va, _] : nested_vm_helper_targets)
        helper_vas.insert(helper_va);
      if (helper_vas.empty())
        return callsites;

      for (auto &F : *module) {
        llvm::DenseMap<uint64_t, unsigned> ordinal_per_helper;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (!callee || !callee->getName().ends_with("_native"))
              continue;
            auto base_name = callee->getName().drop_back(strlen("_native"));
            if (!base_name.starts_with("sub_"))
              continue;
            uint64_t helper_va = 0;
            if (base_name.drop_front(4).getAsInteger(16, helper_va) ||
                !helper_vas.contains(helper_va)) {
              continue;
            }

            NestedHelperCallsite info;
            info.caller_name = F.getName().str();
            info.helper_name = callee->getName().str();
            info.ordinal = ordinal_per_helper[helper_va]++;
            auto hbuf = decodeHashBuffer(CI);
            info.hash = hbuf ? std::optional(hbuf->hash) : std::nullopt;
            callsites.push_back(std::move(info));
          }
        }
      }
      return callsites;
    };

    for (unsigned round = 0; round < 3; ++round) {
      if (events.detailed()) {
        events.emitInfo("late_discovery_round_started",
                        "late target discovery round started",
                        {{"round", static_cast<int64_t>(round + 1)}});
      }
      // Collect constant inttoptr call targets.
      // Match both ConstantExpr::IntToPtr and IntToPtrInst with constant
      // operands — LLVM 21 no longer folds inttoptr(const) instructions
      // to ConstantExpr form, so B3 dynamic rewrites from
      // RewriteLiftedCallsToNative produce IntToPtrInst after GVN folds.
      llvm::DenseSet<uint64_t> late_targets;
      for (auto &F : *module) {
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!call)
              continue;

            if (auto *callee = call->getCalledFunction()) {
              if (callee->getName().contains("CALLI") &&
                  call->arg_size() >= 3) {
                auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2));
                if (!ci)
                  continue;
                const uint64_t target = ci->getZExtValue();
                if (!isCodeAddressInCurrentInput(target))
                  continue;
                if (hasDefinedLiftedOrBlockTarget(target))
                  continue;
                late_targets.insert(target);
                continue;
              }

              if (!callee->isDeclaration())
                continue;
              if (!callee->getName().starts_with("sub_"))
                continue;
              auto *FT = callee->getFunctionType();
              if (FT->getNumParams() != 3 ||
                  FT->getReturnType() != llvm::PointerType::getUnqual(ctx) ||
                  FT->getParamType(0) != llvm::PointerType::getUnqual(ctx) ||
                  FT->getParamType(1) != llvm::Type::getInt64Ty(ctx) ||
                  FT->getParamType(2) != llvm::PointerType::getUnqual(ctx)) {
                continue;
              }

              const uint64_t target = omill::extractEntryVA(callee->getName());
              if (!isCodeAddressInCurrentInput(target))
                continue;
              if (hasDefinedLiftedOrBlockTarget(target))
                continue;
              late_targets.insert(target);
              continue;
            }

            auto *callee_op = call->getCalledOperand();
            llvm::ConstantInt *ci = nullptr;
            // Case 1: ConstantExpr inttoptr.
            if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
              if (ce->getOpcode() == llvm::Instruction::IntToPtr)
                ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
            }
            // Case 2: IntToPtrInst with constant operand.
            if (!ci) {
              if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
                ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
            }
            if (!ci)
              continue;
            uint64_t target = ci->getZExtValue();
            if (target == 0)
              continue;
            if (!isCodeAddressInCurrentInput(target))
              continue;
            if (hasDefinedLiftedOrBlockTarget(target))
              continue;
            late_targets.insert(target);
          }
        }
      }
      collectNestedVMHelperTargets();

      // Populate nested_vm_helper_targets for auto-detected wrappers
      // whose thunks were folded.  After folding, calls go directly to
      // the wrapper so the helper VA in the map is the wrapper VA.
      if (false) {
        for (auto &[thunk_va, wrapper_va] : auto_detected_wrappers) {
          if (has_external_vm_trace)
            break;
          if (nested_vm_helper_targets.count(wrapper_va))
            continue;  // already discovered
          // Trace from this wrapper to get the first handler target.
          omill::VMTraceEmulator probe(pe.memory_map, pe.image_base,
                                       vm_entry_va, vm_exit_va);
          uint64_t seg_start_l = vm_entry_va;
          uint64_t seg_end_l = vm_entry_va + 0x2000000;
          pe.memory_map.forEachRegion(
              [&](uint64_t base, const uint8_t *, size_t size) {
                if (vm_entry_va >= base && vm_entry_va < base + size) {
                  seg_start_l = base;
                  seg_end_l = base + size;
                }
              });
          probe.setHandlerSegmentRange(seg_start_l, seg_end_l);
          auto trace = probe.traceFromWrapper(wrapper_va);
          if (!trace.empty() && !trace.front().successors.empty()) {
            uint64_t target_va = trace.front().successors.front();
            nested_vm_helper_targets[wrapper_va] = target_va;
            nested_vm_helper_deltas[wrapper_va] = probe.lastDelta();
          }
        }
      }
      auto hash_resolved_calls = collectHashResolvedCalls();
      auto nested_helper_callsites = collectNestedHelperCallsites();
      for (auto &[helper_va, target_va] : nested_vm_helper_targets) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
        auto *existing = module->getFunction(native_name);
        if (!existing || existing->isDeclaration())
          late_targets.insert(target_va);
        errs() << "Nested VM helper sub_" << Twine::utohexstr(helper_va)
               << "_native -> first handler 0x"
               << Twine::utohexstr(target_va) << "\n";
      }
      for (auto &resolved : hash_resolved_calls) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(resolved.target_va).str() +
            "_native";
        auto *existing = module->getFunction(native_name);
        if (!existing || existing->isDeclaration())
          late_targets.insert(resolved.target_va);
        errs() << "Hash-resolved " << resolved.helper_name << " call "
               << resolved.ordinal << " hash=0x"
               << Twine::utohexstr(resolved.hash) << " -> 0x"
               << Twine::utohexstr(resolved.target_va) << "\n";
      }
      if (late_targets.empty()) {
        errs() << "Late discovery round " << (round + 1)
               << ": no new targets\n";
        break;
      }

      errs() << "Late discovery round " << (round + 1) << ": "
             << late_targets.size() << " new target(s)\n";
      events.emitInfo("late_discovery_targets", "late discovery targets found",
                      {{"round", static_cast<int64_t>(round + 1)},
                       {"targets", static_cast<int64_t>(late_targets.size())}});

      // Lift late targets directly into the current session/module and rerun
      // the normal pipeline on just the newly-added functions. This avoids
      // a second Arch/semantics/module world and keeps discovery iterative.
      llvm::DenseSet<llvm::Function *> pre_lift_funcs;
      for (auto &F : *module)
        pre_lift_funcs.insert(&F);

      unsigned late_patched = 0;
      unsigned late_lifted = 0;
      unsigned late_failed = 0;
      auto trace_cb = iterative_session->traceLiftCallback();
      auto block_cb = iterative_session->blockLiftCallback();
      for (uint64_t pc : late_targets) {
        if (events.detailed()) {
          events.emitInfo("late_discovery_lift_started",
                          "late discovery target lift started",
                          {{"round", static_cast<int64_t>(round + 1)},
                           {"target", ("0x" + llvm::Twine::utohexstr(pc)).str()},
                           {"pipeline",
                            opts.use_block_lifting ? "block" : "trace"}});
        }
        iterative_session->queueTarget(pc);
        bool lifted_ok = false;
        if (opts.use_block_lifting && !vm_mode && block_cb) {
          lifted_ok = block_cb(pc);
        } else if (trace_cb) {
          lifted_ok = trace_cb(pc);
        } else {
          lifted_ok = lifter.Lift(pc);
          if (lifted_ok)
            iterative_session->noteLiftedTarget(pc);
        }
        if (lifted_ok) {
          ++late_lifted;
        } else {
          ++late_failed;
        }
        if (events.detailed()) {
          events.emitInfo("late_discovery_lift_completed",
                          "late discovery target lift completed",
                          {{"round", static_cast<int64_t>(round + 1)},
                           {"target", ("0x" + llvm::Twine::utohexstr(pc)).str()},
                           {"lifted", lifted_ok}});
        }
      }
      if (events.detailed()) {
        events.emitInfo("late_discovery_lift_batch_completed",
                        "late discovery target batch completed",
                        {{"round", static_cast<int64_t>(round + 1)},
                         {"lifted", static_cast<int64_t>(late_lifted)},
                         {"failed", static_cast<int64_t>(late_failed)}});
      }
      fixLiftedFunctionNamingCollisions();
      if (events.detailed()) {
        events.emitInfo("late_discovery_collision_fix_completed",
                        "late discovery collision fix completed",
                        {{"round", static_cast<int64_t>(round + 1)}});
      }

      if (late_lifted == 0) {
        errs() << "Late discovery round " << (round + 1)
               << ": lift failed for all targets\n";
        events.emitWarn("late_discovery_lift_failed",
                        "late discovery lifting produced no new functions",
                        {{"round", static_cast<int64_t>(round + 1)},
                         {"failed", static_cast<int64_t>(late_failed)}});
        break;
      }

      tagNewlyLiftedFunctions("omill.late_newly_lifted", pre_lift_funcs);
      if (events.detailed()) {
        events.emitInfo("late_discovery_tagging_completed",
                        "late discovery new function tagging completed",
                        {{"round", static_cast<int64_t>(round + 1)}});
      }

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_lift.ll", ec, sys::fs::OF_Text);
        module->print(os, nullptr);
      }

      rerunLateDiscoveryPipeline("omill.late_newly_lifted", /*run_abi=*/true,
                                 /*skip_missing_block_lift=*/false);

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_pipeline.ll", ec, sys::fs::OF_Text);
        module->print(os, nullptr);
      }

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_abi.ll", ec, sys::fs::OF_Text);
        module->print(os, nullptr);
      }

      // Patch call sites: replace inttoptr(i64 <const>) → @sub_<hex>_native
      // Handles both ConstantExpr and IntToPtrInst forms.
      for (uint64_t pc : late_targets) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(pc).str() + "_native";
        auto *target_fn = module->getFunction(native_name);
        if (!target_fn)
          continue;
        auto *pc_ci = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(ctx), pc);

        // Case 1: ConstantExpr inttoptr — RAUW replaces all uses globally.
        auto *itp = llvm::ConstantExpr::getIntToPtr(
            pc_ci, llvm::PointerType::getUnqual(ctx));
        if (itp->getNumUses() > 0) {
          late_patched += itp->getNumUses();
          itp->replaceAllUsesWith(target_fn);
        }

        // Case 2: IntToPtrInst instructions with this constant operand.
        // Each instruction is a separate Value, so scan and replace each.
        // ConstantInt (ConstantData) may not have a use list in LLVM 21.
        if (!pc_ci->hasUseList())
          continue;
        for (auto *user : llvm::make_early_inc_range(pc_ci->users())) {
          auto *inst = llvm::dyn_cast<llvm::IntToPtrInst>(user);
          if (!inst)
            continue;
          late_patched += inst->getNumUses();
          inst->replaceAllUsesWith(target_fn);
          if (inst->use_empty())
            inst->eraseFromParent();
        }
      }
      if (late_patched > 0) {
        runPostPatchCleanup("late_discovery_callsites");
        if (events.detailed()) {
          events.emitInfo("late_discovery_patch_callsites",
                          "patched late inttoptr callsites",
                          {{"round", static_cast<int64_t>(round + 1)},
                           {"patched_uses",
                           static_cast<int64_t>(late_patched)}});
        }
      }

      unsigned helper_patched = 0;
      for (auto &[helper_va, target_va] : nested_vm_helper_targets) {
        std::string helper_name =
            "sub_" + llvm::Twine::utohexstr(helper_va).str() + "_native";
        std::string target_name =
            "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
        auto *helper_fn = module->getFunction(helper_name);
        auto *target_fn = module->getFunction(target_name);
        if (!helper_fn || helper_fn->isDeclaration() ||
            !target_fn || target_fn->isDeclaration()) {
          continue;
        }

        llvm::SmallVector<llvm::CallInst *, 2> indirect_calls;
        for (auto &BB : *helper_fn) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            if (llvm::isa<llvm::Function>(
                    CI->getCalledOperand()->stripPointerCasts())) {
              continue;
            }
            indirect_calls.push_back(CI);
          }
        }
        if (indirect_calls.size() != 1)
          continue;

        auto *CI = indirect_calls.front();
        llvm::SmallVector<llvm::Value *, 16> args;
        for (auto &Arg : CI->args())
          args.push_back(Arg.get());

        llvm::IRBuilder<> Builder(CI);
        llvm::Value *direct_callee = target_fn;
        if (target_fn->getType() != CI->getCalledOperand()->getType()) {
          direct_callee = Builder.CreateBitCast(
              target_fn, CI->getCalledOperand()->getType(),
              target_name + ".cast");
        }
        auto *new_call = Builder.CreateCall(
            CI->getFunctionType(), direct_callee, args, CI->getName());
        new_call->setCallingConv(CI->getCallingConv());
        new_call->setAttributes(CI->getAttributes());
        if (!CI->use_empty())
          CI->replaceAllUsesWith(new_call);
        CI->eraseFromParent();
        ++helper_patched;
      }
      if (helper_patched > 0) {
        errs() << "Patched " << helper_patched
               << " nested VM helper call(s) to direct targets\n";
        runPostPatchCleanup("nested_vm_helpers");
      }

      // Do NOT fold hash-resolved helper calls to constants. Those helpers
      // represent distinct virtualized callees and must remain outlined so the
      // recovered demerged control flow stays modelled as callable functions.
      unsigned hash_helper_clone_count = 0;
      for (const auto &resolved : hash_resolved_calls) {
        auto *caller_fn = module->getFunction(resolved.caller_name);
        auto *helper_fn = module->getFunction(resolved.helper_name);
        if (!caller_fn || caller_fn->isDeclaration() ||
            !helper_fn || helper_fn->isDeclaration()) {
          continue;
        }

        unsigned ordinal = 0;
        llvm::CallInst *target_call = nullptr;
        for (auto &BB : *caller_fn) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (!callee || callee->getName() != resolved.helper_name)
              continue;
            if (ordinal++ == resolved.ordinal) {
              target_call = CI;
              break;
            }
          }
          if (target_call)
            break;
        }
        if (!target_call)
          continue;

        std::string clone_name = resolved.helper_name + "__" +
                                 resolved.caller_name + "_" +
                                 std::to_string(resolved.ordinal) +
                                 "_h" + llvm::utohexstr(resolved.hash);
        // Extract handler VA from helper name for trace linkage.
        uint64_t helper_va_for_trace = 0;
        {
          llvm::StringRef bn = llvm::StringRef(resolved.helper_name);
          if (bn.ends_with("_native"))
            bn = bn.drop_back(7);  // strlen("_native")
          if (bn.starts_with("sub_"))
            bn.drop_front(4).getAsInteger(16, helper_va_for_trace);
        }
        auto [clone, created] = ensureOutlinedVirtualCallee(
            helper_fn, clone_name, resolved.caller_name, resolved.hash,
            "hash_resolved", round + 1, helper_va_for_trace,
            std::optional<uint64_t>(resolved.hash));
        if (!clone)
          continue;
        if (created)
          ++hash_helper_clone_count;

        llvm::SmallVector<llvm::Value *, 16> args;
        for (auto &Arg : target_call->args())
          args.push_back(Arg.get());

        llvm::IRBuilder<> Builder(target_call);
        auto *clone_call =
            Builder.CreateCall(clone, args, clone_name + ".result");
        clone_call->setCallingConv(target_call->getCallingConv());
        clone_call->setAttributes(target_call->getAttributes());
        target_call->replaceAllUsesWith(clone_call);
        target_call->eraseFromParent();
      }
      if (hash_helper_clone_count > 0) {
        errs() << "Cloned " << hash_helper_clone_count
               << " hash-resolved helper call(s) to outlined wrappers\n";
        runPostPatchCleanup("hash_resolved_helpers");
      }

      unsigned helper_clone_count = 0;
      llvm::StringMap<unsigned> helper_callsite_counts;
      llvm::StringMap<llvm::SmallVector<NestedHelperCallsite, 4>>
          helper_callsites_by_key;
      auto helperCloneKey = [&](const NestedHelperCallsite &info) {
        return info.caller_name + "||" + info.helper_name;
      };
      for (const auto &info : nested_helper_callsites) {
        ++helper_callsite_counts[helperCloneKey(info)];
        helper_callsites_by_key[helperCloneKey(info)].push_back(info);
      }

      for (auto &entry : helper_callsites_by_key) {
        auto &infos = entry.getValue();

        llvm::sort(infos, [](const NestedHelperCallsite &lhs,
                             const NestedHelperCallsite &rhs) {
          return lhs.ordinal > rhs.ordinal;
        });

        llvm::SmallVector<llvm::CallInst *, 8> current_calls;
        auto *caller_fn = module->getFunction(infos.front().caller_name);
        auto *helper_fn = module->getFunction(infos.front().helper_name);
        if (!caller_fn || caller_fn->isDeclaration() ||
            !helper_fn || helper_fn->isDeclaration()) {
          continue;
        }
        for (auto &BB : *caller_fn) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (callee == helper_fn)
              current_calls.push_back(CI);
          }
        }

        for (const auto &info : infos) {
          if (info.ordinal >= current_calls.size())
            continue;
          llvm::CallInst *target_call = current_calls[info.ordinal];
          if (!target_call)
            continue;

          std::string clone_name = info.helper_name + "__" + info.caller_name +
                                   "_" + std::to_string(info.ordinal);
          if (info.hash)
            clone_name += "_h" + llvm::utohexstr(*info.hash);

          // Extract handler VA from helper name for trace linkage.
          uint64_t nested_helper_va = 0;
          {
            llvm::StringRef bn = llvm::StringRef(info.helper_name);
            if (bn.ends_with("_native"))
              bn = bn.drop_back(7);
            if (bn.starts_with("sub_"))
              bn.drop_front(4).getAsInteger(16, nested_helper_va);
          }
          auto [clone, created] = ensureOutlinedVirtualCallee(
              helper_fn, clone_name, info.caller_name, info.hash,
              "nested_helper", round + 1, nested_helper_va, info.hash);
          if (!clone)
            continue;

          llvm::SmallVector<llvm::Value *, 16> args;
          for (auto &Arg : target_call->args())
            args.push_back(Arg.get());

          llvm::IRBuilder<> Builder(target_call);
          auto *clone_call =
              Builder.CreateCall(clone, args, clone_name + ".result");
          clone_call->setCallingConv(target_call->getCallingConv());
          clone_call->setAttributes(target_call->getAttributes());
          target_call->replaceAllUsesWith(clone_call);
          target_call->eraseFromParent();
          current_calls[info.ordinal] = nullptr;
          if (created)
            ++helper_clone_count;
        }
      }
      if (helper_clone_count > 0) {
        errs() << "Cloned " << helper_clone_count
               << " nested VM helper call(s) for IR continuity\n";
        runPostPatchCleanup("nested_vm_helper_clones");
      }

      {
        omill::StateFieldMap sfm(*module);
        auto arch_abi =
            omill::ArchABI::get(omill::TargetArch::kX86_64, "windows");
        llvm::SmallVector<unsigned, 16> b3_arg_offsets;
        for (auto &reg : arch_abi.param_regs) {
          auto f = sfm.fieldByName(reg);
          if (f) b3_arg_offsets.push_back(f->offset);
        }
        for (auto &cs : arch_abi.callee_saved) {
          auto f = sfm.fieldByName(cs);
          if (f) b3_arg_offsets.push_back(f->offset);
        }

        auto *i64_ty = llvm::Type::getInt64Ty(ctx);
        auto findStateOffsetPtrInFunction =
            [&](llvm::Function &Fn, uint64_t offset) -> llvm::Value * {
          for (auto &BB : Fn) {
            for (auto &I : BB) {
              auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
              if (!GEP || GEP->getNumOperands() < 2)
                continue;
              auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
              if (!idx || idx->getZExtValue() != offset)
                continue;
              return GEP;
            }
          }
          return nullptr;
        };
        auto calleeReadsArg2AsStatePtr = [&](llvm::Function &Callee) -> bool {
          if (Callee.arg_size() < 3)
            return false;
          auto *arg = Callee.getArg(2);
          for (auto *U : arg->users()) {
            auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
            if (!BO || BO->getOpcode() != llvm::Instruction::Add)
              continue;
            auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
            auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
            if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
                (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
              return true;
            }
          }
          return false;
        };
        auto buildStateOrderedArgs =
            [&](llvm::Function &Caller, llvm::CallInst &CI,
                llvm::Function &Callee,
                llvm::ArrayRef<int> caller_param_offsets)
                -> std::optional<llvm::SmallVector<llvm::Value *, 16>> {
          auto attr = Callee.getFnAttribute("omill.param_state_offsets");
          if (!attr.isValid() || !attr.isStringAttribute())
            return std::nullopt;

          llvm::SmallVector<llvm::StringRef, 16> callee_offset_strs;
          attr.getValueAsString().split(callee_offset_strs, ',');
          if (callee_offset_strs.size() < Callee.arg_size())
            return std::nullopt;

          llvm::IRBuilder<> Builder(&CI);
          auto defaultMissingI64Arg = [&]() -> llvm::Value * {
            return llvm::ConstantInt::get(i64_ty, 0);
          };
          llvm::SmallVector<llvm::Value *, 16> new_args;
          new_args.reserve(Callee.arg_size());
          for (unsigned arg_index = 0; arg_index < Callee.arg_size(); ++arg_index) {
            llvm::StringRef off_str = callee_offset_strs[arg_index].trim();
            if (off_str == "stack" || off_str == "xmm") {
              if (arg_index < CI.arg_size())
                new_args.push_back(CI.getArgOperand(arg_index));
              else
                new_args.push_back(defaultMissingI64Arg());
              continue;
            }

            unsigned target_off = 0;
            if (off_str.getAsInteger(10, target_off))
              return std::nullopt;

            bool found = false;
            for (unsigned i = 0; i < caller_param_offsets.size() && i < Caller.arg_size();
                 ++i) {
              if (caller_param_offsets[i] == static_cast<int>(target_off)) {
                new_args.push_back(Caller.getArg(i));
                found = true;
                break;
              }
            }
            if (found)
              continue;

            if (auto *state_ptr = findStateOffsetPtrInFunction(Caller, target_off)) {
              new_args.push_back(
                  Builder.CreateLoad(i64_ty, state_ptr,
                                     "statefix." + llvm::Twine(target_off)));
              continue;
            }

            for (unsigned i = 0; i < b3_arg_offsets.size() && i < CI.arg_size(); ++i) {
              if (b3_arg_offsets[i] == target_off) {
                new_args.push_back(CI.getArgOperand(i));
                found = true;
                break;
              }
            }
            if (found)
              continue;

            return std::nullopt;
          }
          return new_args;
        };
        auto replaceCallWithArgs =
            [&](llvm::CallInst &CI, llvm::Function &Callee,
                llvm::ArrayRef<llvm::Value *> new_args) {
          auto *new_call = llvm::CallInst::Create(
              Callee.getFunctionType(), &Callee, new_args, CI.getName(),
              CI.getIterator());
          new_call->setCallingConv(CI.getCallingConv());
          new_call->setAttributes(CI.getAttributes());
          if (!CI.use_empty()) {
            if (CI.getType() == new_call->getType()) {
              CI.replaceAllUsesWith(new_call);
            } else if (llvm::isa<llvm::StructType>(new_call->getType())) {
              auto *ev = llvm::ExtractValueInst::Create(
                  new_call, {0}, "ret.primary",
                  std::next(new_call->getIterator()));
              CI.replaceAllUsesWith(ev);
            } else {
              CI.replaceAllUsesWith(llvm::PoisonValue::get(CI.getType()));
            }
          }
          CI.eraseFromParent();
        };
        unsigned fixup_count = 0;
        unsigned same_arity_fixup_count = 0;
        for (auto &F : *module) {
          if (!F.getName().ends_with("_native"))
            continue;
          llvm::SmallVector<int, 16> caller_param_offsets;
          if (auto attr = F.getFnAttribute("omill.param_state_offsets");
              attr.isValid() && attr.isStringAttribute()) {
            llvm::SmallVector<llvm::StringRef, 16> caller_offset_strs;
            attr.getValueAsString().split(caller_offset_strs, ',');
            for (auto &off_str : caller_offset_strs) {
              if (off_str == "stack" || off_str == "xmm") {
                caller_param_offsets.push_back(-1);
                continue;
              }
              unsigned off = 0;
              if (off_str.getAsInteger(10, off))
                caller_param_offsets.push_back(-1);
              else
                caller_param_offsets.push_back(static_cast<int>(off));
            }
          }
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!CI)
                continue;
              auto *callee = llvm::dyn_cast<llvm::Function>(
                  CI->getCalledOperand()->stripPointerCasts());
              if (!callee || !callee->getName().ends_with("_native"))
                continue;
              if (callee->hasFnAttribute("omill.vm_handler") &&
                  (F.hasFnAttribute("omill.vm_wrapper") ||
                   F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()))
                continue;

              if (CI->arg_size() == callee->arg_size()) {
                if (callee->arg_size() == 5 &&
                    calleeReadsArg2AsStatePtr(*callee)) {
                  auto *arg2_ci =
                      llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(2));
                  if (arg2_ci && arg2_ci->isZero()) {
                    llvm::SmallVector<llvm::Value *, 5> shifted_args = {
                        CI->getArgOperand(0), CI->getArgOperand(1),
                        CI->getArgOperand(3), CI->getArgOperand(4),
                        llvm::ConstantInt::get(i64_ty, 0)};
                    replaceCallWithArgs(*CI, *callee, shifted_args);
                    ++same_arity_fixup_count;
                    continue;
                  }
                }

                auto maybe_new_args =
                    buildStateOrderedArgs(F, *CI, *callee, caller_param_offsets);
                if (!maybe_new_args)
                  continue;
                auto &new_args = *maybe_new_args;
                bool suspicious = false;
                for (unsigned arg_index = 0; arg_index < CI->arg_size(); ++arg_index) {
                  auto *old_arg = CI->getArgOperand(arg_index);
                  auto *new_arg = new_args[arg_index];
                  if ((llvm::isa<llvm::PoisonValue>(old_arg) ||
                       llvm::isa<llvm::UndefValue>(old_arg)) &&
                      old_arg != new_arg) {
                    suspicious = true;
                    break;
                  }
                  auto *old_ci = llvm::dyn_cast<llvm::ConstantInt>(old_arg);
                  auto *new_ci = llvm::dyn_cast<llvm::ConstantInt>(new_arg);
                  if (old_arg == new_arg)
                    continue;
                  if (old_ci && old_ci->isZero() && (!new_ci || !new_ci->isZero())) {
                    suspicious = true;
                    break;
                  }
                  if (old_ci && new_ci && old_ci->getValue() != new_ci->getValue()) {
                    suspicious = true;
                    break;
                  }
                  if (!old_ci && new_ci && new_ci->isZero()) {
                    // Do not eagerly rewrite good dataflow into zeros.
                    continue;
                  }
                }
                if (!suspicious)
                  continue;

                replaceCallWithArgs(*CI, *callee, new_args);
                ++same_arity_fixup_count;
                continue;
              }

              auto maybe_new_args =
                  buildStateOrderedArgs(F, *CI, *callee, caller_param_offsets);
              if (!maybe_new_args)
                continue;
              replaceCallWithArgs(*CI, *callee, *maybe_new_args);
              ++fixup_count;
            }
          }
        }
        if (fixup_count > 0 || same_arity_fixup_count > 0)
          errs() << "Fixed " << fixup_count
                 << " B3 dispatch calls with mismatched arg counts and "
                 << same_arity_fixup_count
                 << " suspicious same-arity native calls\n";
      }

      syncOutlinedVirtualCalleeRegistry();


      unsigned created_hash_resolved = 0;
      unsigned created_nested_helper = 0;
      for (const auto &entry : outlined_virtual_callee_records) {
        const auto &record = entry.getValue();
        if (record.first_round != round + 1)
          continue;
        if (record.kind == "hash_resolved")
          ++created_hash_resolved;
        else if (record.kind == "nested_helper")
          ++created_nested_helper;
      }

      errs() << "Late discovery round " << (round + 1) << " complete";
      if (created_hash_resolved > 0 || created_nested_helper > 0) {
        errs() << " (outlined virtual callees: hash="
               << created_hash_resolved
               << ", nested=" << created_nested_helper << ")";
      }
      errs() << "\n";
      events.emitInfo("late_discovery_round_completed",
                      "late discovery round completed",
                      {{"round", static_cast<int64_t>(round + 1)},
                       {"outlined_hash_resolved",
                        static_cast<int64_t>(created_hash_resolved)},
                       {"outlined_nested_helper",
                        static_cast<int64_t>(created_nested_helper)},
                       {"outlined_total",
                        static_cast<int64_t>(outlined_virtual_callee_records.size())}});
    }
  }

  if (OmillTimePasses)
    TimingHandler.print();

  if (preserve_lift_infrastructure) {
    ModulePassManager MPM;
    omill::buildLiftInfrastructureCleanupPipeline(MPM);
    MPM.run(*module, MAM);
  }

  // Some late lifting/materialization shapes still leave stale PHI incoming
  // edges after CFG rewrites. Repair them before verification so no-ABI
  // checkpoints and downstream ABI replay can consume valid textual IR.
  repairMalformedPHIs(*module);
  MAM.invalidate(*module, llvm::PreservedAnalyses::none());

  // Verify (use nullptr to avoid crash in SlotTracker on corrupted modules)
  const bool debug_public_root_seeds =
      parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
  bool module_invalid_before_late_cleanup =
      verifyModule(*module, debug_public_root_seeds ? &errs() : nullptr);
  const bool allow_noabi_postmain_rounds = !module_invalid_before_late_cleanup;
  const bool allow_abi_postmain_rounds = !module_invalid_before_late_cleanup;
  if (module_invalid_before_late_cleanup) {
    errs() << "WARNING: module verification failed (use --verify-each to "
              "identify the culprit pass)\n";
    events.emitWarn("module_verify_warning",
                    "module verification failed after full run");
  }

  // Late cleanup: replace sentinel data constants with poison, DCE.
  if (!module_invalid_before_late_cleanup && !hasOpenOutputRootHazards()) {
    ModulePassManager MPM;
    omill::buildLateCleanupPipeline(MPM, opts);
    MPM.run(*module, MAM);
  } else if (events.detailed()) {
    events.emitInfo("late_cleanup_skipped_for_open_output_root",
                    module_invalid_before_late_cleanup
                        ? "skipped late cleanup for verifier-broken module"
                        : "skipped late cleanup for open output root");
  }

  if (!module_invalid_before_late_cleanup && NoABI &&
      devirtualization_plan.enable_devirtualization &&
      opts.require_remill_normalization) {
    ModulePassManager MPM;
    omill::RemillNormalizationOrchestrator normalization;
    normalization.appendToPipeline(
        MPM, omill::RemillNormalizationRequest{
                 omill::RemillNormalizationEpoch::kFinalVerification,
                 /*no_abi_mode=*/true,
                 /*aggressive_folding=*/true,
                 opts.scope_predicate,
                 /*include_semantic_helpers=*/true});
    MPM.run(*module, MAM);
    repairMalformedPHIs(*module);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  }

  auto annotateOutputRootTerminalBoundaryProbeChains = [&]() {
    if (RawBinary || NoABI)
      return;
    if (parseBoolEnv("OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE")
            .value_or(false)) {
      return;
    }

    const bool debug_terminal_probe =
        parseBoolEnv("OMILL_DEBUG_TERMINAL_BOUNDARY_SIDE_PROBE")
            .value_or(false);
    constexpr size_t kMaxUniqueProbeTargets = 4;
    constexpr unsigned kMaxProbeDepth = 4;

    llvm::SmallVector<std::pair<llvm::Function *, uint64_t>, 8> roots;
    llvm::SmallVector<uint64_t, 8> unique_targets;
    llvm::DenseSet<uint64_t> seen_targets;

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      uint64_t target_pc = 0;
      auto target_attr = F.getFnAttribute("omill.terminal_boundary_target_va");
      if (target_attr.isValid()) {
        if (target_attr.getValueAsString().getAsInteger(16, target_pc))
          target_pc = 0;
      }
      if (target_pc == 0) {
        auto candidate_attr =
            F.getFnAttribute("omill.terminal_boundary_candidate_pc");
        if (candidate_attr.isValid() &&
            !candidate_attr.getValueAsString().getAsInteger(16, target_pc)) {
          // target_pc filled from fallback candidate attr
        }
      }
      if (target_pc == 0)
        continue;
      roots.emplace_back(&F, target_pc);
      if (seen_targets.insert(target_pc).second &&
          unique_targets.size() < kMaxUniqueProbeTargets) {
        unique_targets.push_back(target_pc);
      }
    }

    if (unique_targets.empty())
      return;

    llvm::DenseMap<uint64_t, TerminalBoundaryProbeResult> probe_results;
    auto probeSingleTarget =
        [&](uint64_t target_pc) -> std::optional<TerminalBoundaryProbeResult> {
      if (auto it = probe_results.find(target_pc); it != probe_results.end())
        return it->second;

      SmallString<256> temp_ll_path;
      if (sys::fs::createTemporaryFile("omill_terminal_probe", "ll",
                                       temp_ll_path)) {
        return std::nullopt;
      }

      llvm::SmallVector<std::string, 16> arg_storage;
      arg_storage.emplace_back(argv[0]);
      arg_storage.emplace_back(InputFilename);
      arg_storage.emplace_back("--va");
      arg_storage.emplace_back(llvm::utohexstr(target_pc));
      if (opts.use_block_lifting)
        arg_storage.emplace_back("--block-lift");
      if (devirtualization_plan.enable_devirtualization)
        arg_storage.emplace_back("--devirtualize");
      if (opts.generic_static_devirtualize) {
        arg_storage.emplace_back("--generic-static-devirtualize");
      }
      arg_storage.emplace_back("-o");
      arg_storage.emplace_back(temp_ll_path.str().str());

      llvm::SmallVector<llvm::StringRef, 16> argv_refs;
      argv_refs.reserve(arg_storage.size());
      for (const auto &arg : arg_storage)
        argv_refs.push_back(arg);

      std::string err_msg;
      bool exec_failed = false;
      ScopedEnvOverride skip_nested_probe(
          "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
      int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                         std::nullopt, {}, 0, 0,
                                         &err_msg, &exec_failed);
      if (debug_terminal_probe) {
        errs() << "[terminal-side-probe] target=0x"
               << Twine::utohexstr(target_pc) << " rc=" << rc
               << " exec_failed=" << (exec_failed ? 1 : 0) << "\n";
      }
      if (rc != 0 || exec_failed) {
        sys::fs::remove(temp_ll_path);
        return std::nullopt;
      }

      auto buf_or_err = MemoryBuffer::getFile(temp_ll_path);
      sys::fs::remove(temp_ll_path);
      if (!buf_or_err)
        return std::nullopt;

      auto parsed =
          parseTerminalBoundaryProbeIR((*buf_or_err)->getBuffer(), target_pc);
      if (!parsed)
        return std::nullopt;
      probe_results[target_pc] = *parsed;
      return *parsed;
    };

    llvm::DenseMap<uint64_t, TerminalBoundaryProbeChain> probe_chains;
    for (uint64_t target_pc : unique_targets) {
      TerminalBoundaryProbeChain chain;
      chain.chain_pcs.push_back(target_pc);
      llvm::DenseMap<uint64_t, unsigned> path_index;
      path_index[target_pc] = 0;
      uint64_t current_pc = target_pc;

      for (unsigned depth = 0; depth < kMaxProbeDepth; ++depth) {
        auto single_probe = probeSingleTarget(current_pc);
        if (!single_probe || single_probe->next_target_pc == 0)
          break;

        if (single_probe->cycle && !chain.cycle)
          chain.cycle = *single_probe->cycle;
        if (single_probe->canonical_cycle_pc && !chain.canonical_cycle_pc)
          chain.canonical_cycle_pc = *single_probe->canonical_cycle_pc;

        const uint64_t next_pc = single_probe->next_target_pc;
        if (auto it = path_index.find(next_pc); it != path_index.end()) {
          llvm::SmallVector<uint64_t, 8> cycle_pcs;
          for (unsigned i = it->second; i < chain.chain_pcs.size(); ++i)
            cycle_pcs.push_back(chain.chain_pcs[i]);
          if (!cycle_pcs.empty()) {
            chain.cycle = joinHexPCChain(cycle_pcs);
            chain.canonical_cycle_pc = *llvm::min_element(cycle_pcs);
          }
          break;
        }

        chain.chain_pcs.push_back(next_pc);
        path_index[next_pc] = chain.chain_pcs.size() - 1;
        current_pc = next_pc;
      }

      probe_chains[target_pc] = std::move(chain);
    }

    if (probe_chains.empty())
      return;

    static constexpr llvm::StringLiteral kNextHopAttr =
        "omill.terminal_boundary_next_hop_target_va";
    static constexpr llvm::StringLiteral kProbeChainAttr =
        "omill.terminal_boundary_probe_chain";
    static constexpr llvm::StringLiteral kProbeCycleAttr =
        "omill.terminal_boundary_probe_cycle";
    static constexpr llvm::StringLiteral kProbeCycleLenAttr =
        "omill.terminal_boundary_probe_cycle_len";
    static constexpr llvm::StringLiteral kProbeCycleCanonicalAttr =
        "omill.terminal_boundary_probe_cycle_canonical_target_va";
    static constexpr llvm::StringLiteral kNextHopCycleAttr =
        "omill.terminal_boundary_next_hop_cycle";
    static constexpr llvm::StringLiteral kNextHopCycleCanonicalAttr =
        "omill.terminal_boundary_next_hop_cycle_canonical_target_va";
    static constexpr llvm::StringLiteral kNamedMetadata =
        "omill.terminal_boundary_probe_chains";

    if (auto *old_md = module->getNamedMetadata(kNamedMetadata))
      module->eraseNamedMetadata(old_md);
    auto *named_md = module->getOrInsertNamedMetadata(kNamedMetadata);
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);

    for (const auto &[F, target_pc] : roots) {
      auto it = probe_chains.find(target_pc);
      if (it == probe_chains.end() || it->second.chain_pcs.empty())
        continue;
      const auto &probe = it->second;
      if (probe.chain_pcs.size() >= 2)
        F->addFnAttr(kNextHopAttr, llvm::utohexstr(probe.chain_pcs[1]));
      F->addFnAttr(kProbeChainAttr, joinHexPCChain(probe.chain_pcs));
      if (probe.cycle.has_value()) {
        F->addFnAttr(kProbeCycleAttr, *probe.cycle);
        llvm::SmallVector<llvm::StringRef, 8> cycle_parts;
        llvm::StringRef(*probe.cycle).split(cycle_parts, ',');
        F->addFnAttr(kProbeCycleLenAttr, std::to_string(cycle_parts.size()));
      }
      if (probe.canonical_cycle_pc.has_value()) {
        F->addFnAttr(kProbeCycleCanonicalAttr,
                     llvm::utohexstr(*probe.canonical_cycle_pc));
      }
      if (probe.cycle.has_value())
        F->addFnAttr(kNextHopCycleAttr, *probe.cycle);
      if (probe.canonical_cycle_pc.has_value()) {
        F->addFnAttr(kNextHopCycleCanonicalAttr,
                     llvm::utohexstr(*probe.canonical_cycle_pc));
      }

      llvm::SmallVector<llvm::Metadata *, 12> fields;
      fields.push_back(llvm::MDString::get(ctx, F->getName()));
      for (uint64_t pc : probe.chain_pcs) {
        fields.push_back(llvm::ConstantAsMetadata::get(
            llvm::ConstantInt::get(i64_ty, pc)));
      }
      if (probe.cycle.has_value())
        fields.push_back(llvm::MDString::get(ctx, *probe.cycle));
      named_md->addOperand(llvm::MDTuple::get(ctx, fields));
    }
  };

  auto maybeRerunLateCleanupForCanonicalTerminalBoundaryCycle = [&]() {
    if (RawBinary || NoABI)
      return;

    auto parseFnHexAttr = [](const llvm::Function &F,
                             llvm::StringRef name) -> std::optional<uint64_t> {
      auto attr = F.getFnAttribute(name);
      if (!attr.isValid())
        return std::nullopt;
      uint64_t value = 0;
      if (attr.getValueAsString().getAsInteger(16, value) || value == 0)
        return std::nullopt;
      return value;
    };

    bool need_rerun = false;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      auto canonical_pc = parseFnHexAttr(
          F, "omill.terminal_boundary_probe_cycle_canonical_target_va");
      if (!canonical_pc)
        continue;

      auto current_pc =
          parseFnHexAttr(F, "omill.terminal_boundary_target_va");
      if (!current_pc)
        current_pc =
            parseFnHexAttr(F, "omill.terminal_boundary_candidate_pc");
      if (!current_pc || *current_pc == *canonical_pc)
        continue;

      need_rerun = true;
      break;
    }

    if (!need_rerun)
      return;

    if (events.enabled()) {
      events.emitInfo("late_cleanup_rerun_started",
                      "rerunning late cleanup for canonical boundary cycles");
    }
    ModulePassManager MPM;
    omill::buildLateCleanupPipeline(MPM, opts);
    MPM.run(*module, MAM);
  };

  auto clearTerminalBoundaryAttrs = [&](llvm::Function &F) {
    static constexpr llvm::StringLiteral kAttrs[] = {
        "omill.terminal_boundary_count",
        "omill.terminal_boundary_summary",
        "omill.terminal_boundary_kind",
        "omill.terminal_boundary_target_va",
        "omill.terminal_boundary_nearby_entry_va",
        "omill.terminal_boundary_candidate_pc",
        "omill.terminal_boundary_original_target_va",
        "omill.terminal_boundary_cycle",
        "omill.terminal_boundary_cycle_len",
        "omill.terminal_boundary_cycle_canonical_target_va",
        "omill.terminal_boundary_next_hop_target_va",
        "omill.terminal_boundary_probe_chain",
        "omill.terminal_boundary_probe_cycle",
        "omill.terminal_boundary_probe_cycle_len",
        "omill.terminal_boundary_probe_cycle_canonical_target_va",
        "omill.terminal_boundary_next_hop_cycle",
        "omill.terminal_boundary_next_hop_cycle_canonical_target_va",
    };
    for (auto attr_name : kAttrs)
      F.removeFnAttr(attr_name);
  };

  const bool debug_secondary_recovery =
      parseBoolEnv("OMILL_DEBUG_TERMINAL_BOUNDARY_SECONDARY_ROOT_RECOVERY")
          .value_or(false);

  auto setTerminalBoundaryRecoveryAttrs =
      [&](llvm::Function &F, const TerminalBoundaryRecoveryAttempt &attempt) {
        F.addFnAttr("omill.terminal_boundary_recovery_status",
                    omill::terminalBoundaryRecoveryStatusName(attempt.status));
        F.addFnAttr("omill.terminal_boundary_recovery_target_va",
                    llvm::utohexstr(attempt.target_pc));
        F.addFnAttr("omill.terminal_boundary_recovery_summary",
                    attempt.summary);
      };

  struct TerminalBoundaryChildLiftResult {
    std::string ir_text;
    std::string model_text;
  };

  auto runTerminalBoundaryChildLift =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode,
          bool dump_virtual_model) -> std::optional<TerminalBoundaryChildLiftResult> {
        SmallString<256> temp_ll_path;
        if (sys::fs::createTemporaryFile("omill_terminal_recovery", "ll",
                                         temp_ll_path)) {
          return std::nullopt;
        }

        SmallString<256> temp_model_path;
        if (dump_virtual_model &&
            sys::fs::createTemporaryFile("omill_terminal_recovery", "model",
                                         temp_model_path)) {
          sys::fs::remove(temp_ll_path);
          return std::nullopt;
        }

        llvm::SmallVector<std::string, 16> arg_storage;
        arg_storage.emplace_back(argv[0]);
        arg_storage.emplace_back(InputFilename);
        arg_storage.emplace_back("--va");
        arg_storage.emplace_back(llvm::utohexstr(target_pc));
        if (opts.use_block_lifting)
          arg_storage.emplace_back("--block-lift");
        if (devirtualization_plan.enable_devirtualization)
          arg_storage.emplace_back("--devirtualize");
        if (no_abi)
          arg_storage.emplace_back("--no-abi");
        if (enable_gsd)
          arg_storage.emplace_back("--generic-static-devirtualize");
        arg_storage.emplace_back("-o");
        arg_storage.emplace_back(temp_ll_path.str().str());

        llvm::SmallVector<llvm::StringRef, 16> argv_refs;
        argv_refs.reserve(arg_storage.size());
        for (const auto &arg : arg_storage)
          argv_refs.push_back(arg);

        std::string err_msg;
        bool exec_failed = false;
        ScopedEnvOverride skip_nested_probe(
            "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
        ScopedEnvOverride skip_late_output_target(
            "OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN", "1");
        ScopedEnvOverride skip_late_boundary_rerun(
            "OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN", "1");
        std::unique_ptr<ScopedEnvOverride> skip_always_inline;
        if (no_abi || enable_recovery_mode) {
          skip_always_inline = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_ALWAYS_INLINE", "1");
        }
        std::unique_ptr<ScopedEnvOverride> recovery_mode_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_root_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_max_reachable_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_max_iterations_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_max_target_rounds_guard;
        std::unique_ptr<ScopedEnvOverride> dump_model_guard;
        std::unique_ptr<ScopedEnvOverride> skip_block_merge_guard;
        std::optional<std::string> recovery_root_value;
        if (parseBoolEnv("OMILL_TERMINAL_BOUNDARY_CHILD_SKIP_BLOCK_MERGE")
                .value_or(false)) {
          skip_block_merge_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_BLOCK_MERGE", "1");
        }
        if (enable_recovery_mode) {
          recovery_root_value = llvm::utohexstr(target_pc);
          recovery_mode_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_TERMINAL_BOUNDARY_RECOVERY", "1");
          recovery_root_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA",
              recovery_root_value->c_str());
          recovery_max_reachable_guard =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE", "128");
          recovery_max_iterations_guard =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_ITERATIONS", "8");
          recovery_max_target_rounds_guard =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_NEW_TARGET_ROUNDS",
                  "6");
        }
        if (dump_virtual_model) {
          dump_model_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_DUMP_VIRTUAL_MODEL", temp_model_path.str().str().c_str());
        }

        const unsigned timeout_seconds =
            enable_recovery_mode
                ? parseUnsignedEnv(
                      "OMILL_TERMINAL_BOUNDARY_RECOVERY_TIMEOUT_SECONDS")
                      .value_or(420u)
                : 180u;
        auto child_begin = std::chrono::steady_clock::now();
        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] child-start target=0x"
                 << llvm::utohexstr(target_pc)
                 << " no_abi=" << (no_abi ? 1 : 0)
                 << " gsd=" << (enable_gsd ? 1 : 0)
                 << " recovery=" << (enable_recovery_mode ? 1 : 0)
                 << " dump_model=" << (dump_virtual_model ? 1 : 0) << "\n";
        }
        int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                           std::nullopt, {}, timeout_seconds, 0,
                                           &err_msg, &exec_failed);
        if (debug_secondary_recovery) {
          auto elapsed_ms =
              std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - child_begin)
                  .count();
          errs() << "[terminal-recovery] child-done target=0x"
                 << llvm::utohexstr(target_pc)
                 << " rc=" << rc
                 << " exec_failed=" << (exec_failed ? 1 : 0)
                 << " elapsed_ms=" << elapsed_ms << "\n";
        }
        if (rc != 0 || exec_failed) {
          sys::fs::remove(temp_ll_path);
          if (dump_virtual_model)
            sys::fs::remove(temp_model_path);
          return std::nullopt;
        }

        auto buf_or_err = MemoryBuffer::getFile(temp_ll_path);
        sys::fs::remove(temp_ll_path);
        if (!buf_or_err) {
          if (dump_virtual_model)
            sys::fs::remove(temp_model_path);
          return std::nullopt;
        }

        TerminalBoundaryChildLiftResult result;
        result.ir_text = (*buf_or_err)->getBuffer().str();
        if (dump_virtual_model) {
          auto model_or_err = MemoryBuffer::getFile(temp_model_path);
          sys::fs::remove(temp_model_path);
          if (model_or_err)
            result.model_text = (*model_or_err)->getBuffer().str();
        }
        return result;
      };

  auto importSimpleExecutableChildRoot =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &import_plan,
          llvm::StringRef name_prefix) -> llvm::Function * {
        llvm::StringRef imported_ir = artifact.ir_text;
        llvm::SMDiagnostic parse_error;
        auto imported_module =
            llvm::parseAssemblyString(imported_ir, parse_error, ctx);
        if (!imported_module) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-parse-failed target=0x"
                   << llvm::utohexstr(target_pc) << "\n";
          }
          return nullptr;
        }

        auto findImportedRootByPc = [&](llvm::Module &M,
                                        uint64_t pc) -> llvm::Function * {
          const std::string target_hex = llvm::utohexstr(pc);
          const std::string target_hex_lower =
              llvm::StringRef(target_hex).lower();
          for (const std::string &name :
               {"sub_" + target_hex, "sub_" + target_hex_lower,
                "blk_" + target_hex, "blk_" + target_hex_lower,
                "block_" + target_hex, "block_" + target_hex_lower}) {
            if (auto *fn = M.getFunction(name); fn && !fn->isDeclaration())
              return fn;
          }
          for (auto &F : M) {
            if (F.isDeclaration())
              continue;
            if (omill::extractEntryVA(F.getName()) == pc ||
                omill::extractBlockPC(F.getName()) == pc) {
              return &F;
            }
          }
          return nullptr;
        };

        const uint64_t selected_root_pc =
            artifact.selected_root_pc.value_or(target_pc);
        auto *root = findImportedRootByPc(*imported_module, selected_root_pc);
        if (!root || root->isDeclaration()) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-root-missing target=0x"
                   << llvm::utohexstr(target_pc)
                   << " selected=0x" << llvm::utohexstr(selected_root_pc)
                   << "\n";
          }
          return nullptr;
        }

        auto makeUniqueImportName = [&](llvm::StringRef base_name) {
          std::string candidate = (name_prefix + base_name).str();
          if (!module->getFunction(candidate) &&
              !imported_module->getFunction(candidate)) {
            return candidate;
          }
          for (unsigned i = 1; i < 100; ++i) {
            auto numbered = candidate + "." + std::to_string(i);
            if (!module->getFunction(numbered) &&
                !imported_module->getFunction(numbered)) {
              return numbered;
            }
          }
          return candidate;
        };

        auto makeTargetImportBaseName = [&](llvm::StringRef source_name) {
          std::string target_hex = llvm::utohexstr(target_pc);
          if (source_name.starts_with("blk_"))
            return (llvm::Twine("blk_") + target_hex).str();
          if (source_name.starts_with("block_"))
            return (llvm::Twine("block_") + target_hex).str();
          return (llvm::Twine("sub_") + target_hex).str();
        };

        auto clearImportedAttrs = [&](llvm::Function &F) {
          clearTerminalBoundaryAttrs(F);
          F.removeFnAttr("omill.output_root");
          F.removeFnAttr("omill.internal_output_root");
          F.removeFnAttr("omill.closed_root_slice");
          F.removeFnAttr("omill.closed_root_slice_root");
          F.removeFnAttr("omill.vm_unresolved_continuation_count");
          F.removeFnAttr("omill.vm_unresolved_continuation_targets");
          F.removeFnAttr("omill.vm_unresolved_continuation_summary");
        };
        auto isStructuralImportedFunction = [&](llvm::StringRef name) {
          return name.starts_with("sub_") || name.starts_with("blk_") ||
                 name.starts_with("block_") || name.starts_with("__lifted_");
        };
        auto isAllowedModeledBoundaryDecl = [&](llvm::StringRef name) {
          return name.starts_with("omill_executable_target_") ||
                 name.starts_with("omill_native_target_") ||
                 name.starts_with("omill_vm_enter_target_") ||
                 name.starts_with("omill_native_boundary_") ||
                 name.starts_with("omill_vm_enter_boundary_");
        };
        llvm::StringSet<> allowed_decl_callees;
        for (const auto &name : import_plan.allowed_declaration_callees)
          allowed_decl_callees.insert(name);

        llvm::StringSet<> allowed_slice_names;
        for (const auto &name : artifact.closed_slice_function_names) {
          allowed_slice_names.insert(name);
        }

        llvm::SmallVector<llvm::Function *, 16> closure;
        llvm::SmallVector<llvm::Function *, 16> worklist;
        llvm::SmallPtrSet<llvm::Function *, 16> visited;
        worklist.push_back(root);
        while (!worklist.empty()) {
          auto *F = worklist.pop_back_val();
          if (!F || F->isDeclaration() || !visited.insert(F).second)
            continue;
          if (!allowed_slice_names.empty() &&
              isStructuralImportedFunction(F->getName()) &&
              !allowed_slice_names.count(F->getName())) {
            if (debug_secondary_recovery) {
              errs() << "[terminal-recovery] exec-import-disallowed-fn target=0x"
                     << llvm::utohexstr(target_pc)
                     << " selected=0x" << llvm::utohexstr(selected_root_pc)
                     << " fn=" << F->getName() << "\n";
            }
            return nullptr;
          }
          closure.push_back(F);
          for (auto &BB : *F) {
            for (auto &I : BB) {
              for (llvm::Value *operand : I.operands()) {
                auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                if (!GV)
                  continue;
                if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                  if (callee->isDeclaration()) {
                    if (callee->isIntrinsic() ||
                        callee->getName().starts_with("llvm.") ||
                        isAllowedModeledBoundaryDecl(callee->getName()) ||
                        allowed_decl_callees.count(callee->getName())) {
                      continue;
                    }
                    if (debug_secondary_recovery) {
                      errs() << "[terminal-recovery] exec-import-decl-reject target=0x"
                             << llvm::utohexstr(target_pc)
                             << " selected=0x" << llvm::utohexstr(selected_root_pc)
                             << " callee=" << callee->getName() << "\n";
                    }
                    return nullptr;
                  }
                  worklist.push_back(callee);
                  continue;
                }
                if (auto *global = llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                  if (!global->isDeclaration() &&
                      !global->getName().starts_with("llvm.")) {
                    if (debug_secondary_recovery) {
                      errs() << "[terminal-recovery] exec-import-global-reject target=0x"
                             << llvm::utohexstr(target_pc)
                             << " selected=0x" << llvm::utohexstr(selected_root_pc)
                             << " global=" << global->getName() << "\n";
                    }
                    return nullptr;
                  }
                }
              }
            }
          }
        }
        if (closure.empty()) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-empty-closure target=0x"
                   << llvm::utohexstr(target_pc)
                   << " selected=0x" << llvm::utohexstr(selected_root_pc)
                   << "\n";
          }
          return nullptr;
        }

        llvm::DenseMap<const llvm::Function *, llvm::Function *> cloned;
        llvm::DenseMap<const llvm::GlobalValue *, llvm::GlobalValue *> decl_map;
        llvm::Function *dst_root = nullptr;
        for (auto *src_fn : closure) {
          std::string import_base_name_storage;
          llvm::StringRef import_base_name;
          if (src_fn == root) {
            import_base_name_storage =
                makeTargetImportBaseName(src_fn->getName());
            import_base_name = import_base_name_storage;
          } else {
            import_base_name = src_fn->getName();
          }
          auto *dst_fn = llvm::Function::Create(
              src_fn->getFunctionType(), llvm::GlobalValue::InternalLinkage,
              makeUniqueImportName(import_base_name), *module);
          dst_fn->copyAttributesFrom(src_fn);
          clearImportedAttrs(*dst_fn);
          cloned[src_fn] = dst_fn;
          if (src_fn == root)
            dst_root = dst_fn;
        }
        if (!dst_root) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-no-dst-root target=0x"
                   << llvm::utohexstr(target_pc)
                   << " selected=0x" << llvm::utohexstr(selected_root_pc)
                   << "\n";
          }
          return nullptr;
        }

        for (auto *src_fn : closure) {
          for (auto &BB : *src_fn) {
            for (auto &I : BB) {
              for (llvm::Value *operand : I.operands()) {
                auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                if (!GV || decl_map.count(GV))
                  continue;
                if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                  if (auto it = cloned.find(callee); it != cloned.end()) {
                    decl_map[GV] = it->second;
                    continue;
                  }
                  auto *decl = module->getFunction(callee->getName());
                  if (!decl) {
                    decl = llvm::Function::Create(
                        callee->getFunctionType(), callee->getLinkage(),
                        callee->getName(), *module);
                    decl->copyAttributesFrom(callee);
                  }
                  decl_map[GV] = decl;
                }
              }
            }
          }
        }

        for (auto *src_fn : closure) {
          auto *dst_fn = cloned.lookup(src_fn);
          llvm::ValueToValueMapTy vmap;
          auto src_arg_it = src_fn->arg_begin();
          auto dst_arg_it = dst_fn->arg_begin();
          for (; src_arg_it != src_fn->arg_end() &&
                 dst_arg_it != dst_fn->arg_end();
               ++src_arg_it, ++dst_arg_it) {
            vmap[&*src_arg_it] = &*dst_arg_it;
          }
          for (const auto &decl_entry : decl_map)
            vmap[const_cast<llvm::GlobalValue *>(decl_entry.first)] =
                decl_entry.second;
          llvm::SmallVector<llvm::ReturnInst *, 4> returns;
          llvm::CloneFunctionInto(
              dst_fn, src_fn, vmap,
              llvm::CloneFunctionChangeType::DifferentModule, returns);
          clearImportedAttrs(*dst_fn);
        }

        omill::ExecutableTargetFact fact;
        fact.raw_target_pc = target_pc;
        fact.effective_target_pc = selected_root_pc;
        fact.kind = omill::ExecutableTargetKind::kLiftableEntry;
        fact.trust = omill::ExecutableTargetTrust::kTrustedEntry;
        if (selected_root_pc != target_pc)
          fact.canonical_owner_pc = selected_root_pc;
        writeExecutableTargetFact(*dst_root, fact);
        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] exec-import-ok target=0x"
                 << llvm::utohexstr(target_pc)
                 << " selected=0x" << llvm::utohexstr(selected_root_pc)
                 << " root=" << dst_root->getName()
                 << " funcs=" << closure.size() << "\n";
        }
        return dst_root;
      };

  auto importRecoveredTerminalBoundaryFunction =
      [&](llvm::StringRef abi_ir_text,
          uint64_t target_pc,
          std::string *rejection_reason = nullptr) -> llvm::Function * {
        llvm::SMDiagnostic parse_error;
        auto imported_module =
            llvm::parseAssemblyString(abi_ir_text, parse_error, ctx);
        if (!imported_module) {
          if (rejection_reason)
            *rejection_reason = "parse_failed";
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-parse-failed target=0x"
                   << llvm::utohexstr(target_pc) << "\n";
          }
          return nullptr;
        }

        auto classifyImportedRootRisk =
            [&](llvm::Function &F) -> std::optional<std::string> {
              bool uses_any_arg = false;
              for (auto &arg : F.args()) {
                if (!arg.use_empty()) {
                  uses_any_arg = true;
                  break;
                }
              }

              bool has_normal_return = false;
              bool has_unreachable = false;
              bool saw_non_intrinsic_call = false;
              bool saw_memory_access = false;
              bool saw_other_work = false;
              llvm::Constant *returned_constant = nullptr;
              bool returned_nonconstant_or_mixed = false;

              for (auto &BB : F) {
                if (llvm::isa<llvm::UnreachableInst>(BB.getTerminator()))
                  has_unreachable = true;

                for (auto &I : BB) {
                  if (llvm::isa<llvm::DbgInfoIntrinsic>(I))
                    continue;
                  if (llvm::isa<llvm::AllocaInst>(I))
                    continue;
                  if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(&I)) {
                    if (II->getIntrinsicID() == llvm::Intrinsic::lifetime_start ||
                        II->getIntrinsicID() == llvm::Intrinsic::lifetime_end ||
                        II->getIntrinsicID() == llvm::Intrinsic::memset) {
                      continue;
                    }
                  }

                  if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
                    has_normal_return = true;
                    auto *RV = RI->getReturnValue();
                    if (!RV) {
                      returned_nonconstant_or_mixed = true;
                    } else if (auto *C = llvm::dyn_cast<llvm::Constant>(RV)) {
                      if (!returned_constant)
                        returned_constant = C;
                      else if (returned_constant != C)
                        returned_nonconstant_or_mixed = true;
                    } else {
                      returned_nonconstant_or_mixed = true;
                    }
                    continue;
                  }

                  if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
                    auto *callee = CB->getCalledFunction();
                    if (!callee) {
                      saw_other_work = true;
                      continue;
                    }
                    auto callee_name = callee->getName();
                    if (callee_name == "__omill_missing_block_handler" ||
                        callee_name == "__remill_sync_hyper_call" ||
                        callee_name.contains("HandleUnsupported")) {
                      return std::string("unsupported_root");
                    }
                    if (!callee->isIntrinsic() &&
                        !callee_name.starts_with("llvm.")) {
                      saw_non_intrinsic_call = true;
                    }
                    continue;
                  }

                  if (llvm::isa<llvm::LoadInst>(I) ||
                      llvm::isa<llvm::StoreInst>(I)) {
                    saw_memory_access = true;
                    continue;
                  }

                  saw_other_work = true;
                }
              }

              if (!has_normal_return && has_unreachable)
                return std::string("nonreturning_root");

              if (has_normal_return && !uses_any_arg && !saw_non_intrinsic_call &&
                  !saw_memory_access && !saw_other_work && returned_constant &&
                  !returned_nonconstant_or_mixed) {
                return std::string("trivial_constant_root");
              }

              return std::nullopt;
            };

        auto resolveImportedRoot = [&](llvm::Module &M) -> llvm::Function * {
          auto pickUnique =
              [](llvm::ArrayRef<llvm::Function *> candidates)
              -> llvm::Function * {
            return candidates.size() == 1 ? candidates.front() : nullptr;
          };

          const std::string target_hex = llvm::utohexstr(target_pc);
          auto lookupDefined = [&](llvm::StringRef name) -> llvm::Function * {
            auto *F = M.getFunction(name);
            return (F && !F->isDeclaration()) ? F : nullptr;
          };
          auto findExactLiftedRoot = [&]() -> llvm::Function * {
            for (auto &F : M) {
              if (F.isDeclaration())
                continue;
              if (omill::extractEntryVA(F.getName()) == target_pc ||
                  omill::extractBlockPC(F.getName()) == target_pc) {
                return &F;
              }
            }
            if (auto *F = lookupDefined(omill::liftedFunctionName(target_pc)))
              return F;
            return nullptr;
          };
          auto findExactNativeRoot = [&]() -> llvm::Function * {
            if (auto *F = lookupDefined("sub_" + target_hex + "_native"))
              return F;
            if (auto *F = lookupDefined("blk_" + target_hex + "_native"))
              return F;
            return nullptr;
          };

          if (auto *F = findExactLiftedRoot())
            return F;
          if (auto *F = findExactNativeRoot())
            return F;

          llvm::SmallVector<llvm::Function *, 8> target_native_roots;
          llvm::SmallVector<llvm::Function *, 8> target_lifted_roots;
          llvm::SmallVector<llvm::Function *, 8> output_roots;
          llvm::SmallVector<llvm::Function *, 8> non_native_functions;
          llvm::SmallVector<llvm::Function *, 8> native_functions;
          llvm::SmallVector<llvm::Function *, 8> defined_functions;
          for (auto &F : M) {
            if (F.isDeclaration())
              continue;
            defined_functions.push_back(&F);
            if (F.getName().ends_with("_native"))
              native_functions.push_back(&F);
            else
              non_native_functions.push_back(&F);
            if (F.hasFnAttribute("omill.output_root"))
              output_roots.push_back(&F);
            if (!F.getName().contains(target_hex))
              continue;
            if (F.getName().ends_with("_native"))
              target_native_roots.push_back(&F);
            else
              target_lifted_roots.push_back(&F);
          }

          if (auto *F = pickUnique(output_roots))
            return F;
          if (auto *F = pickUnique(target_lifted_roots))
            return F;
          if (auto *F = pickUnique(target_native_roots))
            return F;
          if (auto *F = pickUnique(non_native_functions))
            return F;
          if (auto *F = pickUnique(native_functions))
            return F;
          if (auto *F = pickUnique(defined_functions))
            return F;
          return nullptr;
        };

        auto *imported_root = resolveImportedRoot(*imported_module);
        if (!imported_root) {
          if (rejection_reason)
            *rejection_reason = "root_missing";
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-root-missing target=0x"
                   << llvm::utohexstr(target_pc) << " candidates=";
            bool first = true;
            for (auto &F : *imported_module) {
              if (F.isDeclaration())
                continue;
              if (!first)
                errs() << ",";
              errs() << F.getName();
              if (F.hasFnAttribute("omill.output_root"))
                errs() << "[root]";
              first = false;
            }
            errs() << "\n";
          }
          return nullptr;
        }

        if (auto risk = classifyImportedRootRisk(*imported_root)) {
          if (rejection_reason)
            *rejection_reason = *risk;
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-root-rejected target=0x"
                   << llvm::utohexstr(target_pc)
                   << " root=" << imported_root->getName()
                   << " reason=" << *risk << "\n";
          }
          return nullptr;
        }

        auto canCloneStandaloneRoot = [&](llvm::Function &F) {
          for (auto &BB : F) {
            for (auto &I : BB) {
              for (llvm::Value *operand : I.operands()) {
                auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                if (!GV)
                  continue;
                if (GV == &F)
                  continue;
                if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                  if (!callee->isDeclaration())
                    return false;
                  continue;
                }
                if (auto *global = llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                  if (!global->isDeclaration() &&
                      !global->getName().starts_with("llvm.")) {
                    return false;
                  }
                }
              }
            }
          }
          return true;
        };

        auto cloneStandaloneRoot = [&](llvm::Function &src,
                                       llvm::StringRef new_name)
            -> llvm::Function * {
          auto clearImportedRootOnlyAttrs = [&](llvm::Function &F) {
            clearTerminalBoundaryAttrs(F);
            F.removeFnAttr("omill.output_root");
            F.removeFnAttr("omill.closed_root_slice");
            F.removeFnAttr("omill.closed_root_slice_root");
            F.removeFnAttr("omill.param_state_offsets");
            F.removeFnAttr("omill.terminal_boundary_recovery_status");
            F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
            F.removeFnAttr("omill.terminal_boundary_recovery_summary");
          };

          auto *dst = module->getFunction(new_name);
          if (!dst) {
            dst = llvm::Function::Create(src.getFunctionType(),
                                         llvm::GlobalValue::InternalLinkage,
                                         new_name, *module);
          }
          if (!dst->empty())
            dst->deleteBody();
          dst->copyAttributesFrom(&src);
          dst->setName(new_name);
          dst->setLinkage(llvm::GlobalValue::InternalLinkage);
          clearImportedRootOnlyAttrs(*dst);

          llvm::ValueToValueMapTy vmap;
          auto src_arg_it = src.arg_begin();
          auto dst_arg_it = dst->arg_begin();
          for (; src_arg_it != src.arg_end() && dst_arg_it != dst->arg_end();
               ++src_arg_it, ++dst_arg_it) {
            vmap[&*src_arg_it] = &*dst_arg_it;
          }
          llvm::SmallVector<llvm::ReturnInst *, 8> returns;
          llvm::CloneFunctionInto(
              dst, &src, vmap,
              llvm::CloneFunctionChangeType::DifferentModule, returns);
          clearImportedRootOnlyAttrs(*dst);
          return dst;
        };

        auto collectDefinedFunctionClosure =
            [&](llvm::Function &root,
                llvm::SmallVectorImpl<llvm::Function *> &closure) {
              llvm::SmallVector<llvm::Function *, 16> worklist;
              llvm::DenseSet<llvm::Function *> visited;
              worklist.push_back(&root);
              while (!worklist.empty()) {
                auto *F = worklist.pop_back_val();
                if (!F || F->isDeclaration() || !visited.insert(F).second)
                  continue;
                closure.push_back(F);
                for (auto &BB : *F) {
                  for (auto &I : BB) {
                    for (llvm::Value *operand : I.operands()) {
                      auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                      if (!GV)
                        continue;
                      if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                        if (!callee->isDeclaration())
                          worklist.push_back(callee);
                        continue;
                      }
                      if (auto *global =
                              llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                        if (!global->isDeclaration() &&
                            !global->getName().starts_with("llvm.")) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
              return true;
            };

        auto make_unique_import_name = [&](llvm::StringRef base_name) {
          std::string candidate = ("tbrec_" + base_name).str();
          if (!module->getFunction(candidate) &&
              !imported_module->getFunction(candidate)) {
            return candidate;
          }
          for (unsigned i = 1; i < 100; ++i) {
            auto numbered = (candidate + "." + std::to_string(i));
            if (!module->getFunction(numbered) &&
                !imported_module->getFunction(numbered)) {
              return numbered;
            }
          }
          return candidate;
        };

        auto cloneFunctionClosure =
            [&](llvm::ArrayRef<llvm::Function *> sources,
                llvm::Function &root) -> llvm::Function * {
              auto clearImportedRootOnlyAttrs = [&](llvm::Function &F) {
                clearTerminalBoundaryAttrs(F);
                F.removeFnAttr("omill.output_root");
                F.removeFnAttr("omill.closed_root_slice");
                F.removeFnAttr("omill.closed_root_slice_root");
                F.removeFnAttr("omill.param_state_offsets");
                F.removeFnAttr("omill.terminal_boundary_recovery_status");
                F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
                F.removeFnAttr("omill.terminal_boundary_recovery_summary");
              };

              llvm::DenseMap<const llvm::Function *, llvm::Function *>
                  cloned_funcs;
              llvm::DenseMap<const llvm::GlobalValue *, llvm::GlobalValue *>
                  decl_map;
              llvm::Function *cloned_root = nullptr;

              for (auto *src_fn : sources) {
                auto clone_name = make_unique_import_name(src_fn->getName());
                auto *dst_fn = llvm::Function::Create(
                    src_fn->getFunctionType(),
                    llvm::GlobalValue::InternalLinkage, clone_name, *module);
                dst_fn->copyAttributesFrom(src_fn);
                clearImportedRootOnlyAttrs(*dst_fn);
                cloned_funcs[src_fn] = dst_fn;
                if (src_fn == &root)
                  cloned_root = dst_fn;
              }

              for (auto *src_fn : sources) {
                for (auto &BB : *src_fn) {
                  for (auto &I : BB) {
                    for (llvm::Value *operand : I.operands()) {
                      auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                      if (!GV || decl_map.count(GV))
                        continue;
                      if (cloned_funcs.count(
                              llvm::dyn_cast<llvm::Function>(GV))) {
                        continue;
                      }
                      if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                        if (callee->isDeclaration()) {
                          auto *decl = module->getFunction(callee->getName());
                          if (!decl) {
                            decl = llvm::Function::Create(
                                callee->getFunctionType(),
                                callee->getLinkage(), callee->getName(),
                                *module);
                          }
                          decl->copyAttributesFrom(callee);
                          decl->setCallingConv(callee->getCallingConv());
                          decl_map[callee] = decl;
                        }
                        continue;
                      }
                      if (auto *global =
                              llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                        if (global->isDeclaration()) {
                          auto *decl =
                              module->getGlobalVariable(global->getName());
                          if (!decl) {
                            decl = new llvm::GlobalVariable(
                                *module, global->getValueType(),
                                global->isConstant(), global->getLinkage(),
                                nullptr, global->getName(), nullptr,
                                global->getThreadLocalMode(),
                                global->getAddressSpace());
                          }
                          decl_map[global] = decl;
                        }
                      }
                    }
                  }
                }
              }

              for (auto *src_fn : sources) {
                auto *dst_fn = cloned_funcs.lookup(src_fn);
                llvm::ValueToValueMapTy vmap;
                auto src_arg_it = src_fn->arg_begin();
                auto dst_arg_it = dst_fn->arg_begin();
                for (; src_arg_it != src_fn->arg_end() &&
                       dst_arg_it != dst_fn->arg_end();
                     ++src_arg_it, ++dst_arg_it) {
                  vmap[&*src_arg_it] = &*dst_arg_it;
                }
                for (const auto &entry : cloned_funcs)
                  vmap[entry.first] = entry.second;
                for (const auto &entry : decl_map)
                  vmap[entry.first] = entry.second;
                llvm::SmallVector<llvm::ReturnInst *, 8> returns;
                llvm::CloneFunctionInto(
                    dst_fn, src_fn, vmap,
                    llvm::CloneFunctionChangeType::DifferentModule, returns);
                clearImportedRootOnlyAttrs(*dst_fn);
              }

              return cloned_root;
            };

        std::string imported_root_name;
        {
          auto clone_name = make_unique_import_name(imported_root->getName());
          if (canCloneStandaloneRoot(*imported_root)) {
            if (auto *cloned = cloneStandaloneRoot(*imported_root, clone_name)) {
              if (debug_secondary_recovery) {
                errs() << "[terminal-recovery] import-clone-ok target=0x"
                       << llvm::utohexstr(target_pc)
                       << " root=" << clone_name << "\n";
              }
              return cloned;
            }
          }
        }
        {
          llvm::SmallVector<llvm::Function *, 16> closure;
          if (collectDefinedFunctionClosure(*imported_root, closure)) {
            if (auto *cloned = cloneFunctionClosure(closure, *imported_root)) {
              if (debug_secondary_recovery) {
                errs() << "[terminal-recovery] import-closure-clone-ok target=0x"
                       << llvm::utohexstr(target_pc)
                       << " root=" << cloned->getName()
                       << " functions=" << closure.size() << "\n";
              }
              return cloned;
            }
          }
        }
        for (auto &F : *imported_module) {
          if (F.isDeclaration())
            continue;
          auto old_name = F.getName().str();
          auto new_name = make_unique_import_name(old_name);
          if (&F == imported_root)
            imported_root_name = new_name;
          F.setName(new_name);
          clearTerminalBoundaryAttrs(F);
          F.removeFnAttr("omill.output_root");
          F.removeFnAttr("omill.closed_root_slice");
          F.removeFnAttr("omill.closed_root_slice_root");
          F.removeFnAttr("omill.terminal_boundary_recovery_status");
          F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
          F.removeFnAttr("omill.terminal_boundary_recovery_summary");
          if (!F.hasLocalLinkage())
            F.setLinkage(llvm::GlobalValue::InternalLinkage);
        }

        for (auto &G : imported_module->globals()) {
          if (G.isDeclaration())
            continue;
          if (G.getName().starts_with("llvm."))
            continue;
          auto new_name = make_unique_import_name(G.getName());
          G.setName(new_name);
          if (!G.hasLocalLinkage())
            G.setLinkage(llvm::GlobalValue::InternalLinkage);
        }

        if (auto *ctors = imported_module->getGlobalVariable("llvm.global_ctors"))
          ctors->eraseFromParent();
        if (auto *dtors = imported_module->getGlobalVariable("llvm.global_dtors"))
          dtors->eraseFromParent();
        if (auto *flags = imported_module->getNamedMetadata("llvm.module.flags"))
          flags->eraseFromParent();
        if (auto *ident = imported_module->getNamedMetadata("llvm.ident"))
          ident->eraseFromParent();
        if (auto *dbg = imported_module->getNamedMetadata("llvm.dbg.cu"))
          dbg->eraseFromParent();

        llvm::Linker linker(*module);
        if (linker.linkInModule(std::move(imported_module),
                                llvm::Linker::Flags::None)) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-link-failed target=0x"
                   << llvm::utohexstr(target_pc)
                   << " root=" << imported_root_name << "\n";
          }
          return nullptr;
        }

        auto *linked = module->getFunction(imported_root_name);
        if (!linked || linked->isDeclaration()) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-link-missing target=0x"
                   << llvm::utohexstr(target_pc)
                   << " root=" << imported_root_name << "\n";
          }
          return nullptr;
        }
        if (!linked->hasLocalLinkage())
          linked->setLinkage(llvm::GlobalValue::InternalLinkage);
        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] import-ok target=0x"
                 << llvm::utohexstr(target_pc)
                 << " root=" << imported_root_name << "\n";
        }
        return linked;
      };

  auto recoverABIForTerminalBoundaryIR =
      [&](llvm::StringRef noabi_ir_text) -> std::optional<std::string> {
        auto runExternalRecoverABI = [&]() -> std::optional<std::string> {
          llvm::SmallString<256> opt_path(argv[0]);
          llvm::sys::path::remove_filename(opt_path);
          llvm::sys::path::remove_filename(opt_path);
          llvm::sys::path::append(opt_path, "omill-opt", "omill-opt.exe");
          if (!llvm::sys::fs::exists(opt_path))
            return std::nullopt;

          llvm::SmallString<256> temp_in_path;
          llvm::SmallString<256> temp_out_path;
          if (llvm::sys::fs::createTemporaryFile(
                  "omill_terminal_recovery_in", "ll", temp_in_path)) {
            return std::nullopt;
          }
          if (llvm::sys::fs::createTemporaryFile(
                  "omill_terminal_recovery_out", "ll", temp_out_path)) {
            llvm::sys::fs::remove(temp_in_path);
            return std::nullopt;
          }

          {
            std::error_code ec;
            llvm::raw_fd_ostream os(temp_in_path, ec, llvm::sys::fs::OF_Text);
            if (ec) {
              llvm::sys::fs::remove(temp_in_path);
              llvm::sys::fs::remove(temp_out_path);
              return std::nullopt;
            }
            os << noabi_ir_text;
          }

          llvm::SmallVector<std::string, 8> arg_storage;
          arg_storage.emplace_back(opt_path.str().str());
          arg_storage.emplace_back("--only-recover-abi");
          arg_storage.emplace_back(temp_in_path.str().str());
          arg_storage.emplace_back("-o");
          arg_storage.emplace_back(temp_out_path.str().str());

          llvm::SmallVector<llvm::StringRef, 8> argv_refs;
          for (const auto &arg : arg_storage)
            argv_refs.push_back(arg);

          std::string err_msg;
          bool exec_failed = false;
          int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                             std::nullopt, {}, 180u, 0,
                                             &err_msg, &exec_failed);
          llvm::sys::fs::remove(temp_in_path);
          if (rc != 0 || exec_failed) {
            llvm::sys::fs::remove(temp_out_path);
            return std::nullopt;
          }

          auto buf_or_err = llvm::MemoryBuffer::getFile(temp_out_path);
          llvm::sys::fs::remove(temp_out_path);
          if (!buf_or_err)
            return std::nullopt;
          return (*buf_or_err)->getBuffer().str();
        };

        if (auto external_ir = runExternalRecoverABI())
          return external_ir;

        llvm::LLVMContext recovery_ctx;
        llvm::SMDiagnostic parse_error;
        auto recovered_module =
            llvm::parseAssemblyString(noabi_ir_text, parse_error, recovery_ctx);
        if (!recovered_module)
          return std::nullopt;

        llvm::PassBuilder PB;
        llvm::LoopAnalysisManager LAM;
        llvm::FunctionAnalysisManager FAM;
        llvm::CGSCCAnalysisManager CGAM;
        llvm::ModuleAnalysisManager RecoveryMAM;
        PB.registerModuleAnalyses(RecoveryMAM);
        PB.registerCGSCCAnalyses(CGAM);
        PB.registerFunctionAnalyses(FAM);
        PB.registerLoopAnalyses(LAM);
        PB.crossRegisterProxies(LAM, FAM, CGAM, RecoveryMAM);
        omill::registerModuleAnalyses(RecoveryMAM);

        omill::PipelineOptions recovery_opts = opts;
        recovery_opts.lower_intrinsics = false;
        recovery_opts.optimize_state = false;
        recovery_opts.lower_control_flow = false;
        recovery_opts.run_cleanup_passes = false;
        recovery_opts.deobfuscate = false;
        recovery_opts.recover_abi = true;
        recovery_opts.resolve_indirect_targets = false;
        recovery_opts.interprocedural_const_prop = false;
        recovery_opts.generic_static_devirtualize = false;
        recovery_opts.verify_generic_static_devirtualization = false;
        recovery_opts.no_abi_mode = false;
        recovery_opts.preserve_lifted_semantics = false;

        llvm::ModulePassManager RecoveryMPM;
        omill::buildPipeline(RecoveryMPM, recovery_opts);
        RecoveryMPM.run(*recovered_module, RecoveryMAM);

        std::string recovered_ir;
        llvm::raw_string_ostream os(recovered_ir);
        recovered_module->print(os, nullptr);
        os.flush();
        return recovered_ir;
      };

  auto rewriteOutputRootToImportedFunction =
      [&](llvm::Function &root, llvm::Function &imported) {
        if (root.getFunctionType() != imported.getFunctionType())
          return false;

        clearTerminalBoundaryAttrs(root);
        for (auto &BB : llvm::make_early_inc_range(root))
          BB.dropAllReferences();
        while (!root.empty())
          root.begin()->eraseFromParent();

        auto *entry = llvm::BasicBlock::Create(ctx, "entry", &root);
        llvm::IRBuilder<> B(entry);
        llvm::SmallVector<llvm::Value *, 8> args;
        for (auto &arg : root.args())
          args.push_back(&arg);
        auto *call = B.CreateCall(&imported, args);
        call->setCallingConv(imported.getCallingConv());
        if (root.getReturnType()->isVoidTy()) {
          B.CreateRetVoid();
        } else {
          B.CreateRet(call);
        }
        return true;
      };

  auto recoverOutputRootTerminalBoundaries = [&]() {
    if (RawBinary || NoABI)
      return;
    if (parseBoolEnv("OMILL_SKIP_TERMINAL_BOUNDARY_SECONDARY_ROOT_RECOVERY")
            .value_or(false)) {
      return;
    }
    llvm::DenseMap<uint64_t, TerminalBoundaryRecoveryAttempt> attempt_cache;
    llvm::DenseMap<uint64_t, llvm::Function *> imported_target_cache;
    const unsigned max_follow_depth =
        parseUnsignedEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_FOLLOW_DEPTH")
            .value_or(1u);

    auto attemptImportRecoveredTarget =
        [&](uint64_t target_pc, llvm::StringRef closed_noabi_ir_text,
            bool enable_gsd_for_child,
            std::string *rejection_reason = nullptr) -> llvm::Function * {
          if (auto it = imported_target_cache.find(target_pc);
              it != imported_target_cache.end()) {
            return it->second;
          }

          auto tryImportABIText =
              [&](llvm::StringRef abi_ir_text,
                  llvm::StringRef source_label) -> llvm::Function * {
            auto abi_summary =
                parseTerminalBoundaryRecoveryIRSummary(abi_ir_text);
            auto abi_status = omill::classifyTerminalBoundaryRecoveryMetrics(
                abi_summary.metrics);
            if (debug_secondary_recovery) {
              errs() << "[terminal-recovery] abi-summary target=0x"
                     << llvm::utohexstr(target_pc)
                     << " source=" << source_label
                     << " status="
                     << omill::terminalBoundaryRecoveryStatusName(abi_status)
                     << " summary="
                     << omill::summarizeTerminalBoundaryRecoveryMetrics(
                            abi_summary.metrics)
                     << "\n";
            }
            if (abi_status !=
                omill::TerminalBoundaryRecoveryStatus::kClosedCandidate) {
              return nullptr;
            }
            std::string local_rejection_reason;
            auto imported = importRecoveredTerminalBoundaryFunction(
                abi_ir_text, target_pc, &local_rejection_reason);
            if (!imported && rejection_reason &&
                !local_rejection_reason.empty()) {
              *rejection_reason = local_rejection_reason;
            }
            if (imported)
              imported_target_cache[target_pc] = imported;
            return imported;
          };

          if (!closed_noabi_ir_text.empty()) {
            ScopedEnvOverride allow_always_inline("OMILL_SKIP_ALWAYS_INLINE",
                                                  "");
            if (auto abi_ir_text =
                    recoverABIForTerminalBoundaryIR(closed_noabi_ir_text)) {
              if (auto *imported =
                      tryImportABIText(*abi_ir_text, "replayed-noabi")) {
                return imported;
              }
            }
          }

          ScopedEnvOverride allow_always_inline("OMILL_SKIP_ALWAYS_INLINE",
                                                "");
          auto abi_child = runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/false, enable_gsd_for_child,
              enable_gsd_for_child, /*dump_virtual_model=*/false);
          if (!abi_child)
            return nullptr;

          return tryImportABIText(abi_child->ir_text, "direct-abi-child");
        };

    llvm::DenseSet<uint64_t> attempt_stack;
    std::function<TerminalBoundaryRecoveryAttempt(uint64_t, unsigned)>
        collectAttemptForTarget =
        [&](uint64_t target_pc, unsigned follow_depth)
        -> TerminalBoundaryRecoveryAttempt {
          if (auto it = attempt_cache.find(target_pc); it != attempt_cache.end())
            return it->second;
          if (!attempt_stack.insert(target_pc).second) {
            TerminalBoundaryRecoveryAttempt cycle_attempt;
            cycle_attempt.target_pc = target_pc;
            cycle_attempt.summary = "recovery_cycle";
            return cycle_attempt;
          }

          TerminalBoundaryRecoveryAttempt attempt;
          attempt.target_pc = target_pc;
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] attempt target=0x"
                   << llvm::utohexstr(target_pc)
                   << " depth=" << follow_depth << "\n";
          }

          auto first_child = runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
              /*enable_recovery_mode=*/false, /*dump_virtual_model=*/false);
          if (!first_child) {
            attempt.summary = "timeout_or_failed_initial_probe";
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          auto first_summary =
              parseTerminalBoundaryRecoveryIRSummary(first_child->ir_text);
          attempt.metrics = first_summary.metrics;
          attempt.status =
              omill::classifyTerminalBoundaryRecoveryMetrics(attempt.metrics);
          attempt.summary =
              omill::summarizeTerminalBoundaryRecoveryMetrics(attempt.metrics);

          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kClosedCandidate) {
            std::string import_rejection_reason;
            if (auto *imported =
                    attemptImportRecoveredTarget(target_pc, first_child->ir_text,
                                                /*enable_gsd_for_child=*/false,
                                                &import_rejection_reason)) {
              attempt.status = omill::TerminalBoundaryRecoveryStatus::kImported;
              attempt.imported = true;
              attempt.summary +=
                  (";imported=" + imported->getName().str());
            } else if (!import_rejection_reason.empty()) {
              attempt.import_rejection_reason = import_rejection_reason;
              attempt.summary +=
                  (";import_rejected=" + import_rejection_reason);
            }
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          if (attempt.status !=
              omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen) {
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          auto recovery_child = runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/true, /*enable_gsd=*/true,
              /*enable_recovery_mode=*/true, /*dump_virtual_model=*/true);
          if (!recovery_child) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kTimeout;
            attempt.summary += ";recovery=timeout_or_failed";
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          auto recovery_model = parseTerminalBoundaryRecoveryModelSummary(
              recovery_child->model_text, target_pc);
          if (recovery_model.found_root) {
            attempt.summary += (";recovery_reachable=" +
                                llvm::Twine(recovery_model.reachable) +
                                ";recovery_frontier=" +
                                llvm::Twine(recovery_model.frontier) +
                                ";recovery_closed=" +
                                llvm::Twine(recovery_model.closed ? 1 : 0))
                                   .str();
          }

          if (recovery_model.found_root && recovery_model.closed &&
              recovery_model.reachable <= 128) {
            std::string import_rejection_reason;
            if (auto *imported =
                    attemptImportRecoveredTarget(target_pc,
                                                recovery_child->ir_text,
                                                /*enable_gsd_for_child=*/true,
                                                &import_rejection_reason)) {
              attempt.status = omill::TerminalBoundaryRecoveryStatus::kImported;
              attempt.imported = true;
              attempt.summary +=
                  (";imported=" + imported->getName().str());
            } else if (!import_rejection_reason.empty()) {
              attempt.import_rejection_reason = import_rejection_reason;
              attempt.summary +=
                  (";import_rejected=" + import_rejection_reason);
            }
          } else if (recovery_model.found_root) {
            auto follow_target = selectFollowupRecoveryTarget(recovery_model);
            if (follow_target && *follow_target != target_pc) {
              if (debug_secondary_recovery) {
                errs() << "[terminal-recovery] follow target=0x"
                       << llvm::utohexstr(target_pc)
                       << " -> 0x" << llvm::utohexstr(*follow_target)
                       << " depth=" << follow_depth << "\n";
              }
              attempt.summary +=
                  (";recovery_follow_target=0x" + llvm::utohexstr(*follow_target));
              if (follow_depth < max_follow_depth) {
                auto followed_attempt =
                    collectAttemptForTarget(*follow_target, follow_depth + 1u);
                attempt.summary +=
                    (";recovery_follow_status=" +
                     std::string(omill::terminalBoundaryRecoveryStatusName(
                         followed_attempt.status)));
                if (!followed_attempt.summary.empty()) {
                  attempt.summary +=
                      (";recovery_follow_summary={" + followed_attempt.summary +
                       "}");
                }
                if (followed_attempt.imported) {
                  if (auto imported_it =
                          imported_target_cache.find(*follow_target);
                      imported_it != imported_target_cache.end() &&
                      imported_it->second) {
                    imported_target_cache[target_pc] = imported_it->second;
                    attempt.status =
                        omill::TerminalBoundaryRecoveryStatus::kImported;
                    attempt.imported = true;
                  }
                }
              } else {
                attempt.summary += ";recovery_follow_depth_limit";
              }
            }
          }

          attempt_stack.erase(target_pc);
          attempt_cache[target_pc] = attempt;
          return attempt;
        };

    bool imported_any = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice")) {
        continue;
      }

      auto cycle_target_attr = F.getFnAttribute(
          "omill.terminal_boundary_probe_cycle_canonical_target_va");
      auto current_target_attr =
          F.getFnAttribute("omill.terminal_boundary_target_va");
      if (!current_target_attr.isValid())
        continue;

      uint64_t recovery_target_pc = 0;
      auto recovery_target_text = cycle_target_attr.isValid()
                                      ? cycle_target_attr.getValueAsString()
                                      : current_target_attr.getValueAsString();
      if (recovery_target_text.getAsInteger(16, recovery_target_pc) ||
          recovery_target_pc == 0) {
        continue;
      }

      auto attempt = collectAttemptForTarget(recovery_target_pc, 0u);
      if (attempt.imported) {
        auto imported_it = imported_target_cache.find(recovery_target_pc);
        if (imported_it == imported_target_cache.end() || !imported_it->second) {
          attempt.imported = false;
          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kImported) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen;
          }
          attempt.summary += ";rewrite_failed=missing_import";
        } else if (F.getFunctionType() !=
                   imported_it->second->getFunctionType()) {
          attempt.imported = false;
          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kImported) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen;
          }
          attempt.summary += ";rewrite_failed=signature_mismatch";
        } else if (rewriteOutputRootToImportedFunction(F,
                                                       *imported_it->second)) {
          imported_any = true;
        } else {
          attempt.imported = false;
          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kImported) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen;
          }
          attempt.summary += ";rewrite_failed=rewrite_failed";
        }
      }

      setTerminalBoundaryRecoveryAttrs(F, attempt);
    }

    if (imported_any) {
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      ModulePassManager MPM;
      omill::buildLateCleanupPipeline(MPM, opts);
      MPM.run(*module, MAM);
    }

    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
  };
  annotateOutputRootTerminalBoundaryProbeChains();
  maybeRerunLateCleanupForCanonicalTerminalBoundaryCycle();
  annotateOutputRootTerminalBoundaryProbeChains();
  recoverOutputRootTerminalBoundaries();
  annotateOutputRootTerminalBoundaryProbeChains();
  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_BEFORE_FINAL_OUTPUT",
                         "before_final_output.ll");
  runFinalOutputCleanup();
  // Legacy `_native` helper recovery was removed with direct canonical ABI.
  runFinalOutputCleanup();
  annotateOutputRootTerminalBoundaryProbeChains();
  omill::refreshTerminalBoundaryRecoveryMetadata(*module);

  auto logFunctionsWithUnresolvedLocalDispatch =
      [&](llvm::StringRef stage_label) {
        const bool debug_public_root_seeds =
            parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
        if (!debug_public_root_seeds)
          return;
        for (auto &Cand : *module) {
          if (Cand.isDeclaration())
            continue;
          bool printed_header = false;
          for (auto &BB : Cand) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              auto *Callee = CB ? CB->getCalledFunction() : nullptr;
              if (!Callee)
                continue;
              auto Name = Callee->getName();
              if (!omill::isDispatchJumpName(Name))
                continue;
              if (!printed_header) {
                errs() << "[abi-post] " << stage_label
                       << " unresolved-func=" << Cand.getName() << " ret=";
                Cand.getReturnType()->print(errs());
                errs() << "\n";
                printed_header = true;
              }
              errs() << "[abi-post] " << stage_label << "   call=" << Name
                     << " bb=" << BB.getName() << "\n";
            }
          }
        }
      };

  auto rewriteFinalFlattenedHelperDispatch = [&]() {
    const bool debug_public_root_seeds =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    auto findFunctionByPrefix = [&](llvm::StringRef prefix) -> llvm::Function * {
      llvm::Function *match = nullptr;
      for (auto &Cand : *module) {
        if (!Cand.getName().starts_with(prefix))
          continue;
        if (match)
          return nullptr;
        match = &Cand;
      }
      return match;
    };

    llvm::Function *F = nullptr;
    llvm::CallBase *dispatch_call = nullptr;
    unsigned total_functions = 0;
    unsigned native_functions = 0;
    unsigned scanned_native_tuple_funcs = 0;
    for (auto &Cand : *module) {
      ++total_functions;
      if (Cand.isDeclaration() || !Cand.getName().ends_with("_native"))
        continue;
      ++native_functions;
      if (debug_public_root_seeds && native_functions <= 8) {
        errs() << "[abi-post] final-flattened-helper-rewrite native="
               << Cand.getName() << " ret=";
        Cand.getReturnType()->print(errs());
        errs() << "\n";
      }
      auto *RetST = llvm::dyn_cast<llvm::StructType>(Cand.getReturnType());
      if (!RetST || RetST->getNumElements() != 8)
        continue;
      ++scanned_native_tuple_funcs;
      for (auto &BB : Cand) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Callee = CB ? CB->getCalledFunction() : nullptr;
          if (!Callee)
            continue;
          auto Name = Callee->getName();
          if (omill::isDispatchJumpName(Name)) {
            if (debug_public_root_seeds) {
              errs() << "[abi-post] final-flattened-helper-rewrite saw candidate="
                     << Cand.getName() << " via " << Name << "\n";
            }
            F = &Cand;
            dispatch_call = CB;
            break;
          }
        }
        if (dispatch_call)
          break;
      }
      if (dispatch_call)
        break;
    }

    if (!F || !dispatch_call) {
      if (debug_public_root_seeds)
        errs() << "[abi-post] final-flattened-helper-rewrite skip missing-func"
               << " total_functions=" << total_functions
               << " native_functions=" << native_functions
               << " scanned_native_tuple_funcs=" << scanned_native_tuple_funcs
               << "\n";
      return false;
    }
    if (debug_public_root_seeds)
      errs() << "[abi-post] final-flattened-helper-rewrite candidate="
             << F->getName() << "\n";

    auto findStateOffsetPtr = [&](uint64_t offset) -> llvm::Value * {
      for (auto &BB : *F) {
        for (auto &I : BB) {
          auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
          if (!GEP || GEP->getNumOperands() < 2)
            continue;
          auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
          if (!idx || idx->getZExtValue() != offset)
            continue;
          return GEP;
        }
      }
      return nullptr;
    };

    auto *eax_ptr = findStateOffsetPtr(2216);
    auto *arg2232_ptr = findStateOffsetPtr(2232);
    auto *arg2280_ptr = findStateOffsetPtr(2280);
    auto *arg2296_ptr = findStateOffsetPtr(2296);
    auto *arg2328_ptr = findStateOffsetPtr(2328);
    auto *arg2408_ptr = findStateOffsetPtr(2408);
    auto *arg2440_ptr = findStateOffsetPtr(2440);
    auto *arg2456_ptr = findStateOffsetPtr(2456);
    if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
        !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
      if (debug_public_root_seeds) {
        errs() << "[abi-post] final-flattened-helper-rewrite skip ptrs"
               << " eax=" << (eax_ptr != nullptr)
               << " 2232=" << (arg2232_ptr != nullptr)
               << " 2280=" << (arg2280_ptr != nullptr)
               << " 2296=" << (arg2296_ptr != nullptr)
               << " 2328=" << (arg2328_ptr != nullptr)
               << " 2408=" << (arg2408_ptr != nullptr)
               << " 2440=" << (arg2440_ptr != nullptr)
               << " 2456=" << (arg2456_ptr != nullptr) << "\n";
      }
      return false;
    }

    llvm::SmallVector<std::pair<uint64_t, llvm::Function *>, 4> targets;
    auto addTarget = [&](uint64_t pc, llvm::StringRef name) {
      auto *Callee = module->getFunction(name);
      if (!Callee)
        Callee = findFunctionByPrefix(name);
      if (!Callee || Callee->isDeclaration())
        return;
      auto *CaseRetST = llvm::dyn_cast<llvm::StructType>(Callee->getReturnType());
      if (!CaseRetST || CaseRetST->getNumElements() != 8)
        return;
      targets.emplace_back(pc, Callee);
    };
    addTarget(0x1800021e7ull, "blk_1800021e7_native");
    addTarget(0x18000223aull, "blk_18000223a_native");
    addTarget(0x18000227dull, "blk_18000227d_native");
    addTarget(0x180002301ull, "sub_180002301_native");
    if (targets.empty()) {
      if (debug_public_root_seeds)
        errs() << "[abi-post] final-flattened-helper-rewrite skip no-targets\n";
      return false;
    }

    auto *switch_block = dispatch_call->getParent();
    auto *target_pc = dispatch_call->getArgOperand(1);
    auto *cont_block = switch_block->splitBasicBlock(
        dispatch_call->getIterator(), "tb.final.dispatch.cont");
    switch_block->getTerminator()->eraseFromParent();
    dispatch_call->eraseFromParent();

    llvm::IRBuilder<> Builder(switch_block);
    auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                         "tb.final.state2232");
    auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                         "tb.final.state2280");
    auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                         "tb.final.state2328");
    auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                         "tb.final.state2440");

    auto *default_loop = llvm::BasicBlock::Create(
        ctx, "tb.final.dispatch.loop.default", F, cont_block);
    llvm::IRBuilder<> DefaultLoopBuilder(default_loop);
    DefaultLoopBuilder.CreateBr(default_loop);

    auto *switch_inst =
        Builder.CreateSwitch(target_pc, default_loop, targets.size() + 1);

    auto *self_loop = llvm::BasicBlock::Create(
        ctx, "tb.final.dispatch.loop.18000216d", F, cont_block);
    llvm::IRBuilder<> SelfLoopBuilder(self_loop);
    SelfLoopBuilder.CreateBr(self_loop);
    switch_inst->addCase(Builder.getInt64(0x18000216dull), self_loop);

    for (auto &[pc, Callee] : targets) {
      auto *case_block = llvm::BasicBlock::Create(
          ctx, "tb.final.case." + llvm::utohexstr(pc), F, cont_block);
      llvm::IRBuilder<> CaseBuilder(case_block);
      auto *case_call = CaseBuilder.CreateCall(
          Callee->getFunctionType(), Callee,
          {state2232, state2280, state2328, state2440});
      case_call->setCallingConv(Callee->getCallingConv());
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {0}),
                              eax_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {1}),
                              arg2232_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {2}),
                              arg2328_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {3}),
                              arg2296_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {4}),
                              arg2280_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {5}),
                              arg2408_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {6}),
                              arg2440_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {7}),
                              arg2456_ptr);
      CaseBuilder.CreateBr(cont_block);
      switch_inst->addCase(Builder.getInt64(pc), case_block);
    }

    if (debug_public_root_seeds)
      errs() << "[abi-post] final-flattened-helper-rewrite applied\n";
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    repairMalformedPHIs(*module);
    return true;
  };
  if (enable_debug_sample_native_fixups) {
    dumpModuleIfEnvEnabled(
        *module,
        "OMILL_DEBUG_DUMP_BEFORE_FINAL_FLATTENED_HELPER_REWRITE",
        "before_final_flattened_helper_rewrite.ll");
    logFunctionsWithUnresolvedLocalDispatch("before-final-flattened-rewrite");
    rewriteFinalFlattenedHelperDispatch();
  }
  auto repairFinalFlattenedSub2301StateCall = [&]() {
    auto *caller = module->getFunction("sub_180002301_native");
    auto *callee = module->getFunction("blk_180002164_native");
    if (!caller || !callee || caller->isDeclaration() || callee->isDeclaration())
      return;

    llvm::AllocaInst *state_alloca = nullptr;
    for (auto &BB : *caller) {
      for (auto &I : BB) {
        auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
        if (!AI)
          continue;
        if (AI->getName().starts_with("blk_180002164_native.synthetic_state")) {
          state_alloca = AI;
          break;
        }
      }
      if (state_alloca)
        break;
    }
    if (!state_alloca) {
      auto *entry_ip = &*caller->getEntryBlock().getFirstInsertionPt();
      llvm::IRBuilder<> EntryBuilder(entry_ip);
      auto *stack_ty =
          llvm::ArrayType::get(llvm::Type::getInt8Ty(ctx), 69632);
      state_alloca = EntryBuilder.CreateAlloca(
          stack_ty, nullptr, "blk_180002164_native.synthetic_state.final");
    }

    unsigned repaired = 0;
    for (auto &BB : *caller) {
      for (auto &I : llvm::make_early_inc_range(BB)) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI || CI->getCalledFunction() != callee || CI->arg_size() != 8)
          continue;
        auto *arg5 = CI->getArgOperand(5)->stripPointerCasts();
        if (llvm::isa<llvm::PtrToIntInst>(arg5) || arg5->getType()->isPointerTy())
          continue;
        llvm::IRBuilder<> Builder(CI);
        auto *state_i64 = Builder.CreatePtrToInt(
            state_alloca, CI->getArgOperand(5)->getType(),
            "blk_180002164_native.synthetic_state.i64.final");
        CI->setArgOperand(5, state_i64);
        ++repaired;
      }
    }
    if (repaired > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] repaired-final-sub2301-state-calls=" << repaired
             << "\n";
    }
  };
  if (enable_debug_sample_native_fixups)
    repairFinalFlattenedSub2301StateCall();
  auto repairFinalBrokenFiveArgStateCalls = [&]() {
    auto calleeReadsArg2AsStatePtr = [&](llvm::Function &Callee) -> bool {
      if (Callee.arg_size() < 3)
        return false;
      auto *arg = Callee.getArg(2);
      for (auto *U : arg->users()) {
        auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
        if (!BO || BO->getOpcode() != llvm::Instruction::Add)
          continue;
        auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
        auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
        if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
            (rhs_ci && rhs_ci->getZExtValue() == 9116))
          return true;
      }
      return false;
    };

    unsigned repaired = 0;
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto findCallerStateBase = [&](llvm::Function &F) -> llvm::Value * {
      if (F.arg_size() >= 3 && calleeReadsArg2AsStatePtr(F))
        return F.getArg(2);
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I);
          if (!BO || BO->getOpcode() != llvm::Instruction::Add)
            continue;
          auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
          auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
          if (lhs_ci && lhs_ci->getZExtValue() == 9116)
            return BO->getOperand(1);
          if (rhs_ci && rhs_ci->getZExtValue() == 9116)
            return BO->getOperand(0);
        }
      }
      return nullptr;
    };
    auto isPointerLikeStateValue = [&](llvm::Value *V) {
      V = V->stripPointerCasts();
      return llvm::isa<llvm::PtrToIntInst>(V) || V->getType()->isPointerTy();
    };
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      auto *caller_state_base = findCallerStateBase(F);
      if (!caller_state_base)
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->arg_size() != 5)
            continue;
          auto *callee = llvm::dyn_cast<llvm::Function>(
              CI->getCalledOperand()->stripPointerCasts());
          if (!callee || callee->isDeclaration() ||
              !callee->getName().ends_with("_native") ||
              !calleeReadsArg2AsStatePtr(*callee)) {
            continue;
          }
          auto *arg2 = CI->getArgOperand(2);
          auto *arg3 = CI->getArgOperand(3);
          auto *arg4 = CI->getArgOperand(4);
          if (arg2 == caller_state_base || isPointerLikeStateValue(arg2))
            continue;

          llvm::SmallVector<llvm::Value *, 5> shifted_args;
          if (auto *arg2_ci = llvm::dyn_cast<llvm::ConstantInt>(arg2);
              arg2_ci && arg2_ci->isZero()) {
            if (isPointerLikeStateValue(arg3)) {
              shifted_args = {CI->getArgOperand(0), CI->getArgOperand(1), arg3,
                              arg4, llvm::ConstantInt::get(i64_ty, 0)};
            } else {
              shifted_args = {CI->getArgOperand(0), CI->getArgOperand(1),
                              caller_state_base, arg3, arg4};
            }
          } else {
            shifted_args = {CI->getArgOperand(0), CI->getArgOperand(1),
                            caller_state_base, arg2, arg3};
          }

          auto *new_call = llvm::CallInst::Create(
              callee->getFunctionType(), callee, shifted_args, CI->getName(),
              CI->getIterator());
          new_call->setCallingConv(CI->getCallingConv());
          new_call->setAttributes(CI->getAttributes());
          if (!CI->use_empty()) {
            if (CI->getType() == new_call->getType()) {
              CI->replaceAllUsesWith(new_call);
            } else if (llvm::isa<llvm::StructType>(new_call->getType())) {
              auto *ev = llvm::ExtractValueInst::Create(
                  new_call, {0}, "ret.primary",
                  std::next(new_call->getIterator()));
              CI->replaceAllUsesWith(ev);
            } else {
              CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
            }
          }
          CI->eraseFromParent();
          ++repaired;
        }
      }
    }

    if (repaired > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] repaired-final-broken-five-arg-state-calls="
             << repaired << "\n";
    }
  };
  if (enable_debug_sample_native_fixups) {
    repairFinalBrokenFiveArgStateCalls();
    dumpModuleIfEnvEnabled(
        *module,
        "OMILL_DEBUG_DUMP_AFTER_FINAL_FLATTENED_HELPER_REWRITE",
        "after_final_flattened_helper_rewrite.ll");
    logFunctionsWithUnresolvedLocalDispatch("after-final-flattened-rewrite");
  }

  auto repairLateDeclaredContinuationWrappers = [&]() {
    unsigned rewritten = 0;
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto isTypeCompatibleReplacement = [](llvm::CallInst &CI,
                                          llvm::Function &target) {
      auto *target_fty = target.getFunctionType();
      if (target_fty->isVarArg() || CI.arg_size() != target_fty->getNumParams())
        return false;
      if (CI.getType() != target_fty->getReturnType())
        return false;
      for (unsigned i = 0; i < CI.arg_size(); ++i) {
        if (CI.getArgOperand(i)->getType() != target_fty->getParamType(i))
          return false;
      }
      return true;
    };
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->arg_size() < 3)
            continue;
          auto *callee = CI->getCalledFunction();
          if (!callee || !callee->isDeclaration())
            continue;
          auto name = callee->getName();
          if (!(name.starts_with("blk_") || name.starts_with("block_")) ||
              name.ends_with("_native")) {
            continue;
          }
          auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
          if (!pc_ci)
            continue;

          uint64_t resolved_pc = 0;
          auto *target = findExactOrNearbyLiftedOrBlockFunction(
              pc_ci->getZExtValue(), /*native=*/false, &resolved_pc);
          if (!target || target == callee || target->isDeclaration())
            continue;
          if (!isTypeCompatibleReplacement(*CI, *target))
            continue;

          if (auto *helper = llvm::dyn_cast<llvm::CallInst>(CI->getArgOperand(2))) {
            if (auto *helper_callee = helper->getCalledFunction();
                helper_callee &&
                omill::isDispatchIntrinsicName(helper_callee->getName()) &&
                helper->arg_size() >= 3) {
              CI->setArgOperand(2, helper->getArgOperand(2));
              if (helper->use_empty())
                helper->eraseFromParent();
            }
          }

          CI->setCalledFunction(target);
          CI->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
          ++rewritten;
        }
      }
    }

    if (rewritten > 0) {
      errs() << "[abi-post] repaired-late-declared-continuation-wrappers="
             << rewritten << "\n";
    }
  };
  if (!opts.no_abi_mode)
    repairLateDeclaredContinuationWrappers();
  dumpModuleIfEnvEnabled(
      *module, "OMILL_DEBUG_DUMP_AFTER_LATE_DECL_CONT_REWRITE",
      "after_late_decl_cont_rewrite.ll");

  if (parseBoolEnv("OMILL_DEBUG_OUTPUT_ROOTS").value_or(false)) {
    errs() << "[output-roots] final-defined=" << countDefinedOutputRoots()
           << "\n";
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root"))
        continue;
      errs() << "[output-roots] name=" << F.getName()
             << " decl=" << (F.isDeclaration() ? 1 : 0);
      if (auto target_attr = F.getFnAttribute("omill.terminal_boundary_target_va");
          target_attr.isValid()) {
        errs() << " target=0x" << target_attr.getValueAsString();
      }
      if (auto recovery_attr =
              F.getFnAttribute("omill.terminal_boundary_recovery_status");
          recovery_attr.isValid()) {
        errs() << " recovery=" << recovery_attr.getValueAsString();
      }
      errs() << "\n";
    }
  }

  auto collectUnresolvedOutputRootPcCalls = [&]() {
    llvm::SmallVector<std::string, 8> unresolved;
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;
      if (!hasUnresolvedLiftedControlTransferInClosure(F))
        continue;
      std::string label = F.getName().str();
      if (auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
          attr.isValid() && attr.isStringAttribute() &&
          !attr.getValueAsString().empty()) {
        label += "[vm=0x" + attr.getValueAsString().str() + "]";
      }
      unresolved.push_back(std::move(label));
    }
    return unresolved;
  };

  auto collectOutputRootFunctionReturnLeaks = [&]() {
    llvm::SmallVector<std::string, 8> leaked;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      llvm::SmallVector<llvm::Function *, 16> worklist = {&F};
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      while (!worklist.empty()) {
        auto *current = worklist.pop_back_val();
        if (!current || current->isDeclaration() ||
            !visited.insert(current).second) {
          continue;
        }
        bool has_return_intrinsic = false;
        for (auto &BB : *current) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            if (auto *callee = CB->getCalledFunction()) {
              if (!callee->isDeclaration())
                worklist.push_back(callee);
              if (callee->getName() == "__remill_function_return")
                has_return_intrinsic = true;
            }
          }
        }
        if (has_return_intrinsic)
          leaked.push_back(current->getName().str());
      }
    }
    llvm::sort(leaked);
    leaked.erase(std::unique(leaked.begin(), leaked.end()), leaked.end());
    return leaked;
  };

  auto annotateVmUnresolvedContinuationsInCurrentModule = [&]() {
    constexpr llvm::StringLiteral kCountAttr =
        "omill.vm_unresolved_continuation_count";
    constexpr llvm::StringLiteral kTargetsAttr =
        "omill.vm_unresolved_continuation_targets";
    constexpr llvm::StringLiteral kSummaryAttr =
        "omill.vm_unresolved_continuation_summary";
    constexpr llvm::StringLiteral kNamedMetadata =
        "omill.vm_unresolved_continuations";

    for (auto &F : *module) {
      F.removeFnAttr(kCountAttr);
      F.removeFnAttr(kTargetsAttr);
      F.removeFnAttr(kSummaryAttr);
    }
    if (auto *named_md = module->getNamedMetadata(kNamedMetadata))
      named_md->clearOperands();
    auto *named_md = module->getOrInsertNamedMetadata(kNamedMetadata);

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      llvm::SmallVector<llvm::Function *, 16> worklist = {&F};
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      llvm::SmallVector<std::pair<uint64_t, std::string>, 8> infos;

      while (!worklist.empty()) {
        auto *current = worklist.pop_back_val();
        if (!current || current->isDeclaration() ||
            !visited.insert(current).second) {
          continue;
        }

        for (auto &BB : *current) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee = call->getCalledFunction();
            if (!callee)
              continue;
            auto callee_name = callee->getName();
            if (omill::isDispatchIntrinsicName(callee_name)) {
              if (auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(
                      call->getArgOperand(1))) {
                std::string reason =
                    omill::isDispatchJumpName(callee_name) ? "dispatch_jump"
                                                           : "dispatch_call";
                if (auto *prev = llvm::dyn_cast_or_null<llvm::CallInst>(
                        call->getPrevNonDebugInstruction())) {
                  if (auto *prev_callee = prev->getCalledFunction()) {
                    if (prev_callee->getName().contains("CALLI"))
                      reason += ":paired_CALLI";
                    else if (prev_callee->getName().contains("JMPI"))
                      reason += ":paired_JMPI";
                  }
                }
                infos.push_back({pc_ci->getZExtValue(), std::move(reason)});
              }
            }

            for (llvm::Value *operand : I.operands()) {
              auto *maybe_callee = llvm::dyn_cast<llvm::Function>(operand);
              if (!maybe_callee || maybe_callee->isDeclaration())
                continue;
              worklist.push_back(maybe_callee);
            }
          }
        }
      }

      if (infos.empty())
        continue;

      llvm::SmallVector<std::string, 8> target_parts;
      llvm::SmallVector<std::string, 8> summary_parts;
      llvm::SmallDenseSet<uint64_t, 8> seen_targets;
      for (const auto &[pc, reason] : infos) {
        if (seen_targets.insert(pc).second)
          target_parts.push_back(llvm::utohexstr(pc));
        summary_parts.push_back(reason + "@0x" + llvm::utohexstr(pc));
      }

      F.addFnAttr(kCountAttr, std::to_string(infos.size()));
      F.addFnAttr(kTargetsAttr, llvm::join(target_parts, ","));
      F.addFnAttr(kSummaryAttr, llvm::join(summary_parts, ","));

      llvm::Metadata *ops[] = {
          llvm::ValueAsMetadata::get(&F),
          llvm::MDString::get(ctx, std::to_string(infos.size())),
          llvm::MDString::get(ctx, llvm::join(target_parts, ",")),
          llvm::MDString::get(ctx, llvm::join(summary_parts, ","))};
      named_md->addOperand(llvm::MDNode::get(ctx, ops));
    }
  };
  if (noabi_output_root_targets_patched)
    annotateVmUnresolvedContinuationsInCurrentModule();

  auto collectSuspiciousZeroArityOutputRoots = [&]() {
    llvm::SmallVector<std::string, 8> suspicious;
    const auto &DL = module->getDataLayout();
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;
      if (F.arg_size() != 0)
        continue;

      bool has_state_alloca = false;
      bool has_large_stack_alloca = false;
      bool uses_stacksave = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
            if (auto *ST =
                    llvm::dyn_cast<llvm::StructType>(AI->getAllocatedType());
                ST && ST->hasName() && ST->getName() == "struct.State") {
              has_state_alloca = true;
            }
            if (auto *AT =
                    llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType())) {
              auto bytes = DL.getTypeAllocSize(AT);
              if (bytes >= 4096)
                has_large_stack_alloca = true;
            }
          }
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (callee && callee->getName() == "llvm.stacksave.p0")
            uses_stacksave = true;
        }
      }

      if (has_state_alloca || has_large_stack_alloca || uses_stacksave)
        suspicious.push_back(F.getName().str());
    }
    return suspicious;
  };

  auto collectSuspiciousStackBackedOutputRoots = [&]() {
    llvm::SmallVector<std::string, 8> suspicious;
    const auto &DL = module->getDataLayout();
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;

      bool has_state_alloca = false;
      bool has_large_stack_alloca = false;
      bool uses_stacksave = false;
      bool calls_local_lifted_helper = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
            if (auto *ST =
                    llvm::dyn_cast<llvm::StructType>(AI->getAllocatedType());
                ST && ST->hasName() && ST->getName() == "struct.State") {
              has_state_alloca = true;
            }
            if (auto *AT =
                    llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType())) {
              auto bytes = DL.getTypeAllocSize(AT);
              if (bytes >= 4096)
                has_large_stack_alloca = true;
            }
          }
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (callee && callee->getName() == "llvm.stacksave.p0")
            uses_stacksave = true;
          if (callee && !callee->isDeclaration() &&
              !callee->getName().ends_with("_native") &&
              (callee->getName().starts_with("blk_") ||
               callee->getName().starts_with("sub_") ||
               callee->getName().starts_with("block_"))) {
            calls_local_lifted_helper = true;
          }
        }
      }

      if ((has_state_alloca || has_large_stack_alloca || uses_stacksave) &&
          calls_local_lifted_helper) {
        suspicious.push_back(F.getName().str());
      }
    }
    return suspicious;
  };

  auto collectLargeStackOutputRoots = [&]() {
    llvm::SmallVector<std::string, 8> suspicious;
    const auto &DL = module->getDataLayout();
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;

      bool has_large_stack_alloca = false;
      bool uses_stacksave = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
            if (auto *AT =
                    llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType())) {
              auto bytes = DL.getTypeAllocSize(AT);
              if (bytes >= 4096)
                has_large_stack_alloca = true;
            }
          }
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (callee && callee->getName() == "llvm.stacksave.p0")
            uses_stacksave = true;
        }
      }

      if (has_large_stack_alloca || uses_stacksave)
        suspicious.push_back(F.getName().str());
    }
    return suspicious;
  };

  auto tryFastPlainNoBlockExportFallback =
      [&](llvm::StringRef reason) -> std::optional<int> {
        if (RawBinary || NoABI || !fast_plain_export_root_fallback ||
            !opts.use_block_lifting ||
            func_va == 0 || countDefinedOutputRoots() > 1u) {
          return std::nullopt;
        }

        errs() << "Attempting plain no-block export fallback\n";
        events.emitInfo("plain_no_block_export_fallback_started",
                        "plain no-block export fallback started",
                        {{"reason", reason}});

        llvm::SmallString<256> temp_ll_path;
        if (llvm::sys::fs::createTemporaryFile("omill_plain_export_noblock",
                                               "ll", temp_ll_path)) {
          return std::nullopt;
        }

        llvm::SmallVector<std::string, 16> arg_storage;
        arg_storage.emplace_back(argv[0]);
        arg_storage.emplace_back(InputFilename);
        arg_storage.emplace_back("--va");
        arg_storage.emplace_back(llvm::utohexstr(func_va));
        arg_storage.emplace_back("-o");
        arg_storage.emplace_back(temp_ll_path.str().str());

        llvm::SmallVector<llvm::StringRef, 16> argv_refs;
        for (const auto &arg : arg_storage)
          argv_refs.push_back(arg);

        std::string err_msg;
        bool exec_failed = false;
        {
          ScopedEnvOverride skip_nested_probe(
              "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
          ScopedEnvOverride skip_late_output_target(
              "OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN", "1");
          ScopedEnvOverride skip_late_boundary_rerun(
              "OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN", "1");
          int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                             std::nullopt, {}, 180u, 0,
                                             &err_msg, &exec_failed);
          if (rc != 0 || exec_failed) {
            llvm::sys::fs::remove(temp_ll_path);
            return std::nullopt;
          }
        }

        auto buf_or_err = llvm::MemoryBuffer::getFile(temp_ll_path);
        llvm::sys::fs::remove(temp_ll_path);
        if (!buf_or_err)
          return std::nullopt;
        auto child_text = (*buf_or_err)->getBuffer().str();
        llvm::LLVMContext verify_ctx;
        llvm::SMDiagnostic parse_error;
        auto verify_module =
            llvm::parseAssemblyString(child_text, parse_error, verify_ctx);
        auto childModuleReadableEnoughForDirectWrite =
            [&](const llvm::Module &M) {
              bool has_state_alloca = false;
              bool has_large_stack_alloca = false;
              bool uses_stacksave = false;
              bool calls_local_lifted_helper = false;
              bool has_unresolved_lifted_control_transfer = false;
              unsigned defined_lifted_function_count = 0;
              const auto &DL = M.getDataLayout();
              for (auto &F : M) {
                if (F.isDeclaration())
                  continue;
                if (F.hasFnAttribute("omill.output_root") &&
                    hasUnresolvedLiftedControlTransferInClosure(F)) {
                  has_unresolved_lifted_control_transfer = true;
                }
                if ((F.getName().starts_with("sub_") ||
                     F.getName().starts_with("blk_") ||
                     F.getName().starts_with("block_")) &&
                    !F.getName().ends_with("_native")) {
                  ++defined_lifted_function_count;
                }
                for (auto &BB : F) {
                  for (auto &I : BB) {
                    if (auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
                      if (auto *allocated_struct =
                              llvm::dyn_cast<llvm::StructType>(
                                  alloca->getAllocatedType());
                          allocated_struct && allocated_struct->hasName() &&
                          allocated_struct->getName() == "struct.State") {
                        has_state_alloca = true;
                      }
                      if (auto *AT = llvm::dyn_cast<llvm::ArrayType>(
                              alloca->getAllocatedType())) {
                        if (DL.getTypeAllocSize(AT) >= 4096)
                          has_large_stack_alloca = true;
                      }
                    }
                    auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
                    auto *callee = call ? call->getCalledFunction() : nullptr;
                    if (callee && callee->getName() == "llvm.stacksave.p0")
                      uses_stacksave = true;
                    if (callee && !callee->isDeclaration() &&
                        !callee->getName().ends_with("_native") &&
                        (callee->getName().starts_with("sub_") ||
                         callee->getName().starts_with("blk_") ||
                         callee->getName().starts_with("block_"))) {
                      calls_local_lifted_helper = true;
                    }
                  }
                }
              }
              return !has_state_alloca && !has_large_stack_alloca &&
                     !uses_stacksave && !calls_local_lifted_helper &&
                     !has_unresolved_lifted_control_transfer &&
                     defined_lifted_function_count == 0;
            };
        if (!verify_module || verifyModule(*verify_module, nullptr) ||
            !childModuleReadableEnoughForDirectWrite(*verify_module)) {
          return std::nullopt;
        }

        std::error_code direct_ec;
        events.emitInfo("output_write_started", "writing final output",
                        {{"path", OutputFilename}});
        ToolOutputFile direct_out(OutputFilename, direct_ec,
                                  sys::fs::OF_Text);
        if (direct_ec) {
          errs() << "Error opening output: " << direct_ec.message() << "\n";
          return fail(1, "failed to open output file");
        }
        direct_out.os() << child_text;
        direct_out.keep();
        events.emitInfo("plain_no_block_export_fallback_applied",
                        "plain no-block export fallback applied");
        events.emitInfo("output_write_completed", "output write complete",
                        {{"path", OutputFilename}});
        events.emitTerminalSuccess(OutputFilename);
        return 0;

        return std::nullopt;
      };

  auto tryReplayABIFromPreABICheckpoint = [&]() -> bool {
    if (RawBinary || NoABI || !use_pre_abi_noabi_cleanup)
      return false;
    if (!pre_abi_checkpoint_text || pre_abi_checkpoint_text->empty())
      return false;
    if (parseBoolEnv("OMILL_SKIP_PRE_ABI_REPLAY_FALLBACK").value_or(false))
      return false;
    if (countDefinedOutputRoots() > 1u)
      return false;

    auto replayed_ir = recoverABIForTerminalBoundaryIR(*pre_abi_checkpoint_text);
    if (!replayed_ir)
      return false;

    llvm::SMDiagnostic parse_error;
    auto replayed_module =
        llvm::parseAssemblyString(*replayed_ir, parse_error, ctx);
    if (!replayed_module)
      return false;
    if (verifyModule(*replayed_module, nullptr))
      return false;

    unsigned defined_output_roots = 0;
    bool has_unresolved_output_pc = false;
    for (auto &F : *replayed_module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;
      ++defined_output_roots;
      if (hasUnresolvedOutputRootPcCall(F))
        has_unresolved_output_pc = true;
    }
    if (defined_output_roots == 0 || has_unresolved_output_pc)
      return false;

    module = std::move(replayed_module);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    annotateOutputRootTerminalBoundaryProbeChains();
    runFinalOutputCleanup();
    annotateOutputRootTerminalBoundaryProbeChains();
    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
    repairMalformedPHIs(*module);

    events.emitInfo("pre_abi_replay_fallback_applied",
                    "replayed ABI from pre-ABI closed checkpoint",
                    {{"defined_output_roots",
                      static_cast<int64_t>(defined_output_roots)}});
    return true;
  };

  auto tryReplayABIFromExternalMainRootNoABIChild = [&]() -> bool {
    if (RawBinary || NoABI || !use_pre_abi_noabi_cleanup || func_va == 0)
      return false;
    if (parseBoolEnv("OMILL_SKIP_MAIN_ROOT_NOABI_CHILD_REPLAY")
            .value_or(false)) {
      return false;
    }

    auto noabi_child = [&]() -> std::optional<TerminalBoundaryChildLiftResult> {
      llvm::SmallString<256> temp_ll_path;
      if (llvm::sys::fs::createTemporaryFile("omill_main_root_noabi", "ll",
                                             temp_ll_path)) {
        return std::nullopt;
      }
      llvm::SmallString<256> temp_model_path;
      if (llvm::sys::fs::createTemporaryFile("omill_main_root_noabi", "model",
                                             temp_model_path)) {
        llvm::sys::fs::remove(temp_ll_path);
        return std::nullopt;
      }

      llvm::SmallVector<std::string, 16> arg_storage;
      arg_storage.emplace_back(argv[0]);
      arg_storage.emplace_back(InputFilename);
      arg_storage.emplace_back("--va");
      arg_storage.emplace_back(llvm::utohexstr(func_va));
      if (opts.use_block_lifting)
        arg_storage.emplace_back("--block-lift");
      if (devirtualization_plan.enable_devirtualization)
        arg_storage.emplace_back("--devirtualize");
      if (opts.generic_static_devirtualize)
        arg_storage.emplace_back("--generic-static-devirtualize");
      arg_storage.emplace_back("--no-abi");
      arg_storage.emplace_back("-o");
      arg_storage.emplace_back(temp_ll_path.str().str());

      llvm::SmallVector<llvm::StringRef, 16> argv_refs;
      for (const auto &arg : arg_storage)
        argv_refs.push_back(arg);

      std::string err_msg;
      bool exec_failed = false;
      std::string recovery_root_va_text = llvm::utohexstr(func_va);
      ScopedEnvOverride skip_nested_probe(
          "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
      ScopedEnvOverride skip_late_output_target(
          "OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN", "1");
      ScopedEnvOverride skip_late_boundary_rerun(
          "OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN", "1");
      ScopedEnvOverride enable_call_frontier_dispatch_override(
          "OMILL_ENABLE_CALL_FRONTIER_DISPATCH_OVERRIDE", "1");
      ScopedEnvOverride enable_terminal_boundary_recovery(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY", "1");
      ScopedEnvOverride terminal_boundary_recovery_root(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA",
          recovery_root_va_text.c_str());
      ScopedEnvOverride terminal_boundary_recovery_max_reachable(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE", "32");
      ScopedEnvOverride terminal_boundary_recovery_max_iterations(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_ITERATIONS", "14");
      ScopedEnvOverride terminal_boundary_recovery_max_new_target_rounds(
          "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_NEW_TARGET_ROUNDS", "14");
      ScopedEnvOverride dump_virtual_model("OMILL_DUMP_VIRTUAL_MODEL",
                                           temp_model_path.str().str().c_str());
      int rc = llvm::sys::ExecuteAndWait(
          argv_refs.front(), argv_refs, std::nullopt, {},
          parseUnsignedEnv("OMILL_MAIN_ROOT_NOABI_CHILD_TIMEOUT_SECONDS")
              .value_or(900u),
          0, &err_msg, &exec_failed);
      if (rc != 0 || exec_failed) {
        llvm::sys::fs::remove(temp_ll_path);
        llvm::sys::fs::remove(temp_model_path);
        return std::nullopt;
      }

      auto buf_or_err = llvm::MemoryBuffer::getFile(temp_ll_path);
      llvm::sys::fs::remove(temp_ll_path);
      if (!buf_or_err) {
        llvm::sys::fs::remove(temp_model_path);
        return std::nullopt;
      }
      TerminalBoundaryChildLiftResult result;
      result.ir_text = (*buf_or_err)->getBuffer().str();
      auto model_or_err = llvm::MemoryBuffer::getFile(temp_model_path);
      llvm::sys::fs::remove(temp_model_path);
      if (model_or_err)
        result.model_text = (*model_or_err)->getBuffer().str();
      return result;
    }();
    if (!noabi_child)
      return false;

    dumpTextIfEnvEnabled(noabi_child->ir_text,
                         "OMILL_DEBUG_DUMP_MAIN_ROOT_NOABI_CHILD_IR",
                         "main_root_noabi_child.ll");

    llvm::StringMap<std::string> original_output_root_attrs;
    auto rememberOriginalOutputRootAttr = [&](llvm::StringRef name) {
      for (auto &F : *module) {
        if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
          continue;
        auto attr = F.getFnAttribute(name);
        if (!attr.isValid() || !attr.isStringAttribute())
          continue;
        auto value = attr.getValueAsString();
        if (value.empty())
          continue;
        original_output_root_attrs[name] = value.str();
        break;
      }
    };
    rememberOriginalOutputRootAttr("omill.export_entry_seed_exprs");
    rememberOriginalOutputRootAttr("omill.export_callsite_win64_gpr_count");
    rememberOriginalOutputRootAttr("omill.extra_gpr_live_ins");
    rememberOriginalOutputRootAttr("omill.public_root_seed_kind");
    rememberOriginalOutputRootAttr("omill.public_root_seed_summary");

    auto prepareMainRootNoABIChildForABIReplay =
        [&](llvm::StringRef child_ir, llvm::StringRef child_model) -> std::string {
      llvm::SMDiagnostic parse_error;
      auto child_module = llvm::parseAssemblyString(child_ir, parse_error, ctx);
      if (!child_module)
        return child_ir.str();

      auto parsePrefixedHex = [](llvm::StringRef name,
                                 llvm::StringRef prefix) -> uint64_t {
        if (!name.starts_with(prefix))
          return 0;
        auto rest = name.drop_front(prefix.size());
        size_t hex_len = 0;
        while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
          ++hex_len;
        if (hex_len == 0)
          return 0;
        uint64_t pc = 0;
        if (rest.substr(0, hex_len).getAsInteger(16, pc))
          return 0;
        return pc;
      };

      auto extractLiftedPC = [&](llvm::Function &F) -> uint64_t {
        auto name = F.getName();
        if (uint64_t pc = parsePrefixedHex(name, "sub_"); pc != 0)
          return pc;
        if (uint64_t pc = parsePrefixedHex(name, "blk_"); pc != 0)
          return pc;
        if (uint64_t pc = parsePrefixedHex(name, "block_"); pc != 0)
          return pc;
        return 0;
      };

      auto findNearestDefinedLiftedOrBlock = [&](uint64_t target_pc)
          -> llvm::Function * {
        if (!target_pc)
          return nullptr;
        llvm::Function *best = nullptr;
        uint64_t best_distance = std::numeric_limits<uint64_t>::max();
        for (auto &F : *child_module) {
          if (F.isDeclaration())
            continue;
          uint64_t pc = extractLiftedPC(F);
          if (!pc)
            continue;
          uint64_t distance =
              pc > target_pc ? (pc - target_pc) : (target_pc - pc);
          if (distance > 0x80)
            continue;
          if (!best || distance < best_distance) {
            best = &F;
            best_distance = distance;
          }
        }
        return best;
      };

      auto importLiftedChildClosure =
          [&](uint64_t target_pc, llvm::StringRef imported_ir,
              llvm::StringRef imported_model,
              llvm::StringRef name_prefix) -> llvm::Function * {
            llvm::SMDiagnostic parse_error;
            auto imported_module =
                llvm::parseAssemblyString(imported_ir, parse_error, ctx);
            if (!imported_module)
              return nullptr;

            auto findLiftedRootByPc = [&](uint64_t pc) -> llvm::Function * {
              const std::string target_hex = llvm::utohexstr(pc);
              const std::string target_hex_lower =
                  llvm::StringRef(target_hex).lower();
              for (const std::string &name :
                   {"sub_" + target_hex, "sub_" + target_hex_lower,
                    "blk_" + target_hex, "blk_" + target_hex_lower,
                    "block_" + target_hex, "block_" + target_hex_lower}) {
                if (auto *fn = imported_module->getFunction(name))
                  return fn;
              }
              for (auto &F : *imported_module) {
                if (F.isDeclaration())
                  continue;
                if (omill::extractEntryVA(F.getName()) == pc)
                  return &F;
              }
              return nullptr;
            };

            auto *root = findLiftedRootByPc(target_pc);
            if (!root || root->isDeclaration())
              return nullptr;

            llvm::StringSet<> allowed_slice_names;
            for (const auto &name :
                 parseClosedRootSliceHandlerNames(imported_model, target_pc)) {
              allowed_slice_names.insert(name);
            }

            llvm::SmallVector<llvm::Function *, 16> closure;
            llvm::SmallVector<llvm::Function *, 16> worklist;
            llvm::SmallPtrSet<llvm::Function *, 16> visited;
            if (!allowed_slice_names.empty()) {
              for (const auto &name : allowed_slice_names) {
                if (auto *fn = imported_module->getFunction(name.getKey());
                    fn && !fn->isDeclaration()) {
                  worklist.push_back(fn);
                }
              }
            }
            if (worklist.empty())
              worklist.push_back(root);

            while (!worklist.empty()) {
              auto *F = worklist.pop_back_val();
              if (!F || F->isDeclaration() || !visited.insert(F).second)
                continue;
              closure.push_back(F);
              for (auto &BB : *F) {
                for (auto &I : BB) {
                  for (llvm::Value *operand : I.operands()) {
                    auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                    if (!GV)
                      continue;
                    if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                      if (callee->isDeclaration())
                        continue;
                      if (!allowed_slice_names.empty() &&
                          !allowed_slice_names.count(callee->getName()))
                        continue;
                      worklist.push_back(callee);
                      continue;
                    }
                    if (auto *global =
                            llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                      if (!global->isDeclaration() &&
                          !global->getName().starts_with("llvm.")) {
                        return nullptr;
                      }
                    }
                  }
                }
              }
            }
            if (closure.empty())
              return nullptr;

            llvm::DenseMap<const llvm::Function *, llvm::Function *> cloned;
            llvm::DenseMap<const llvm::GlobalValue *, llvm::GlobalValue *>
                decl_map;
            llvm::Function *cloned_root = nullptr;

            auto clearImportedAttrs = [&](llvm::Function &F) {
              clearTerminalBoundaryAttrs(F);
              F.removeFnAttr("omill.output_root");
              F.removeFnAttr("omill.closed_root_slice");
              F.removeFnAttr("omill.closed_root_slice_root");
              F.removeFnAttr("omill.param_state_offsets");
              F.removeFnAttr("omill.vm_unresolved_continuation_count");
              F.removeFnAttr("omill.vm_unresolved_continuation_targets");
              F.removeFnAttr("omill.vm_unresolved_continuation_summary");
              F.removeFnAttr("omill.terminal_boundary_recovery_status");
              F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
              F.removeFnAttr("omill.terminal_boundary_recovery_summary");
            };

            auto makeUniqueImportName = [&](llvm::StringRef base_name) {
              std::string candidate = (name_prefix + base_name).str();
              if (!child_module->getFunction(candidate) &&
                  !imported_module->getFunction(candidate)) {
                return candidate;
              }
              for (unsigned i = 1; i < 100; ++i) {
                auto numbered = candidate + "." + std::to_string(i);
                if (!child_module->getFunction(numbered) &&
                    !imported_module->getFunction(numbered)) {
                  return numbered;
                }
              }
              return candidate;
            };

            for (auto *src_fn : closure) {
              auto clone_name = makeUniqueImportName(src_fn->getName());
              auto *dst_fn = llvm::Function::Create(
                  src_fn->getFunctionType(),
                  llvm::GlobalValue::InternalLinkage, clone_name, *child_module);
              dst_fn->copyAttributesFrom(src_fn);
              clearImportedAttrs(*dst_fn);
              cloned[src_fn] = dst_fn;
              if (src_fn == root)
                cloned_root = dst_fn;
            }
            if (!cloned_root)
              return nullptr;

            for (auto *src_fn : closure) {
              for (auto &BB : *src_fn) {
                for (auto &I : BB) {
                  for (llvm::Value *operand : I.operands()) {
                    auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                    if (!GV || decl_map.count(GV))
                      continue;
                    if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                      if (auto it = cloned.find(callee); it != cloned.end()) {
                        decl_map[GV] = it->second;
                        continue;
                      }
                      auto *decl = child_module->getFunction(callee->getName());
                      if (!decl) {
                        decl = llvm::Function::Create(
                            callee->getFunctionType(), callee->getLinkage(),
                            callee->getName(), *child_module);
                        decl->copyAttributesFrom(callee);
                      }
                      decl_map[GV] = decl;
                    }
                  }
                }
              }
            }

            for (auto *src_fn : closure) {
              auto *dst_fn = cloned.lookup(src_fn);
              llvm::ValueToValueMapTy vmap;
              auto src_arg_it = src_fn->arg_begin();
              auto dst_arg_it = dst_fn->arg_begin();
              for (; src_arg_it != src_fn->arg_end() &&
                     dst_arg_it != dst_fn->arg_end();
                   ++src_arg_it, ++dst_arg_it) {
                vmap[&*src_arg_it] = &*dst_arg_it;
              }
              for (const auto &decl_entry : decl_map)
                vmap[const_cast<llvm::GlobalValue *>(decl_entry.first)] =
                    decl_entry.second;
              llvm::SmallVector<llvm::ReturnInst *, 8> returns;
              llvm::CloneFunctionInto(
                  dst_fn, src_fn, vmap,
                  llvm::CloneFunctionChangeType::DifferentModule, returns);
              clearImportedAttrs(*dst_fn);
            }

            return cloned_root;
          };

      llvm::SmallVector<llvm::Function *, 8> output_roots;
      for (auto &F : *child_module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
      }
      if (output_roots.size() != 1)
        return child_ir.str();

      llvm::SmallVector<llvm::Function *, 8> worklist(output_roots.begin(),
                                                      output_roots.end());
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      llvm::SmallPtrSet<llvm::Function *, 8> extra_output_roots;
      unsigned rewritten_dispatch_calls = 0;
      unsigned rewritten_dispatch_calls_after_import = 0;
      unsigned promoted_continuation_roots = 0;
      unsigned promoted_frontier_roots = 0;
      unsigned attempted_frontier_imports = 0;
      const unsigned kMaxFrontierImports =
          parseUnsignedEnv("OMILL_MAIN_ROOT_CHILD_MAX_FRONTIER_IMPORTS")
              .value_or(1u);
      while (!worklist.empty()) {
        auto *F = worklist.pop_back_val();
        if (!visited.insert(F).second)
          continue;

        for (auto &BB : *F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!call)
              continue;
            if (auto *callee = call->getCalledFunction()) {
              if (!callee->isDeclaration())
                worklist.push_back(callee);
              if (!omill::isDispatchCallName(callee->getName()) ||
                  call->arg_size() < 2) {
                continue;
              }
            } else {
              continue;
            }

            auto *pc_ci =
                llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
            if (!pc_ci)
              continue;
            uint64_t target_pc = pc_ci->getZExtValue();
            if (!target_pc)
              continue;

            auto *target_fn = findNearestDefinedLiftedOrBlock(target_pc);
            if (!target_fn || target_fn == F)
              continue;
            if (target_fn->getFunctionType() == call->getFunctionType()) {
              call->setCalledFunction(target_fn);
              ++rewritten_dispatch_calls;
            }
            extra_output_roots.insert(target_fn);
          }
        }
      }

      for (uint64_t continuation_pc :
           parseLocalizedContinuationCalleePcs(child_model, func_va)) {
        auto *target_fn = findNearestDefinedLiftedOrBlock(continuation_pc);
        if (!target_fn)
          continue;
        if (extra_output_roots.insert(target_fn).second)
          ++promoted_continuation_roots;
      }
      for (uint64_t frontier_pc :
           parseRootSliceFrontierTargetPcs(child_model, func_va)) {
        auto *target_fn = findNearestDefinedLiftedOrBlock(frontier_pc);
        if (!target_fn && attempted_frontier_imports < kMaxFrontierImports) {
          ++attempted_frontier_imports;
          auto child = runTerminalBoundaryChildLift(frontier_pc, /*no_abi=*/true,
                                                    opts.generic_static_devirtualize,
                                                    /*enable_recovery_mode=*/true,
                                                    /*dump_virtual_model=*/true);
          if (child) {
            target_fn = importLiftedChildClosure(frontier_pc, child->ir_text,
                                                 child->model_text,
                                                 "tbrec_");
          }
        }
        if (!target_fn)
          continue;
        if (extra_output_roots.insert(target_fn).second)
          ++promoted_frontier_roots;
      }

      worklist.assign(output_roots.begin(), output_roots.end());
      visited.clear();
      while (!worklist.empty()) {
        auto *F = worklist.pop_back_val();
        if (!visited.insert(F).second)
          continue;

        for (auto &BB : *F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!call)
              continue;
            if (auto *callee = call->getCalledFunction()) {
              if (!callee->isDeclaration())
                worklist.push_back(callee);
              if (!omill::isDispatchCallName(callee->getName()) ||
                  call->arg_size() < 2) {
                continue;
              }
            } else {
              continue;
            }

            auto *pc_ci =
                llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
            if (!pc_ci)
              continue;
            auto *target_fn =
                findNearestDefinedLiftedOrBlock(pc_ci->getZExtValue());
            if (!target_fn || target_fn == F ||
                target_fn->getFunctionType() != call->getFunctionType()) {
              continue;
            }
            call->setCalledFunction(target_fn);
            ++rewritten_dispatch_calls_after_import;
          }
        }
      }

      if (extra_output_roots.empty())
        return child_ir.str();

      for (auto *F : extra_output_roots) {
        F->addFnAttr("omill.output_root");
        F->addFnAttr("omill.internal_output_root", "1");
      }

      for (auto &F : *child_module) {
        if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
          continue;
        if (F.hasFnAttribute("omill.internal_output_root"))
          continue;
        for (const auto &entry : original_output_root_attrs)
          F.addFnAttr(entry.getKey(), entry.getValue());
      }

      std::string prepared_ir;
      llvm::raw_string_ostream os(prepared_ir);
      child_module->print(os, nullptr);
      os.flush();
      errs() << "[abi-child] promoted-dispatch-helper-output-roots="
             << extra_output_roots.size()
             << " rewritten-dispatch-calls=" << rewritten_dispatch_calls
             << " rewritten-dispatch-calls-after-import="
             << rewritten_dispatch_calls_after_import
             << " promoted-continuation-roots="
             << promoted_continuation_roots
             << " promoted-frontier-roots=" << promoted_frontier_roots
             << "\n";
      return prepared_ir;
    };

    std::string prepared_noabi_child_ir =
        prepareMainRootNoABIChildForABIReplay(noabi_child->ir_text,
                                              noabi_child->model_text);
    dumpTextIfEnvEnabled(prepared_noabi_child_ir,
                         "OMILL_DEBUG_DUMP_PREPARED_MAIN_ROOT_NOABI_CHILD_IR",
                         "prepared_main_root_noabi_child.ll");
    auto replayed_ir = recoverABIForTerminalBoundaryIR(prepared_noabi_child_ir);
    if (!replayed_ir)
      return false;

    llvm::SMDiagnostic parse_error;
    auto replayed_module =
        llvm::parseAssemblyString(*replayed_ir, parse_error, ctx);
    if (!replayed_module)
      return false;
    if (verifyModule(*replayed_module, nullptr))
      return false;
    auto ensure_output_root = [&](llvm::Module &M) -> bool {
      auto pickUnique = [](llvm::ArrayRef<llvm::Function *> candidates)
          -> llvm::Function * {
        return candidates.size() == 1 ? candidates.front() : nullptr;
      };
      std::string target_hex = llvm::utohexstr(func_va);
      llvm::SmallVector<llvm::Function *, 8> exact_target_roots;
      llvm::SmallVector<llvm::Function *, 8> exact_target_lifted_roots;
      llvm::SmallVector<llvm::Function *, 8> exact_target_native_roots;
      llvm::SmallVector<llvm::Function *, 8> output_roots;
      llvm::SmallVector<llvm::Function *, 8> lifted_functions;
      llvm::SmallVector<llvm::Function *, 8> native_functions;
      llvm::SmallVector<llvm::Function *, 8> defined_functions;
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        defined_functions.push_back(&F);
        if (F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
        if (!F.getName().ends_with("_native"))
          lifted_functions.push_back(&F);
        if (F.getName().ends_with("_native"))
          native_functions.push_back(&F);
        const bool is_exact_lifted =
            (F.getName() == ("sub_" + target_hex)) ||
            (F.getName() == ("blk_" + target_hex)) ||
            (F.getName().contains(target_hex) &&
             !F.getName().ends_with("_native"));
        const bool is_exact_native =
            (F.getName() == ("sub_" + target_hex + "_native")) ||
            (F.getName() == ("blk_" + target_hex + "_native")) ||
            (F.getName().contains(target_hex) &&
             F.getName().ends_with("_native"));
        if (is_exact_lifted)
          exact_target_lifted_roots.push_back(&F);
        if (is_exact_native)
          exact_target_native_roots.push_back(&F);
        if (is_exact_lifted || is_exact_native) {
          exact_target_roots.push_back(&F);
        }
      }
      if (!output_roots.empty())
        return true;

      llvm::Function *root = nullptr;
      if (auto *F = pickUnique(exact_target_lifted_roots))
        root = F;
      else if (auto *F = pickUnique(exact_target_roots))
        root = F;
      else if (auto *F = pickUnique(lifted_functions))
        root = F;
      else if (auto *F = pickUnique(native_functions))
        root = F;
      if (!root)
        root = pickUnique(defined_functions);
      if (!root)
        return false;
      root->addFnAttr("omill.output_root");
      return true;
    };
    if (!ensure_output_root(*replayed_module))
      return false;
    bool requires_hidden_entry_seed_preservation = false;
    if (auto it = original_output_root_attrs.find("omill.export_entry_seed_exprs");
        it != original_output_root_attrs.end() && !it->second.empty()) {
      requires_hidden_entry_seed_preservation = true;
    }

    for (auto &F : *replayed_module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      if (F.hasFnAttribute("omill.internal_output_root"))
        continue;
      for (const auto &entry : original_output_root_attrs)
        F.addFnAttr(entry.getKey(), entry.getValue());
    }

    if (requires_hidden_entry_seed_preservation) {
      bool preserved = false;
      for (auto &F : *replayed_module) {
        if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
          continue;
        auto attr = F.getFnAttribute("omill.export_entry_seed_exprs");
        preserved = attr.isValid() && attr.isStringAttribute() &&
                    !attr.getValueAsString().empty();
        break;
      }
      if (!preserved)
        return false;
    }

    auto saved_module = std::move(module);
    module = std::move(replayed_module);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());

    rerunLateNativeArgRepair();
    repairMalformedPHIs(*module);
    annotateVmUnresolvedContinuationsInCurrentModule();
    annotateOutputRootTerminalBoundaryProbeChains();
    runFinalOutputCleanup();
    rerunLateOutputRootTargetPipeline();
    annotateOutputRootTerminalBoundaryProbeChains();
    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
    repairMalformedPHIs(*module);
    annotateVmUnresolvedContinuationsInCurrentModule();
    auto unresolved_after_child_replay = collectUnresolvedOutputRootPcCalls();
    auto function_return_leaks = collectOutputRootFunctionReturnLeaks();
    if (!unresolved_after_child_replay.empty() || countDefinedOutputRoots() == 0u) {
      dumpModuleIfEnvEnabled(
          *module, "OMILL_DEBUG_DUMP_CHILD_NOABI_REPLAY_CANDIDATE",
          "child_noabi_replay_candidate.ll");
      errs() << "External main-root no-ABI child replay not adopted"
             << " roots=" << countDefinedOutputRoots()
             << " unresolved=";
      for (size_t i = 0; i < unresolved_after_child_replay.size(); ++i) {
        if (i)
          errs() << ",";
        errs() << unresolved_after_child_replay[i];
      }
      if (!function_return_leaks.empty()) {
        errs() << " function_return_leaks=";
        for (size_t i = 0; i < function_return_leaks.size(); ++i) {
          if (i)
            errs() << ",";
          errs() << function_return_leaks[i];
        }
      }
      errs() << "\n";
      module = std::move(saved_module);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      repairMalformedPHIs(*module);
      return false;
    }

    events.emitInfo("main_root_noabi_child_replay_adopted",
                    "replayed ABI from external main-root no-ABI child",
                    {{"defined_output_roots",
                      static_cast<int64_t>(countDefinedOutputRoots())}});
    return true;
  };

  auto sanitizeRemainingPoisonNativeHelperArgs = [&]() {
    auto parseParamOffsets = [&](llvm::Function &F) {
      llvm::SmallVector<int, 16> offsets;
      if (auto attr = F.getFnAttribute("omill.param_state_offsets");
          attr.isValid() && attr.isStringAttribute()) {
        llvm::SmallVector<llvm::StringRef, 16> parts;
        attr.getValueAsString().split(parts, ',');
        for (auto &part : parts) {
          if (part == "stack" || part == "xmm") {
            offsets.push_back(-1);
            continue;
          }
          unsigned off = 0;
          if (part.getAsInteger(10, off))
            offsets.push_back(-1);
          else
            offsets.push_back(static_cast<int>(off));
        }
      }
      return offsets;
    };

    unsigned repaired = 0;
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto stateArgIndex = [&](llvm::Function &Fn) -> std::optional<unsigned> {
      for (unsigned i = 0; i < Fn.arg_size(); ++i) {
        auto *arg = Fn.getArg(i);
        for (auto *U : arg->users()) {
          auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
          if (!BO || BO->getOpcode() != llvm::Instruction::Add)
            continue;
          auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
          auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
          if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
              (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
            return i;
          }
        }
      }
      return std::nullopt;
    };
    auto isPointerLikeStateValue = [&](llvm::Value *V) {
      V = V->stripPointerCasts();
      return llvm::isa<llvm::PtrToIntInst>(V) || V->getType()->isPointerTy();
    };
    auto findLocalSyntheticStateBase = [&](llvm::Function &F,
                                           llvm::StringRef callee_name,
                                           llvm::Instruction *InsertBefore)
        -> llvm::Value * {
      llvm::AllocaInst *match = nullptr;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
          if (!AI)
            continue;
          if (AI->getName().starts_with(callee_name) &&
              AI->getAllocatedType()->isArrayTy()) {
            match = AI;
            break;
          }
        }
        if (match)
          break;
      }
      if (!match)
        return nullptr;
      llvm::IRBuilder<> Builder(InsertBefore);
      return Builder.CreatePtrToInt(match, i64_ty,
                                    callee_name + ".statebase.reuse");
    };
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      auto caller_offsets = parseParamOffsets(F);
      if (caller_offsets.empty())
        continue;
      auto caller_state_arg_index = stateArgIndex(F);
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          auto *Callee = CI ? CI->getCalledFunction() : nullptr;
          if (!Callee || Callee->isDeclaration() ||
              !Callee->getName().ends_with("_native")) {
            continue;
          }

          auto callee_offsets = parseParamOffsets(*Callee);
          if (callee_offsets.size() != CI->arg_size())
            continue;
          auto callee_state_arg_index = stateArgIndex(*Callee);

          llvm::SmallVector<llvm::Value *, 16> new_args;
          bool changed = false;
          for (unsigned i = 0; i < CI->arg_size(); ++i) {
            auto *arg = CI->getArgOperand(i);
            llvm::Value *replacement = nullptr;
            if (callee_state_arg_index && i == *callee_state_arg_index &&
                !isPointerLikeStateValue(arg)) {
              if (caller_state_arg_index &&
                  *caller_state_arg_index < F.arg_size()) {
                replacement = F.getArg(*caller_state_arg_index);
              } else {
                replacement =
                    findLocalSyntheticStateBase(F, Callee->getName(), CI);
              }
            }
            int target_off = callee_offsets[i];
            llvm::Value *mapped_caller_arg = nullptr;
            if (!replacement && target_off >= 0) {
              for (unsigned j = 0; j < caller_offsets.size() && j < F.arg_size();
                   ++j) {
                if (caller_offsets[j] == target_off) {
                  mapped_caller_arg = F.getArg(j);
                  break;
                }
              }
            }
            bool needs_repair =
                llvm::isa<llvm::PoisonValue>(arg) ||
                llvm::isa<llvm::UndefValue>(arg);
            if (!needs_repair && replacement && arg != replacement)
              needs_repair = true;
            if (!needs_repair && mapped_caller_arg) {
              if (auto *caller_arg = llvm::dyn_cast<llvm::Argument>(arg);
                  caller_arg && caller_arg->getParent() == &F &&
                  caller_arg != mapped_caller_arg) {
                needs_repair = true;
              } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(arg);
                         ci && ci->isZero()) {
                needs_repair = true;
              }
            }
            if (!needs_repair) {
              new_args.push_back(arg);
              continue;
            }

            if (!replacement)
              replacement = mapped_caller_arg;
            if (!replacement)
              replacement = llvm::ConstantInt::get(i64_ty, 0);
            if (replacement->getType() != arg->getType()) {
              llvm::IRBuilder<> Builder(CI);
              if (replacement->getType()->isIntegerTy() &&
                  arg->getType()->isIntegerTy()) {
                replacement = Builder.CreateIntCast(replacement, arg->getType(),
                                                    false,
                                                    Callee->getName() +
                                                        ".poisonfix.cast");
              } else if (replacement->getType()->isPointerTy() &&
                         arg->getType()->isIntegerTy()) {
                replacement = Builder.CreatePtrToInt(
                    replacement, arg->getType(),
                    Callee->getName() + ".poisonfix.pti");
              } else if (replacement->getType()->isIntegerTy() &&
                         arg->getType()->isPointerTy()) {
                replacement = Builder.CreateIntToPtr(
                    replacement, arg->getType(),
                    Callee->getName() + ".poisonfix.itp");
              }
            }
            new_args.push_back(replacement);
            changed = true;
          }

          if (!changed)
            continue;

          auto *new_call = llvm::CallInst::Create(
              Callee->getFunctionType(), Callee, new_args, CI->getName(),
              CI->getIterator());
          new_call->setCallingConv(CI->getCallingConv());
          new_call->setAttributes(CI->getAttributes());
          if (!CI->use_empty()) {
            if (CI->getType() == new_call->getType()) {
              CI->replaceAllUsesWith(new_call);
            } else if (llvm::isa<llvm::StructType>(new_call->getType())) {
              auto *ev = llvm::ExtractValueInst::Create(
                  new_call, {0}, "ret.primary",
                  std::next(new_call->getIterator()));
              CI->replaceAllUsesWith(ev);
            } else {
              CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
            }
          }
          CI->eraseFromParent();
          ++repaired;
        }
      }
    }
    if (repaired > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] sanitized-poison-native-helper-args=" << repaired
             << "\n";
    }
  };
  auto eraseNoOpSelfRecursiveNativeCalls = [&]() {
    unsigned erased = 0;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->getCalledFunction() != &F || !CI->use_empty() ||
              CI->arg_size() != F.arg_size()) {
            continue;
          }
          bool same_args = true;
          for (unsigned i = 0; i < CI->arg_size(); ++i) {
            if (CI->getArgOperand(i) != F.getArg(i)) {
              same_args = false;
              break;
            }
          }
          if (!same_args)
            continue;
          CI->eraseFromParent();
          ++erased;
        }
      }
    }
    if (erased > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] erased-noop-self-recursive-native-calls=" << erased
             << "\n";
    }
  };
  auto buildFrontierCallbacks = [&]() {
    omill::FrontierCallbacks callbacks;
    callbacks.is_code_address = [&](uint64_t target) {
      return isCodeAddressInCurrentInput(target);
    };
    callbacks.has_defined_target = [&](uint64_t target) {
      return hasDefinedLiftedOrBlockTarget(target);
    };
    callbacks.normalize_target_pc = [&](uint64_t target) {
      return normalizeKnownVmContinuationTarget(target);
    };
    callbacks.is_executable_target = [&](uint64_t target) {
      return memory_map_holder->isExecutable(target, 1);
    };
    callbacks.is_protected_boundary = [&](uint64_t target) {
      return !RawBinary &&
             omill::classifyProtectedBoundary(pe.memory_map, target).has_value();
    };
    callbacks.is_exact_call_fallthrough_target = [&](uint64_t target) {
      return omill::isExactX86DirectControlFlowFallthrough(&pe.memory_map,
                                                           target);
    };
    callbacks.can_decode_target = [&](uint64_t target) {
      auto decodable =
          omill::isDecodableLiftTargetEntry(&pe.memory_map, target,
                                            opts.target_arch);
      return decodable.has_value() && *decodable;
    };
    callbacks.read_target_bytes = [&](uint64_t target, uint8_t *out,
                                      size_t size) {
      return pe.memory_map.read(target, out, static_cast<unsigned>(size));
    };
    callbacks.decode_target_summary = [&](uint64_t target)
        -> std::optional<omill::FrontierCallbacks::DecodedTargetSummary> {
      std::string probe_bytes;
      probe_bytes.resize(15);
      if (!pe.memory_map.read(target,
                              reinterpret_cast<uint8_t *>(probe_bytes.data()),
                              static_cast<unsigned>(probe_bytes.size()))) {
        return std::nullopt;
      }
      remill::Instruction inst;
      inst.Reset();
      if (!arch->DecodeInstruction(target, probe_bytes, inst,
                                   arch->CreateInitialContext())) {
        return std::nullopt;
      }

      omill::FrontierCallbacks::DecodedTargetSummary summary;
      summary.pc = target;
      summary.next_pc = inst.next_pc;
      summary.is_control_flow = inst.IsControlFlow();
      summary.is_conditional = inst.IsConditionalBranch();
      summary.is_call = inst.IsFunctionCall();
      summary.is_return = inst.IsFunctionReturn();
      summary.is_terminal = inst.IsFunctionReturn();
      switch (inst.category) {
        case remill::Instruction::kCategoryIndirectJump:
        case remill::Instruction::kCategoryConditionalIndirectJump:
        case remill::Instruction::kCategoryIndirectFunctionCall:
        case remill::Instruction::kCategoryConditionalIndirectFunctionCall:
          summary.is_indirect = true;
          break;
        default:
          break;
      }
      if (inst.branch_taken_pc)
        summary.branch_taken_pc = inst.branch_taken_pc;
      if (inst.branch_not_taken_pc)
        summary.branch_not_taken_pc = inst.branch_not_taken_pc;
      if (summary.is_call && !summary.branch_not_taken_pc && inst.next_pc)
        summary.branch_not_taken_pc = inst.next_pc;
      return summary;
    };
    return callbacks;
  };
  auto advanceSessionOwnedFrontierWork =
      [&](omill::FrontierDiscoveryPhase phase, llvm::StringRef label) {
        if (RawBinary || !block_lifter || !iterative_session ||
            !devirtualization_plan.enable_devirtualization) {
          return false;
        }
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":before_callbacks")
                              .str()
                              .c_str());
        auto callbacks = buildFrontierCallbacks();
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":after_callbacks")
                              .str()
                              .c_str());
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":before_discover")
                              .str()
                              .c_str());
        if (events.detailed()) {
          events.emitInfo("frontier_discovery_started",
                          "session-owned frontier discovery started",
                          {{"label", label.str()}});
        }
        auto round = devirtualization_runtime.runFrontierRound(
            *module, *block_lifter, *iterative_session, callbacks, phase);
        if (round.crashed) {
          errs() << "WARNING: late frontier advance crashed for " << label
                 << "\n";
          if (events.detailed()) {
            events.emitWarn("frontier_advance_crashed",
                            "session-owned frontier advance crashed",
                            {{"label", label.str()}});
          }
          return false;
        }
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":after_discover")
                              .str()
                              .c_str());
        if (events.detailed()) {
          events.emitInfo("frontier_advance_completed",
                          "session-owned frontier advance completed",
                          {{"label", label.str()},
                           {"summary",
                            devirtualization_orchestrator
                                .summarizeFrontierAdvance(round.advance)}});
          events.emitInfo(
              "frontier_discovery_completed",
              "session-owned frontier discovery completed",
              {{"label", label.str()},
               {"summary",
                devirtualization_orchestrator.summarizeFrontierAdvance(
                    round.discover)}});
        }
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":after_advance")
                              .str()
                              .c_str());
        const bool changed = round.changed;
        const bool debug_late_closure_targets =
            parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
        if (debug_late_closure_targets) {
          errs() << "[frontier] " << label << " discover "
                 << devirtualization_orchestrator.summarizeFrontierAdvance(
                        round.discover)
                 << "\n";
          errs() << "[frontier] " << label << " advance "
                 << devirtualization_orchestrator.summarizeFrontierAdvance(
                        round.advance)
                 << "\n";
          for (const auto &item :
               devirtualization_orchestrator.session().discovered_frontier_work_items) {
            if (!item.target_pc)
              continue;
            errs() << "[frontier] item=0x" << llvm::utohexstr(*item.target_pc)
                   << " kind=" << omill::toString(item.kind)
                   << " status=" << omill::toString(item.status)
                   << " id=" << item.identity << "\n";
          }
        }
        if (!changed)
          return false;

        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        repairMalformedPHIs(*module);
        errs() << "[frontier] " << label << " "
               << devirtualization_orchestrator.summarizeFrontierAdvance(
                      round.advance)
               << "\n";
        return true;
      };
  auto noteAbiPostCleanupStep = [&](llvm::StringRef label, bool starting) {
    const bool debug_abi_post_cleanup =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    if (debug_abi_post_cleanup) {
      errs() << "[abi-post-step] " << (starting ? "begin " : "end ") << label
             << "\n";
    }
    if (events.detailed()) {
      events.emitInfo(starting ? "abi_post_cleanup_step_started"
                               : "abi_post_cleanup_step_completed",
                      starting ? "abi post-cleanup step started"
                               : "abi post-cleanup step completed",
                      {{"label", label.str()}});
    }
  };
  llvm::SmallVector<std::string, 8> unresolved_pc_output_roots;
  std::optional<omill::FrontierCallbacks> output_recovery_frontier_callbacks;
  if (!RawBinary && block_lifter && iterative_session &&
      devirtualization_plan.enable_devirtualization) {
    output_recovery_frontier_callbacks = buildFrontierCallbacks();
  }
  const bool precise_runtime_output_recovery_logs =
      parseBoolEnv("OMILL_DEBUG_RUNTIME_OUTPUT_RECOVERY").value_or(false);
  omill::tooling::OutputRecoveryOptionInputs output_recovery_option_inputs;
  output_recovery_option_inputs.raw_binary = RawBinary;
  output_recovery_option_inputs.no_abi = NoABI;
  output_recovery_option_inputs.use_block_lifting = opts.use_block_lifting;
  output_recovery_option_inputs.enable_devirtualization =
      devirtualization_plan.enable_devirtualization;
  output_recovery_option_inputs.enable_precise_logs =
      precise_runtime_output_recovery_logs;
  output_recovery_option_inputs.allow_noabi_postmain_rounds =
      allow_noabi_postmain_rounds;
  output_recovery_option_inputs.allow_abi_postmain_rounds =
      allow_abi_postmain_rounds;
  output_recovery_option_inputs.enable_nested_vm_enter_child_import =
      !RawBinary && !NoABI &&
      parseBoolEnv("OMILL_ENABLE_NESTED_VM_ENTER_CHILD_IMPORT").value_or(false);
  output_recovery_option_inputs.max_vm_enter_child_imports =
      parseUnsignedEnv("OMILL_MAIN_ROOT_CHILD_MAX_VM_ENTER_IMPORTS")
          .value_or(1u);
  auto output_recovery_options =
      omill::tooling::buildOutputRecoveryOptions(
          output_recovery_option_inputs);

  omill::tooling::OutputRecoveryAdapterContext output_recovery_adapter_context{
      *module, ctx, MAM};
  output_recovery_adapter_context.append_debug_marker =
      [&](llvm::StringRef marker) {
        auto marker_text = marker.str();
        appendDebugMarker(marker_text.c_str());
      };
  output_recovery_adapter_context.emit_warn_event =
      [&](llvm::StringRef code, llvm::StringRef message,
          std::optional<int64_t> round) {
        errs() << "WARNING: " << message;
        if (round)
          errs() << " round " << *round;
        errs() << "\n";
        if (round) {
          events.emitWarn(code, message, {{"round", *round}});
        } else {
          events.emitWarn(code, message);
        }
      };
  output_recovery_adapter_context.precise_log =
      [&](const omill::RuntimePreciseLogEvent &event) {
        errs() << "[runtime-precise] " << event.component << ":"
               << event.stage;
        if (event.round)
          errs() << " round=" << *event.round;
        if (event.target_pc)
          errs() << " target=0x" << llvm::utohexstr(*event.target_pc);
        errs() << " " << event.message;
        if (event.detail && !event.detail->empty())
          errs() << " detail=" << *event.detail;
        errs() << "\n";
        if (events.enabled() && events.detailed()) {
          llvm::json::Object payload;
          payload["component"] = event.component;
          payload["stage"] = event.stage;
          if (event.round)
            payload["round"] = static_cast<int64_t>(*event.round);
          if (event.target_pc)
            payload["target_pc"] = hexString(*event.target_pc);
          if (event.detail && !event.detail->empty())
            payload["detail"] = *event.detail;
          events.emitInfo("runtime_precise_log", event.message,
                          std::move(payload));
        }
      };
  output_recovery_adapter_context.run_late_closure_canonicalization =
      [&](llvm::StringRef reason) { runLateClosureCanonicalization(reason); };
  output_recovery_adapter_context.run_post_patch_cleanup =
      [&](llvm::StringRef reason) { runPostPatchCleanup(reason); };
  output_recovery_adapter_context.run_final_output_cleanup =
      [&]() { runFinalOutputCleanup(); };
  output_recovery_adapter_context.annotate_vm_unresolved_continuations =
      [&]() { annotateVmUnresolvedContinuationsInCurrentModule(); };
  output_recovery_adapter_context.prune_to_defined_output_root_closure =
      [&]() { pruneToDefinedOutputRootClosure(); };
  output_recovery_adapter_context.rerun_late_output_root_target_pipeline =
      [&]() { rerunLateOutputRootTargetPipeline(); };
  output_recovery_adapter_context
      .sanitize_remaining_poison_native_helper_args =
      [&]() { sanitizeRemainingPoisonNativeHelperArgs(); };
  output_recovery_adapter_context.erase_noop_self_recursive_native_calls =
      [&]() { eraseNoOpSelfRecursiveNativeCalls(); };
  output_recovery_adapter_context.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase phase, llvm::StringRef label) {
        return advanceSessionOwnedFrontierWork(phase, label);
      };
  output_recovery_adapter_context.lift_child_text =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode, bool dump_virtual_model)
      -> std::optional<omill::tooling::ChildLiftTextArtifact> {
        auto child = runTerminalBoundaryChildLift(target_pc, no_abi, enable_gsd,
                                                  enable_recovery_mode,
                                                  dump_virtual_model);
        if (!child)
          return std::nullopt;
        return omill::tooling::ChildLiftTextArtifact{
            std::move(child->ir_text), std::move(child->model_text)};
      };
  output_recovery_adapter_context.import_executable_child_root =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &import_plan,
          llvm::StringRef name_prefix) -> llvm::Function * {
        return importSimpleExecutableChildRoot(target_pc, artifact,
                                               import_plan, name_prefix);
      };
  output_recovery_adapter_context.import_recovered_terminal_boundary_function =
      [&](llvm::StringRef ir_text, uint64_t target_pc,
          std::string *rejection_reason) -> llvm::Function * {
        return importRecoveredTerminalBoundaryFunction(ir_text, target_pc,
                                                       rejection_reason);
      };
  output_recovery_adapter_context.note_imported_target = [&](uint64_t target_pc) {
    if (iterative_session)
      iterative_session->noteLiftedTarget(target_pc);
  };
  output_recovery_adapter_context
      .collect_executable_placeholder_declaration_targets = [&]() {
        auto targets = collectExecutablePlaceholderDeclarationTargets();
        return std::vector<uint64_t>(targets.begin(), targets.end());
      };
  output_recovery_adapter_context
      .collect_declared_structural_targets_with_defined_implementations =
      [&]() {
        auto targets =
            collectDeclaredStructuralTargetsWithDefinedImplementations();
        return std::vector<uint64_t>(targets.begin(), targets.end());
      };
  output_recovery_adapter_context.collect_output_root_constant_code_call_targets =
      [&]() {
        auto targets = collectOutputRootConstantCodeCallTargets();
        return std::vector<uint64_t>(targets.begin(), targets.end());
      };
  output_recovery_adapter_context
      .collect_output_root_constant_calli_targets = [&]() {
        auto targets = collectOutputRootConstantCalliTargets();
        return std::vector<uint64_t>(targets.begin(), targets.end());
      };
  output_recovery_adapter_context
      .collect_output_root_constant_dispatch_targets = [&]() {
        auto targets = collectOutputRootConstantDispatchTargets();
        return std::vector<uint64_t>(targets.begin(), targets.end());
      };
  output_recovery_adapter_context.patch_constant_inttoptr_calls_to_native =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) {
        llvm::SmallVector<uint64_t, 32> ordered_targets(targets.begin(),
                                                        targets.end());
        patchConstantIntToPtrCallsToNative(ordered_targets, marker, message);
      };
  output_recovery_adapter_context
      .patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        llvm::SmallVector<uint64_t, 32> ordered_targets(targets.begin(),
                                                        targets.end());
        return patchDeclaredLiftedOrBlockCallsToDefinedTargets(ordered_targets,
                                                               marker, message);
      };
  output_recovery_adapter_context.patch_constant_calli_targets_to_direct_calls =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        llvm::SmallVector<uint64_t, 32> ordered_targets(targets.begin(),
                                                        targets.end());
        return patchConstantCalliTargetsToDirectCalls(ordered_targets, marker,
                                                      message);
      };
  output_recovery_adapter_context
      .patch_constant_dispatch_targets_to_direct_calls =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        llvm::SmallVector<uint64_t, 32> ordered_targets(targets.begin(),
                                                        targets.end());
        return patchConstantDispatchTargetsToDirectCalls(ordered_targets, marker,
                                                         message);
      };
  output_recovery_adapter_context.note_abi_post_cleanup_step =
      [&](llvm::StringRef label, bool starting) {
        noteAbiPostCleanupStep(label, starting);
      };
  auto output_recovery_callbacks =
      omill::tooling::buildOutputRecoveryCallbacks(
          output_recovery_adapter_context);

  auto output_recovery_summary = devirtualization_runtime.runOutputRecovery(
      *module, block_lifter.get(), iterative_session.get(),
      output_recovery_frontier_callbacks
          ? &*output_recovery_frontier_callbacks
          : nullptr,
      output_recovery_options, output_recovery_callbacks);
  if (events.detailed()) {
    events.emitInfo(
        "runtime_output_recovery_completed",
        "runtime-owned output recovery completed",
        {{"changed", output_recovery_summary.changed},
         {"noabi_imported_children",
          static_cast<int64_t>(output_recovery_summary.noabi_imported_children)},
         {"abi_imported_vm_enter_children",
          static_cast<int64_t>(
              output_recovery_summary.abi_imported_vm_enter_children)},
         {"patched_declared_targets",
          static_cast<int64_t>(output_recovery_summary.patched_declared_targets)},
         {"patched_code_targets",
          static_cast<int64_t>(output_recovery_summary.patched_code_targets)},
         {"patched_calli_targets",
          static_cast<int64_t>(output_recovery_summary.patched_calli_targets)},
         {"patched_dispatch_targets",
          static_cast<int64_t>(
              output_recovery_summary.patched_dispatch_targets)},
         {"artifact_bundle_count",
          static_cast<int64_t>(output_recovery_summary.artifact_bundles.size())}});
  }
  emitRuntimeArtifactBundleEvents(events, "output_recovery",
                                  output_recovery_summary.artifact_bundles);
  for (const auto &note : output_recovery_summary.notes)
    errs() << "[runtime-output-recovery] " << note << "\n";

  if (!RawBinary && !NoABI)
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();

  if ((!unresolved_pc_output_roots.empty() ||
       (!RawBinary && !NoABI && countDefinedOutputRoots() == 0u)) &&
      tryReplayABIFromPreABICheckpoint()) {
    annotateVmUnresolvedContinuationsInCurrentModule();
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }

  if ((!unresolved_pc_output_roots.empty() ||
       (!RawBinary && !NoABI && countDefinedOutputRoots() == 0u)) &&
      tryReplayABIFromExternalMainRootNoABIChild()) {
    annotateVmUnresolvedContinuationsInCurrentModule();
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }

  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_BEFORE_UNRESOLVED_CHECK",
                         "before_unresolved_check.ll");

  if (!unresolved_pc_output_roots.empty()) {
    errs() << "Error: unresolved lifted control transfer remains in output "
              "root closure(s): ";
    for (size_t i = 0; i < unresolved_pc_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << unresolved_pc_output_roots[i];
    }
    errs() << "\n";
    return fail(1,
                "unresolved lifted control transfer remains in output root closures");
  }

  if (!RawBinary && !NoABI && countDefinedOutputRoots() == 0u) {
    errs() << "Error: no defined output root remains after ABI recovery\n";
    return fail(1, "no defined output root remains after ABI recovery");
  }

  llvm::SmallVector<std::string, 8> suspicious_zero_arity_output_roots;
  if (!RawBinary && !NoABI && devirtualization_plan.enable_devirtualization)
    devirtualization_orchestrator.refreshSessionState(*module);
  const bool has_blocking_session_frontier_state =
      !RawBinary && !NoABI && devirtualization_plan.enable_devirtualization &&
      devirtualization_orchestrator.hasBlockingUnstableFrontierState(*module);
  if (!RawBinary && !NoABI)
    suspicious_zero_arity_output_roots = collectSuspiciousZeroArityOutputRoots();
  if (!suspicious_zero_arity_output_roots.empty()) {
    bool devirtualization_invariants_clean = false;
    if (devirtualization_plan.enable_devirtualization &&
        unresolved_pc_output_roots.empty() && countDefinedOutputRoots() != 0u) {
      devirtualization_invariants_clean =
          devirtualization_orchestrator
              .collectInvariantViolations(*module,
                                          devirtualization_request.output_mode)
              .empty();
    }
    if (devirtualization_plan.enable_devirtualization &&
        (!has_blocking_session_frontier_state ||
         devirtualization_invariants_clean) &&
        unresolved_pc_output_roots.empty() &&
        countDefinedOutputRoots() != 0u) {
      errs() << "Warning: retaining suspicious zero-arity stack-backed output "
                "root(s) because devirtualization state is stable: ";
      for (size_t i = 0; i < suspicious_zero_arity_output_roots.size(); ++i) {
        if (i)
          errs() << ", ";
        errs() << suspicious_zero_arity_output_roots[i];
      }
      errs() << "\n";
      if (events.detailed()) {
        events.emitWarn(
            "suspicious_zero_arity_output_root_retained",
            "retaining suspicious zero-arity output roots because "
            "devirtualization state is stable",
            {{"count",
              static_cast<int64_t>(suspicious_zero_arity_output_roots.size())}});
      }
      suspicious_zero_arity_output_roots.clear();
    }
  }
  if (!suspicious_zero_arity_output_roots.empty()) {
    if (auto rc =
            tryFastPlainNoBlockExportFallback("suspicious_zero_arity_output_root")) {
      return *rc;
    }
    errs() << "Error: suspicious zero-arity stack-backed output root(s): ";
    for (size_t i = 0; i < suspicious_zero_arity_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << suspicious_zero_arity_output_roots[i];
    }
    errs() << "\n";
    return fail(1, "suspicious zero-arity stack-backed output roots");
  }

  llvm::SmallVector<std::string, 8> suspicious_stack_backed_output_roots;
  if (!RawBinary && !NoABI && !normalized_export_thunk_root)
    suspicious_stack_backed_output_roots =
        collectSuspiciousStackBackedOutputRoots();
  if (!suspicious_stack_backed_output_roots.empty()) {
    if (auto rc = tryFastPlainNoBlockExportFallback(
            "suspicious_stack_backed_output_root")) {
      return *rc;
    }
    errs() << "Error: suspicious stack-backed output root(s): ";
    for (size_t i = 0; i < suspicious_stack_backed_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << suspicious_stack_backed_output_roots[i];
    }
    errs() << "\n";
    return fail(1, "suspicious stack-backed output roots");
  }

  // Final textual output should never contain dangling PHI predecessors.
  repairMalformedPHIs(*module);
  if (devirtualization_plan.enable_devirtualization) {
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kAbiOrNoAbiFinalization, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "final cleanup complete");
    emit_latest_devirtualization_epoch("final cleanup complete");
    auto devirtualization_violations =
        devirtualization_orchestrator.collectInvariantViolations(
            *module, devirtualization_request.output_mode);
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kFinalInvariantVerification, *module,
        devirtualization_request.output_mode, /*changed=*/false,
        "final verification complete");
    emit_latest_devirtualization_epoch("final verification complete");
    if (devirtualization_violations.empty()) {
      events.emitInfo("devirtualization_invariants_verified",
                      "devirtualization invariants verified",
                      {{"mode", NoABI ? "noabi" : "abi"}});
    } else {
      llvm::json::Array violations_json;
      for (const auto &violation : devirtualization_violations) {
        violations_json.push_back(violation);
        errs() << "Devirtualization invariant violation: " << violation
               << "\n";
      }
      llvm::json::Object payload;
      payload["mode"] = NoABI ? "noabi" : "abi";
      payload["count"] =
          static_cast<int64_t>(devirtualization_violations.size());
      payload["violations"] = std::move(violations_json);
      events.emitWarn("devirtualization_invariants_failed",
                      "devirtualization invariants failed",
                      std::move(payload));
      if (devirtualization_policy.enforce_final_invariants) {
        return fail(1, "devirtualization invariants failed");
      }
    }
  }

  auto collectReachableExternalCallsFromOutputRoots = [&]() {
    auto classifyLeakClass = [](llvm::StringRef callee_name) {
      if (callee_name == "__omill_missing_block_handler")
        return std::string("missing_block_handler");
      if (callee_name.starts_with("__remill_read_memory_") ||
          callee_name.starts_with("__remill_write_memory_")) {
        return std::string("remill_memory_intrinsic");
      }
      if (callee_name.starts_with("omill_executable_target_"))
        return std::string("executable_placeholder");
      if (callee_name.starts_with("omill_vm_enter_target_"))
        return std::string("vm_enter_placeholder");
      if (callee_name.starts_with("omill_native_target_") ||
          callee_name.starts_with("omill_native_boundary_")) {
        return std::string("native_placeholder");
      }
      if (callee_name.starts_with("__remill_"))
        return std::string("remill_runtime_intrinsic");
      return std::string("external_call");
    };

    struct ExternalCallWarning {
      std::string root_name;
      std::string caller_name;
      std::string callee_name;
      std::string leak_class;
    };

    llvm::SmallVector<llvm::Function *, 8> output_roots;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.internal_output_root")) {
        continue;
      }
      output_roots.push_back(&F);
    }
    if (output_roots.empty()) {
      for (auto &F : *module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
      }
    }

    llvm::SmallVector<ExternalCallWarning, 8> warnings;
    for (auto *root : output_roots) {
      llvm::SmallVector<llvm::Function *, 16> worklist = {root};
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      while (!worklist.empty()) {
        auto *current = worklist.pop_back_val();
        if (!current || !visited.insert(current).second)
          continue;
        for (auto &BB : *current) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            auto *callee = CB ? CB->getCalledFunction() : nullptr;
            if (!callee)
              continue;
            if (callee->isIntrinsic())
              continue;
            if (callee->isDeclaration()) {
              warnings.push_back(
                  {root->getName().str(), current->getName().str(),
                   callee->getName().str(),
                   classifyLeakClass(callee->getName())});
              continue;
            }
            worklist.push_back(callee);
          }
        }
      }
    }
    return warnings;
  };

  auto reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
  if (!reachable_external_calls.empty()) {
    llvm::json::Array warnings_json;
    llvm::json::Object counts_by_class;
    std::map<std::string, int64_t> class_counts;
    for (const auto &warning : reachable_external_calls) {
      ++class_counts[warning.leak_class];
      errs() << "Warning: reachable external call [" << warning.leak_class
             << "] from output root " << warning.root_name << ": "
             << warning.caller_name << " -> " << warning.callee_name << "\n";
      llvm::json::Object entry;
      entry["root"] = warning.root_name;
      entry["caller"] = warning.caller_name;
      entry["callee"] = warning.callee_name;
      entry["class"] = warning.leak_class;
      warnings_json.push_back(std::move(entry));
    }
    for (const auto &[klass, count] : class_counts)
      counts_by_class[klass] = count;
    llvm::json::Object payload;
    payload["count"] =
        static_cast<int64_t>(reachable_external_calls.size());
    payload["counts_by_class"] = std::move(counts_by_class);
    payload["calls"] = std::move(warnings_json);
    events.emitWarn("reachable_external_calls_in_output_root_closure",
                    "reachable external calls remain in output root closure",
                    std::move(payload));
  }

  auto finalization_summary = devirtualization_runtime.finalizeOutput(
      *module, devirtualization_plan.enable_devirtualization);
  omill::FinalStateRecoveryRequest final_state_recovery_request;
  final_state_recovery_request.no_abi = NoABI;
  final_state_recovery_request.enabled =
      NoABI && devirtualization_plan.enable_devirtualization;
  if (auto plan = devirtualization_runtime.planFinalStateRecovery(
          *module, final_state_recovery_request)) {
    finalization_summary.final_state_recovery_plan = *plan;
  }
  if (auto final_state_bundle = devirtualization_runtime.runFinalStateRecovery(
          *module, final_state_recovery_request, output_recovery_callbacks)) {
    finalization_summary.artifact_bundles.push_back(*final_state_bundle);
  }
  emitRuntimeArtifactBundleEvents(events, "finalization",
                                  finalization_summary.artifact_bundles);
  if (finalization_summary.has_protector_report) {
    const auto &protector_report = finalization_summary.protector_report;
    if (!protector_report.issues.empty()) {
      llvm::json::Array issues_json;
      llvm::json::Object counts_by_class;
      for (const auto &[klass, count] : protector_report.counts_by_class)
        counts_by_class[klass] = static_cast<int64_t>(count);
      for (const auto &issue : protector_report.issues) {
        llvm::json::Object entry;
        entry["class"] = omill::toString(issue.issue_class);
        if (!issue.root_name.empty())
          entry["root"] = issue.root_name;
        if (!issue.caller_name.empty())
          entry["caller"] = issue.caller_name;
        if (!issue.callee_name.empty())
          entry["callee"] = issue.callee_name;
        if (!issue.edge_identity.empty())
          entry["edge_identity"] = issue.edge_identity;
        if (!issue.message.empty())
          entry["message"] = issue.message;
        issues_json.push_back(std::move(entry));
        errs() << "Protector report [" << omill::toString(issue.issue_class)
               << "]";
        if (!issue.edge_identity.empty())
          errs() << " edge=" << issue.edge_identity;
        if (!issue.caller_name.empty())
          errs() << " caller=" << issue.caller_name;
        if (!issue.callee_name.empty())
          errs() << " callee=" << issue.callee_name;
        if (!issue.message.empty())
          errs() << " " << issue.message;
        errs() << "\n";
      }
      llvm::json::Object payload;
      payload["count"] =
          static_cast<int64_t>(protector_report.issues.size());
      payload["counts_by_class"] = std::move(counts_by_class);
      payload["issues"] = std::move(issues_json);
      events.emitWarn("protector_model_validation_report",
                      "protector-focused validation report",
                      std::move(payload));
    }
  }

  if (!RawBinary && !NoABI && fast_plain_export_root_fallback &&
      opts.use_block_lifting) {
    auto large_stack_output_roots = collectLargeStackOutputRoots();
    if (!large_stack_output_roots.empty()) {
      if (auto rc = tryFastPlainNoBlockExportFallback("large_stack_output_root"))
        return *rc;
    }
  }

  if (events.detailed()) {
    std::optional<omill::ProtectorValidationReport> report;
    if (finalization_summary.has_protector_report)
      report = finalization_summary.protector_report;
    std::string artifact_report_path;
    if (writeRuntimeArtifactReport(
            OutputFilename, devirtualization_runtime.roundArtifactBundles(),
            report, &artifact_report_path)) {
      events.emitInfo("runtime_artifact_report_written",
                      "runtime artifact report written",
                      {{"path", artifact_report_path},
                       {"bundle_count",
                        static_cast<int64_t>(
                            devirtualization_runtime.roundArtifactBundles()
                                .size())}});
    }
  }

  // Write final output
  if (canonicalizeTerminalMissingBlockDispatchSuffixes())
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  std::error_code EC;
  events.emitInfo("output_write_started", "writing final output",
                  {{"path", OutputFilename}});
  ToolOutputFile Out(OutputFilename, EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "Error opening output: " << EC.message() << "\n";
    return fail(1, "failed to open output file");
  }
  appendDebugMarker("final_output:before_print");
  module->print(Out.os(), nullptr);
  appendDebugMarker("final_output:after_print");
  Out.keep();
  events.emitInfo("output_write_completed", "output write complete",
                  {{"path", OutputFilename}});

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("after_abi.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after_abi.ll\n";
    }
  }

  emitIterativeSessionReport(iterative_session);
  errs() << "Done.\n";
  events.emitTerminalSuccess(OutputFilename);
  return 0;
}



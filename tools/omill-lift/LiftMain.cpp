#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/PassTimingInfo.h>
#include <llvm/IR/ValueHandle.h>
#include <llvm/IR/Verifier.h>
#include <llvm/AsmParser/Parser.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/StandardInstrumentations.h>
#include <llvm/Linker/Linker.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>
#include <llvm/Transforms/IPO/Inliner.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/DeadStoreElimination.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Analysis/DomTreeUpdater.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Transforms/Utils/CodeExtractor.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/PromoteMemToReg.h>
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
#include "omill/BC/LiftDatabaseIO.h"
#include "omill/BC/RemillProjectionLifter.h"
#include "omill/BC/StaticLiftBuilder.h"
#include "omill/BC/LiftTargetPolicy.h"
#include "omill/BC/TraceLifter.h"
#include "omill/BC/BlockLifter.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/BC/BufferMemoryAdapters.h"
#include "omill/BC/LiftingArtifactFixes.h"
#include "omill/BC/TraceLiftAnalysis.h"
#include <remill/BC/Util.h>
#include <remill/OS/OS.h>

#include "omill/Support/MemoryLimit.h"
#include "omill/Arch/ArchABI.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/TargetArchAnalysis.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Analysis/RemillStateVariableSolver.h"
#include "omill/Analysis/VirtualMachineModel.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/ContinuationResolver.h"
#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/OutputRootClosure.h"
#include "omill/Devirtualization/Runtime.h"
#include "omill/Omill.h"
#include "omill/Remill/Normalization.h"
#include "omill/Passes/JumpTableConcretizer.h"
#include "omill/Passes/InterProceduralConstProp.h"
#include "omill/Passes/CombinedFixedPointDevirt.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/RecoverStackFrame.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Passes/DeadStateStoreDSE.h"
#include "omill/Passes/MergeDecomposedStatePHIs.h"
#include "omill/Passes/SCCDispatchCPT.h"

#include "omill/Passes/ResolveAndLowerControlFlow.h"
#include "omill/Passes/OptimizeState.h"

#include "omill/Support/JumpTableDiscovery.h"
#include "omill/Tools/LiftRunContract.h"
#include "omill/Tools/LiftEventLogger.h"
#include "omill/Utils/LiftedNames.h"

// Bring library-provided event/serializer helpers into unqualified scope.
using omill::tools::LiftEventLogger;
using omill::tools::emitIterativeSessionEvents;
using omill::tools::emitIterativeSessionReport;
using omill::tools::writeRuntimeArtifactReport;
using omill::tools::hexString;
using omill::tools::jsonPcArray;
using omill::tools::jsonSolvedIntegerValue;
using omill::tools::controlTransferKindName;
using omill::tools::emitRuntimeArtifactBundleEvents;
#include "omill/Utils/ProtectedBoundaryUtils.h"
#include "omill/Utils/StateFieldMap.h"
#include "InputLoader.h"
#include "RuntimeAdapters.h"
#include "RecoveryBindings.h"
#include "EnvSupport.h"

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



#include "Options.h"

namespace {

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


int liftMain(int argc, char **argv) {

// Setup: options parsing, binary loading, initial lifting (~950 lines)
#include "LiftMain_setup.inc"

// VM mode: trace emulation, handler discovery (~2220 lines)
#include "LiftMain_vm.inc"

// Devirtualization: planning, compat inputs, pre-ABI prep (~2630 lines)
#include "LiftMain_devirt.inc"

// ABI recovery: signature recovery, output, finalization (~10310 lines)
#include "LiftMain_abi.inc"

}

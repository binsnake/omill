#include "omill/Devirtualization/Runtime.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringSet.h>
#include <llvm/AsmParser/Parser.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/StructuralHash.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <cstring>
#include <map>

#include "omill/Omill.h"
#include "omill/Devirtualization/BinaryRegionReconstructor.h"
#include "omill/Devirtualization/ContinuationResolver.h"
#include "omill/Devirtualization/OutputRootClosure.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

const char *toString(FinalStateRecoveryActionKind kind) {
  switch (kind) {
    case FinalStateRecoveryActionKind::kRetryExecutableChildImport:
      return "retry_executable_child_import";
    case FinalStateRecoveryActionKind::kRetryTerminalExecutableChild:
      return "retry_terminal_executable_child";
    case FinalStateRecoveryActionKind::kRetryNativeBoundaryRecovery:
      return "retry_native_boundary_recovery";
    case FinalStateRecoveryActionKind::kKeepModeledPlaceholder:
      return "keep_modeled_placeholder";
    case FinalStateRecoveryActionKind::kHardReject:
      return "hard_reject";
  }
  return "keep_modeled_placeholder";
}

const char *toString(FinalStateRecoveryDisposition disposition) {
  switch (disposition) {
    case FinalStateRecoveryDisposition::kPlanned:
      return "planned";
    case FinalStateRecoveryDisposition::kSkipped:
      return "skipped";
    case FinalStateRecoveryDisposition::kRetriedNoChange:
      return "retried_no_change";
    case FinalStateRecoveryDisposition::kImported:
      return "imported";
    case FinalStateRecoveryDisposition::kKeptPlaceholder:
      return "kept_placeholder";
    case FinalStateRecoveryDisposition::kHardRejected:
      return "hard_rejected";
  }
  return "skipped";
}

const char *toString(BoundaryTailRecoveryActionKind kind) {
  switch (kind) {
    case BoundaryTailRecoveryActionKind::kLiftBoundaryContinuation:
      return "lift_boundary_continuation";
    case BoundaryTailRecoveryActionKind::kMaterializeTerminalBoundary:
      return "materialize_terminal_boundary";
    case BoundaryTailRecoveryActionKind::kReplayBoundaryAndReclassify:
      return "replay_boundary_and_reclassify";
    case BoundaryTailRecoveryActionKind::kKeepModeledBoundary:
      return "keep_modeled_boundary";
    case BoundaryTailRecoveryActionKind::kHardRejectBoundary:
      return "hard_reject_boundary";
  }
  return "keep_modeled_boundary";
}

const char *toString(BoundaryTailRecoveryDisposition disposition) {
  switch (disposition) {
    case BoundaryTailRecoveryDisposition::kPlanned:
      return "planned";
    case BoundaryTailRecoveryDisposition::kSkipped:
      return "skipped";
    case BoundaryTailRecoveryDisposition::kContinuationLifted:
      return "continuation_lifted";
    case BoundaryTailRecoveryDisposition::kMaterializedTerminalBoundary:
      return "materialized_terminal_boundary";
    case BoundaryTailRecoveryDisposition::kReclassified:
      return "reclassified";
    case BoundaryTailRecoveryDisposition::kKeptModeledBoundary:
      return "kept_modeled_boundary";
    case BoundaryTailRecoveryDisposition::kHardRejected:
      return "hard_rejected";
  }
  return "skipped";
}

const char *toString(FinalTailNodeKind kind) {
  switch (kind) {
    case FinalTailNodeKind::kExecutablePlaceholder:
      return "executable_placeholder";
    case FinalTailNodeKind::kModeledReentryBoundary:
      return "modeled_reentry_boundary";
    case FinalTailNodeKind::kTerminalModeledBoundary:
      return "terminal_modeled_boundary";
    case FinalTailNodeKind::kTerminalModeledChild:
      return "terminal_modeled_child";
    case FinalTailNodeKind::kHardRejectedBoundary:
      return "hard_rejected_boundary";
    case FinalTailNodeKind::kHardRejectedExecutable:
      return "hard_rejected_executable";
    case FinalTailNodeKind::kRetryableBoundary:
      return "retryable_boundary";
  }
  return "executable_placeholder";
}

bool isLoweringHelperCalleeName(llvm::StringRef name) {
  return name == "fetestexcept" || name == "feclearexcept" ||
         name == "feraiseexcept" || name == "fesetround" ||
         name == "fegetround";
}

namespace {

llvm::Function *findBoundaryContinuationFunction(llvm::Module &M,
                                                 uint64_t continuation_pc);

std::string toString(RecoveryRejectionReason reason) {
  switch (reason) {
    case RecoveryRejectionReason::kNone:
      return "none";
    case RecoveryRejectionReason::kChildLiftFailed:
      return "child_lift_failed";
    case RecoveryRejectionReason::kImportFailed:
      return "import_failed";
    case RecoveryRejectionReason::kTypeMismatch:
      return "type_mismatch";
    case RecoveryRejectionReason::kParseFailed:
      return "parse_failed";
    case RecoveryRejectionReason::kMissingRoot:
      return "missing_root";
    case RecoveryRejectionReason::kDisallowedFunction:
      return "disallowed_function";
    case RecoveryRejectionReason::kDeclarationRejected:
      return "declaration_rejected";
    case RecoveryRejectionReason::kGlobalRejected:
      return "global_rejected";
    case RecoveryRejectionReason::kRuntimeLeak:
      return "runtime_leak";
    case RecoveryRejectionReason::kNotSelfContained:
      return "not_self_contained";
    case RecoveryRejectionReason::kUnsupported:
      return "unsupported";
  }
  return "unsupported";
}

std::string toString(ChildArtifactLeakKind leak_kind) {
  switch (leak_kind) {
    case ChildArtifactLeakKind::kNone:
      return "none";
    case ChildArtifactLeakKind::kRemillJump:
      return "remill_jump";
    case ChildArtifactLeakKind::kRemillFunctionCall:
      return "remill_function_call";
    case ChildArtifactLeakKind::kRemillMemoryIntrinsic:
      return "remill_memory_intrinsic";
    case ChildArtifactLeakKind::kExternalCall:
      return "external_call";
  }
  return "none";
}

const char *toString(ImportEligibility eligibility) {
  switch (eligibility) {
    case ImportEligibility::kImportable:
      return "importable";
    case ImportEligibility::kRetryable:
      return "retryable";
    case ImportEligibility::kRejected:
      return "rejected";
  }
  return "rejected";
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

std::optional<uint64_t> parseUniqueClosedRootSliceImportTarget(
    llvm::StringRef model_text) {
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');

  std::optional<uint64_t> selected_root_pc;
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (!trimmed.starts_with("root-slice root=") ||
        !trimmed.contains("closed=true")) {
      continue;
    }

    llvm::StringRef root_text;
    if (auto root_value = parseQuotedAttrValueFromLine(trimmed, "root")) {
      root_text = *root_value;
    } else {
      constexpr llvm::StringLiteral pattern = "root=";
      size_t pos = trimmed.find(pattern);
      if (pos == llvm::StringRef::npos)
        continue;
      pos += pattern.size();
      size_t end = pos;
      while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
        ++end;
      root_text = trimmed.slice(pos, end);
    }

    if (root_text.consume_front("0x"))
      ;
    uint64_t root_pc = 0;
    if (root_text.empty() || root_text.getAsInteger(16, root_pc) || !root_pc)
      continue;

    if (selected_root_pc && *selected_root_pc != root_pc)
      return std::nullopt;
    selected_root_pc = root_pc;
  }

  return selected_root_pc;
}

bool modelTextContainsInvariant(llvm::StringRef model_text,
                                llvm::StringRef invariant_name) {
  if (model_text.empty() || invariant_name.empty())
    return false;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (trimmed.contains("Devirtualization invariant violation:") &&
        trimmed.contains(invariant_name)) {
      return true;
    }
  }
  return false;
}

llvm::SmallVector<std::string, 16> parseClosedRootSliceHandlerNames(
    llvm::StringRef model_text, uint64_t root_pc) {
  llvm::SmallVector<std::string, 16> handler_names;
  llvm::StringSet<> seen_names;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');
  const std::string prefix =
      (llvm::Twine("root-slice root=0x") + llvm::utohexstr(root_pc)).str();
  bool saw_matching_root = false;
  bool in_root_block = false;

  auto add_name = [&](llvm::StringRef name) {
    auto trimmed_name = name.trim();
    if (trimmed_name.empty())
      return;
    if (!seen_names.insert(trimmed_name).second)
      return;
    handler_names.push_back(trimmed_name.str());
  };

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
      if (arrow != llvm::StringRef::npos)
        add_name(trimmed.drop_front(arrow + 2));
      continue;
    }
    if (!in_root_block)
      continue;
    if (trimmed.starts_with("frontier "))
      continue;
    if (trimmed.starts_with("region ") || trimmed.starts_with("root-slice ") ||
        trimmed.starts_with("slot ") || trimmed.starts_with("handler ") ||
        trimmed.empty()) {
      in_root_block = false;
    }
  }
  return handler_names;
}

std::optional<uint64_t> parseSyntheticBlockLikePcFromName(
    llvm::StringRef name) {
  if (auto pc = extractEntryVA(name))
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

llvm::SmallVector<uint64_t, 16> parseLocalizedContinuationCalleePcs(
    llvm::StringRef model_text, uint64_t root_pc) {
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

llvm::SmallVector<uint64_t, 16> parseRootSliceFrontierTargetPcs(
    llvm::StringRef model_text, uint64_t root_pc) {
  llvm::SmallVector<uint64_t, 16> target_pcs;
  llvm::DenseSet<uint64_t> seen_pcs;
  llvm::SmallVector<llvm::StringRef, 128> lines;
  model_text.split(lines, '\n');

  bool in_root_block = false;
  auto add_pc = [&](llvm::StringRef value) {
    if (value.empty())
      return;
    llvm::StringRef hex = value;
    if (hex.consume_front("0x"))
      ;
    uint64_t pc = 0;
    if (hex.getAsInteger(16, pc))
      return;
    if (pc == root_pc)
      return;
    if (seen_pcs.insert(pc).second)
      target_pcs.push_back(pc);
  };

  const std::string prefix =
      (llvm::Twine("root-slice root=0x") + llvm::utohexstr(root_pc)).str();
  for (auto line : lines) {
    auto trimmed = line.trim();
    if (trimmed.starts_with(prefix)) {
      in_root_block = true;
      continue;
    }
    if (!in_root_block)
      continue;
    if (trimmed.starts_with("frontier ")) {
      if (auto target = parseQuotedAttrValueFromLine(trimmed, "target")) {
        add_pc(*target);
        continue;
      }
      constexpr llvm::StringLiteral pattern = "target=";
      size_t pos = trimmed.find(pattern);
      if (pos != llvm::StringRef::npos) {
        pos += pattern.size();
        size_t end = pos;
        while (end < trimmed.size() && !llvm::isSpace(trimmed[end]))
          ++end;
        add_pc(trimmed.slice(pos, end));
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

llvm::Function *findImportedRootByPc(llvm::Module &M, uint64_t pc) {
  if (auto *fn = findStructuralCodeTargetFunctionByPC(M, pc);
      fn && !fn->isDeclaration()) {
    return fn;
  }
  if (auto *fn = findLiftedOrBlockFunctionByPC(M, pc); fn && !fn->isDeclaration())
    return fn;
  return nullptr;
}

bool isTrustedExecutableFact(const ExecutableTargetFact &fact) {
  switch (fact.trust) {
    case ExecutableTargetTrust::kTrustedEntry:
    case ExecutableTargetTrust::kExactFallthrough:
    case ExecutableTargetTrust::kNearbyOwner:
      return true;
    case ExecutableTargetTrust::kInvalidatedEntry:
    case ExecutableTargetTrust::kUntrustedExecutable:
    case ExecutableTargetTrust::kSuppressed:
    case ExecutableTargetTrust::kTerminal:
      return false;
  }
  return false;
}

ChildArtifactLeakKind classifyLeakKind(const ChildLiftArtifact &artifact) {
  if (artifact.has_remill_jump)
    return ChildArtifactLeakKind::kRemillJump;
  if (artifact.has_remill_function_call)
    return ChildArtifactLeakKind::kRemillFunctionCall;
  if (artifact.has_runtime_leak)
    return ChildArtifactLeakKind::kRemillMemoryIntrinsic;
  return ChildArtifactLeakKind::kNone;
}

bool isTerminalModeledArtifact(const ChildLiftArtifact &artifact) {
  return artifact.selected_root_is_terminal_modeled ||
         artifact.selected_root_is_terminal_only ||
         artifact.selected_root_is_self_loop_only;
}

bool isJumpContinuationTailArtifact(const ChildLiftArtifact &artifact) {
  return artifact.has_jump_tail && artifact.has_remill_jump &&
         !artifact.has_remill_function_call;
}

llvm::Value *canonicalizeContinuationStoragePointer(llvm::Value *value) {
  return value ? value->stripPointerCasts() : nullptr;
}

std::optional<uint64_t> constantPcFromValue(llvm::Value *value) {
  if (!value)
    return std::nullopt;
  value = value->stripPointerCasts();
  if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(value))
    return constant->getZExtValue();
  return std::nullopt;
}

bool callUsesContinuationStorage(const llvm::CallBase &call,
                                 llvm::Value *storage) {
  storage = canonicalizeContinuationStoragePointer(storage);
  if (!storage)
    return false;
  for (llvm::Value *arg : call.args()) {
    if (canonicalizeContinuationStoragePointer(arg) == storage)
      return true;
  }
  return false;
}

void analyzeLocalControlledReturn(llvm::Function &selected_root,
                                  ChildLiftArtifact &artifact) {
  llvm::CallBase *jump_call = nullptr;
  for (auto &BB : selected_root) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      auto *callee = call ? call->getCalledFunction() : nullptr;
      if (!callee || callee->getName() != "__remill_jump")
        continue;
      if (jump_call)
        return;
      jump_call = call;
    }
  }
  if (!jump_call)
    return;

  auto *jump_target_load = llvm::dyn_cast<llvm::LoadInst>(
      jump_call->getArgOperand(1)->stripPointerCasts());
  if (!jump_target_load)
    return;

  auto *storage =
      canonicalizeContinuationStoragePointer(jump_target_load->getPointerOperand());
  if (!storage || (!llvm::isa<llvm::AllocaInst>(storage) &&
                   !llvm::isa<llvm::GetElementPtrInst>(storage))) {
    return;
  }

  llvm::SmallDenseSet<uint64_t, 4> constant_values;
  std::optional<uint64_t> last_constant_value;
  bool saw_non_constant_write = false;

  auto record_write = [&](llvm::Value *written_value) {
    if (auto constant_pc = constantPcFromValue(written_value)) {
      constant_values.insert(*constant_pc);
      last_constant_value = *constant_pc;
    } else {
      saw_non_constant_write = true;
      last_constant_value.reset();
    }
  };

  for (auto &BB : selected_root) {
    for (auto &I : BB) {
      if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (canonicalizeContinuationStoragePointer(store->getPointerOperand()) ==
            storage) {
          record_write(store->getValueOperand());
        }
        continue;
      }

      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      auto *callee = call ? call->getCalledFunction() : nullptr;
      if (!call || &I == jump_call || !callUsesContinuationStorage(*call, storage))
        continue;
      if (callee && callee->getName() == "__remill_jump")
        continue;
      if (!call->onlyReadsMemory()) {
        saw_non_constant_write = true;
        last_constant_value.reset();
      }
    }
  }

  const bool saw_constant_rewrite = constant_values.size() > 1;
  if (!saw_non_constant_write && !saw_constant_rewrite)
    return;

  artifact.has_local_controlled_return = true;
  if (!saw_non_constant_write && last_constant_value)
    artifact.local_controlled_return_pc = last_constant_value;
  if (artifact.local_controlled_return_pc && !artifact.jump_tail_continuation_pc)
    artifact.jump_tail_continuation_pc = artifact.local_controlled_return_pc;
}

std::optional<uint64_t> selectJumpTailContinuationPc(
    const ChildLiftArtifact &artifact) {
  if (artifact.jump_tail_continuation_pc)
    return artifact.jump_tail_continuation_pc;

  llvm::SmallDenseSet<uint64_t, 8> candidates;
  auto add_candidate = [&](uint64_t pc) {
    if (!pc || pc == artifact.target_pc)
      return;
    if (artifact.selected_root_pc && *artifact.selected_root_pc == pc)
      return;
    candidates.insert(pc);
  };

  for (uint64_t pc : artifact.localized_continuation_targets)
    add_candidate(pc);
  if (candidates.size() == 1)
    return *candidates.begin();

  candidates.clear();
  for (uint64_t pc : artifact.frontier_target_pcs)
    add_candidate(pc);
  if (candidates.size() == 1)
    return *candidates.begin();

  return std::nullopt;
}

bool isAcceptedExternalLeafCall(llvm::StringRef name) {
  return !name.empty() && !name.starts_with("__remill_") &&
         !name.starts_with("omill_") && !name.starts_with("llvm.") &&
         !isLoweringHelperCalleeName(name) &&
         name != "__omill_missing_block_handler";
}

void appendUniquePc(std::vector<uint64_t> &targets, uint64_t pc) {
  if (!pc)
    return;
  if (llvm::find(targets, pc) == targets.end())
    targets.push_back(pc);
}

std::string moduleToString(const llvm::Module &M) {
  std::string buffer;
  llvm::raw_string_ostream os(buffer);
  M.print(os, nullptr);
  os.flush();
  return buffer;
}

void registerChildPreparationAnalyses(llvm::ModuleAnalysisManager &MAM,
                                      llvm::FunctionAnalysisManager &FAM,
                                      llvm::LoopAnalysisManager &LAM,
                                      llvm::CGSCCAnalysisManager &CGAM) {
  llvm::PassBuilder PB;
  llvm::AAManager AAM;
  registerAAWithManager(AAM);
  FAM.registerPass([&] { return std::move(AAM); });
  PB.registerLoopAnalyses(LAM);
  PB.registerFunctionAnalyses(FAM);
  registerAnalyses(FAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerModuleAnalyses(MAM);
  registerModuleAnalyses(MAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
}

ChildLiftArtifact analyzeChildLiftArtifact(llvm::LLVMContext &llvm_context,
                                           ChildLiftArtifact artifact);

PreparedChildArtifact prepareChildLiftArtifact(llvm::LLVMContext &llvm_context,
                                               const ChildLiftArtifact &raw,
                                               bool no_abi_mode) {
  PreparedChildArtifact prepared;
  prepared.artifact = raw;
  if (!no_abi_mode || raw.ir_text.empty()) {
    prepared.summary.detail = "skipped_preparation";
    return prepared;
  }

  llvm::SMDiagnostic parse_error;
  auto imported_module =
      llvm::parseAssemblyString(raw.ir_text, parse_error, llvm_context);
  if (!imported_module) {
    prepared.summary.detail = "prepare_parse_failed";
    return prepared;
  }

  prepared.summary.parsed = true;
  const auto original_fingerprint = llvm::StructuralHash(*imported_module);

  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;
  registerChildPreparationAnalyses(MAM, FAM, LAM, CGAM);

  {
    llvm::ModulePassManager MPM;
    buildLateClosureCanonicalizationPipeline(MPM);
    MPM.run(*imported_module, MAM);
    prepared.summary.ran_late_closure_canonicalization = true;
  }
  {
    llvm::ModulePassManager MPM;
    buildPostPatchCleanupPipeline(MPM, 80);
    MPM.run(*imported_module, MAM);
    prepared.summary.ran_post_patch_cleanup = true;
  }
  prepared.artifact.ir_text = moduleToString(*imported_module);
  prepared.summary.changed =
      llvm::StructuralHash(*imported_module) != original_fingerprint;
  prepared.summary.detail =
      prepared.summary.changed ? "prepared_child_changed"
                               : "prepared_child_unchanged";
  return prepared;
}

ChildLiftArtifact analyzeChildLiftArtifactForPlanning(
    llvm::LLVMContext &llvm_context, ChildLiftArtifact artifact) {
  if (artifact.ir_text.empty()) {
    if (!artifact.selected_root_pc && artifact.target_pc)
      artifact.selected_root_pc = artifact.target_pc;
    return artifact;
  }
  return analyzeChildLiftArtifact(llvm_context, std::move(artifact));
}

ChildLiftArtifact analyzeChildLiftArtifact(llvm::LLVMContext &llvm_context,
                                           ChildLiftArtifact artifact) {
  const auto closed_slice_root_pc =
      parseUniqueClosedRootSliceImportTarget(artifact.model_text);
  if (!artifact.selected_root_pc)
    artifact.selected_root_pc = closed_slice_root_pc;
  artifact.has_unresolved_dispatch_intrinsics =
      modelTextContainsInvariant(artifact.model_text,
                                 "unresolved_dispatch_intrinsics");

  llvm::SMDiagnostic parse_error;
  auto imported_module =
      llvm::parseAssemblyString(artifact.ir_text, parse_error, llvm_context);
  if (!imported_module) {
    artifact.rejection_reason = RecoveryRejectionReason::kParseFailed;
    artifact.rejection_detail = "ir_parse_failed";
    artifact.import_safety = ChildImportClass::kUnsupported;
    return artifact;
  }

  const uint64_t selected_root_pc =
      artifact.selected_root_pc.value_or(artifact.target_pc);
  auto *selected_root = findImportedRootByPc(*imported_module, selected_root_pc);
  if (!selected_root) {
    artifact.rejection_reason = RecoveryRejectionReason::kMissingRoot;
    artifact.rejection_detail = "selected_root_missing";
    artifact.import_safety = ChildImportClass::kUnsupported;
    return artifact;
  }

  artifact.selected_root_pc = selected_root_pc;
  artifact.selected_root_name = selected_root->getName().str();
  artifact.selected_root_kind = selected_root->getName().starts_with("blk_")
                                    ? "block"
                                    : (selected_root->getName().starts_with("sub_")
                                           ? "lifted"
                                           : "structural");
  for (const auto &name :
       parseClosedRootSliceHandlerNames(artifact.model_text, selected_root_pc)) {
    artifact.closed_slice_function_names.push_back(name);
  }
  for (uint64_t pc :
       parseLocalizedContinuationCalleePcs(artifact.model_text, selected_root_pc)) {
    appendUniquePc(artifact.localized_continuation_targets, pc);
  }
  for (uint64_t pc :
       parseRootSliceFrontierTargetPcs(artifact.model_text, selected_root_pc)) {
    appendUniquePc(artifact.frontier_target_pcs, pc);
  }
  if (auto fact = readExecutableTargetFact(*selected_root))
    artifact.selected_root_is_trusted_entry = isTrustedExecutableFact(*fact);

  bool saw_non_intrinsic_call = false;
  bool saw_return = false;
  for (auto &BB : *selected_root) {
    if (auto *BI = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
        BI && BI->isUnconditional() && BI->getSuccessor(0) == &BB) {
      artifact.selected_root_has_structural_loop = true;
    }
    for (auto &I : BB) {
      if (llvm::isa<llvm::ReturnInst>(&I))
        saw_return = true;
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      auto *callee = CB ? CB->getCalledFunction() : nullptr;
      if (!callee)
        continue;
      if (callee->getName() == "__remill_jump")
        artifact.has_remill_jump = true;
      if (callee->getName() == "__remill_function_call")
        artifact.has_remill_function_call = true;
      if (callee->getName().starts_with("__remill_read_memory_") ||
          callee->getName().starts_with("__remill_write_memory_")) {
        artifact.has_runtime_leak = true;
      }
      if (!callee->isIntrinsic() && callee->isDeclaration() &&
          callee->getName().starts_with("__remill_")) {
        artifact.has_runtime_leak = true;
      }
      if (!callee->isIntrinsic() && !callee->getName().starts_with("__remill_"))
        saw_non_intrinsic_call = true;
    }
  }

  auto isStructuralImportedFunction = [&](llvm::StringRef name) {
    return name.starts_with("sub_") || name.starts_with("blk_") ||
           name.starts_with("block_") || name.starts_with("__lifted_");
  };
  llvm::StringSet<> allowed_slice_names;
  for (const auto &name : artifact.closed_slice_function_names)
    allowed_slice_names.insert(name);

  llvm::SmallVector<llvm::Function *, 16> closure_worklist;
  llvm::SmallPtrSet<llvm::Function *, 16> closure_visited;
  llvm::StringSet<> seen_decl_callees;
  closure_worklist.push_back(selected_root);
  while (!closure_worklist.empty()) {
    auto *F = closure_worklist.pop_back_val();
    if (!F || F->isDeclaration() || !closure_visited.insert(F).second)
      continue;
    if (!allowed_slice_names.empty() &&
        isStructuralImportedFunction(F->getName()) &&
        !allowed_slice_names.count(F->getName())) {
      artifact.rejection_reason = RecoveryRejectionReason::kDisallowedFunction;
      artifact.rejection_detail = "disallowed_slice_function";
      artifact.import_safety = ChildImportClass::kUnsupported;
      return artifact;
    }
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        auto *callee = CB ? CB->getCalledFunction() : nullptr;
        if (!callee)
          continue;
        if (callee->isDeclaration()) {
          if (!callee->isIntrinsic() &&
              !callee->getName().starts_with("llvm.")) {
            if (isLoweringHelperCalleeName(callee->getName())) {
              if (seen_decl_callees.insert(callee->getName()).second)
                artifact.lowering_helper_callees.push_back(
                    callee->getName().str());
            } else if (seen_decl_callees.insert(callee->getName()).second) {
              artifact.reachable_declaration_callees.push_back(
                  callee->getName().str());
            }
          }
          if (callee->getName() == "__remill_jump")
            artifact.has_remill_jump = true;
          if (callee->getName() == "__remill_function_call")
            artifact.has_remill_function_call = true;
          if (callee->getName().starts_with("__remill_read_memory_") ||
              callee->getName().starts_with("__remill_write_memory_")) {
            artifact.has_runtime_leak = true;
          }
          if (!callee->isIntrinsic() &&
              callee->getName().starts_with("__remill_")) {
            artifact.has_runtime_leak = true;
          }
          continue;
        }
        closure_worklist.push_back(callee);
      }
    }
  }

  for (auto &F : *imported_module) {
    if (!F.isDeclaration())
      continue;
    const uint64_t target_pc = extractStructuralCodeTargetPC(F);
    if (!target_pc)
      continue;
    if (F.getName().starts_with("omill_executable_target_")) {
      appendUniquePc(artifact.modeled_executable_targets, target_pc);
      continue;
    }
    if (F.getName().starts_with("omill_native_target_") ||
        F.getName().starts_with("omill_native_boundary_") ||
        F.getName().starts_with("omill_vm_enter_target_") ||
        F.getName().starts_with("omill_vm_enter_boundary_")) {
      appendUniquePc(artifact.modeled_boundary_targets, target_pc);
    }
  }

  artifact.selected_root_is_terminal_only =
      saw_return && !saw_non_intrinsic_call &&
      !artifact.selected_root_has_structural_loop;
  artifact.selected_root_is_self_loop_only =
      !saw_return && !saw_non_intrinsic_call &&
      artifact.selected_root_has_structural_loop &&
      !artifact.has_remill_jump && !artifact.has_remill_function_call &&
      !artifact.has_runtime_leak;
  artifact.selected_root_is_terminal_modeled =
      artifact.selected_root_is_terminal_only ||
      artifact.selected_root_is_self_loop_only;
  artifact.has_jump_tail =
      artifact.has_remill_jump && !artifact.has_remill_function_call &&
      !artifact.selected_root_is_self_loop_only;
  if (artifact.has_jump_tail)
    analyzeLocalControlledReturn(*selected_root, artifact);
  artifact.has_pc_relative_return_thunk =
      artifact.has_jump_tail && artifact.has_local_controlled_return;
  artifact.jump_tail_continuation_pc = selectJumpTailContinuationPc(artifact);

  const auto leak_kind = classifyLeakKind(artifact);
  if (leak_kind != ChildArtifactLeakKind::kNone) {
    artifact.import_safety = ChildImportClass::kRuntimeLeakingChild;
    artifact.rejection_reason = RecoveryRejectionReason::kRuntimeLeak;
    artifact.rejection_detail = toString(leak_kind);
  } else if (!artifact.modeled_boundary_targets.empty()) {
    artifact.import_safety = ChildImportClass::kBoundaryModeledChild;
    artifact.rejection_reason = RecoveryRejectionReason::kNone;
    artifact.rejection_detail.clear();
  } else if (artifact.selected_root_is_trusted_entry &&
             artifact.selected_root_is_terminal_only) {
    artifact.import_safety = ChildImportClass::kTrustedTerminalEntry;
    artifact.rejection_reason = RecoveryRejectionReason::kNone;
    artifact.rejection_detail.clear();
  } else if (closed_slice_root_pc) {
    artifact.import_safety = ChildImportClass::kClosedSliceRoot;
    artifact.rejection_reason = RecoveryRejectionReason::kNone;
    artifact.rejection_detail.clear();
  } else if (artifact.selected_root_is_terminal_modeled) {
    artifact.import_safety = ChildImportClass::kTerminalOnlyUnknown;
    artifact.rejection_reason = RecoveryRejectionReason::kNotSelfContained;
    artifact.rejection_detail = artifact.selected_root_is_self_loop_only
                                    ? "terminal_modeled_child"
                                    : "terminal_only_child";
  } else {
    artifact.import_safety = ChildImportClass::kUnsupported;
    artifact.rejection_reason = RecoveryRejectionReason::kUnsupported;
    artifact.rejection_detail = "unsupported_child_shape";
  }
  return artifact;
}

std::string describeVmEnterChildImportBlocker(
    const ChildLiftArtifact &artifact) {
  llvm::SmallVector<std::string, 4> parts;
  const auto leak_kind = classifyLeakKind(artifact);
  if (leak_kind != ChildArtifactLeakKind::kNone) {
    parts.push_back(std::string("runtime_leak:") + toString(leak_kind));
  }
  if (artifact.has_unresolved_dispatch_intrinsics) {
    parts.push_back("unresolved_dispatch_intrinsics");
  }
  if (!artifact.modeled_executable_targets.empty()) {
    parts.push_back("modeled_executable_tail");
  }
  if (artifact.has_jump_tail) {
    parts.push_back(artifact.jump_tail_continuation_pc
                        ? "jump_tail_with_continuation"
                        : "jump_tail");
  }
  if (!artifact.rejection_detail.empty()) {
    const bool already_present = llvm::any_of(parts, [&](const std::string &part) {
      const std::string suffix = ":" + artifact.rejection_detail;
      return part == artifact.rejection_detail ||
             llvm::StringRef(part).ends_with(suffix);
    });
    if (!already_present)
      parts.push_back(artifact.rejection_detail);
  }
  if (parts.empty())
    return toString(artifact.rejection_reason);

  std::string detail;
  llvm::raw_string_ostream os(detail);
  for (size_t i = 0; i < parts.size(); ++i) {
    if (i)
      os << "+";
    os << parts[i];
  }
  return detail;
}

ChildImportPlan buildVmEnterChildImportPlan(const ChildLiftArtifact &artifact) {
  ChildImportPlan plan;
  plan.target_pc = artifact.target_pc;
  plan.selected_root_pc = artifact.selected_root_pc;
  plan.import_class = artifact.import_safety;
  plan.allowed_declaration_callees = artifact.reachable_declaration_callees;
  plan.lowering_helper_callees = artifact.lowering_helper_callees;

  const auto leak_kind = classifyLeakKind(artifact);
  const bool has_retryable_tail =
      artifact.has_unresolved_dispatch_intrinsics ||
      !artifact.modeled_executable_targets.empty() || artifact.has_jump_tail;

  if (leak_kind != ChildArtifactLeakKind::kNone) {
    plan.eligibility = ImportEligibility::kRejected;
    plan.rejection_reason = RecoveryRejectionReason::kRuntimeLeak;
    plan.rejection_detail = describeVmEnterChildImportBlocker(artifact);
    return plan;
  }

  if (has_retryable_tail) {
    plan.eligibility = ImportEligibility::kRetryable;
    plan.rejection_reason =
        artifact.has_unresolved_dispatch_intrinsics
            ? RecoveryRejectionReason::kUnsupported
            : artifact.rejection_reason;
    if (plan.rejection_reason == RecoveryRejectionReason::kNone)
      plan.rejection_reason = RecoveryRejectionReason::kUnsupported;
    plan.rejection_detail = describeVmEnterChildImportBlocker(artifact);
    return plan;
  }

  if (artifact.import_safety == ChildImportClass::kTrustedTerminalEntry ||
      artifact.import_safety == ChildImportClass::kBoundaryModeledChild ||
      (artifact.import_safety == ChildImportClass::kClosedSliceRoot &&
       artifact.selected_root_is_terminal_modeled)) {
    plan.eligibility = ImportEligibility::kImportable;
    plan.rejection_reason = RecoveryRejectionReason::kNone;
    return plan;
  }

  if (artifact.selected_root_is_terminal_modeled ||
      artifact.import_safety == ChildImportClass::kTerminalOnlyUnknown) {
    plan.eligibility = ImportEligibility::kRejected;
    plan.rejection_reason = RecoveryRejectionReason::kNotSelfContained;
    plan.rejection_detail = artifact.rejection_detail.empty()
                                ? "terminal_modeled_vm_enter_child"
                                : artifact.rejection_detail;
    return plan;
  }

  plan.eligibility = ImportEligibility::kRejected;
  plan.rejection_reason = artifact.rejection_reason;
  if (plan.rejection_reason == RecoveryRejectionReason::kNone)
    plan.rejection_reason = RecoveryRejectionReason::kUnsupported;
  plan.rejection_detail = describeVmEnterChildImportBlocker(artifact);
  return plan;
}

std::optional<ContinuationProof> findContinuationProofForTarget(
    const DevirtualizationOrchestrator &orchestrator, uint64_t target_pc) {
  const auto &session = orchestrator.session();
  const SessionEdgeFact *best_edge = nullptr;
  for (const auto &[identity, edge] : session.graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc || *edge.target_pc != target_pc)
      continue;
    if (!best_edge ||
        edge.scheduling_class < best_edge->scheduling_class ||
        edge.continuation_confidence > best_edge->continuation_confidence) {
      best_edge = &edge;
    }
    if (edge.continuation_proof &&
        edge.continuation_proof->import_disposition ==
            ContinuationImportDisposition::kImportable) {
      return edge.continuation_proof;
    }
  }
  if (best_edge && best_edge->continuation_proof)
    return best_edge->continuation_proof;
  return std::nullopt;
}

std::map<uint64_t, std::vector<LearnedOutgoingEdge>> collectLearnedOutgoingEdges(
    const IterativeLiftingSession *iterative_session, uint64_t target_pc,
    const std::optional<ContinuationProof> &proof) {
  std::map<uint64_t, std::vector<LearnedOutgoingEdge>> learned;
  if (!iterative_session)
    return learned;

  for (const auto *edge : iterative_session->graph().outgoingEdges(target_pc)) {
    if (edge->learned_outgoing_edges.empty())
      continue;
    auto &bucket = learned[edge->source_pc];
    bucket.insert(bucket.end(), edge->learned_outgoing_edges.begin(),
                  edge->learned_outgoing_edges.end());
  }

  if (proof && proof->binary_region_snapshot_key) {
    if (const auto *snapshot =
            iterative_session->lookupBinaryRegionSnapshot(
                *proof->binary_region_snapshot_key)) {
      for (const auto &[block_pc, block] : snapshot->blocks_by_pc) {
        learned[block_pc] = block.outgoing_edges;
      }
    }
  }

  return learned;
}

void mergeResolvedProofIntoSession(DevirtualizationOrchestrator &orchestrator,
                                   uint64_t target_pc,
                                   const ContinuationProof &proof) {
  for (auto &[identity, edge] :
       orchestrator.session().graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc || *edge.target_pc != target_pc)
      continue;
    edge.continuation_proof = proof;
    edge.continuation_confidence = proof.confidence;
    edge.continuation_liveness = proof.liveness;
    edge.scheduling_class = proof.scheduling_class;
    if (!proof.rationale.empty())
      edge.continuation_rationale = proof.rationale;
  }
}

ChildImportPlan planExecutableChildImport(
    uint64_t target_pc, const ChildLiftArtifact &artifact,
    const std::optional<ContinuationProof> &proof,
    const std::optional<ContinuationResolutionResult> &resolution) {
  ChildImportPlan plan;
  plan.target_pc = target_pc;
  plan.selected_root_pc = artifact.selected_root_pc;
  plan.import_class = artifact.import_safety;
  plan.proof = proof;
  plan.lowering_helper_callees = artifact.lowering_helper_callees;

  if (artifact.rejection_reason == RecoveryRejectionReason::kParseFailed ||
      artifact.rejection_reason == RecoveryRejectionReason::kMissingRoot) {
    plan.eligibility = ImportEligibility::kRejected;
    plan.rejection_reason = artifact.rejection_reason;
    plan.rejection_detail = artifact.rejection_detail;
    return plan;
  }

  if (artifact.import_safety == ChildImportClass::kRuntimeLeakingChild) {
    plan.eligibility = ImportEligibility::kRejected;
    plan.rejection_reason = RecoveryRejectionReason::kRuntimeLeak;
    plan.rejection_detail = artifact.rejection_detail;
    return plan;
  }

  if (resolution &&
      resolution->disposition ==
          ContinuationResolutionDisposition::kDeferredQuarantinedSelectorArm) {
    plan.eligibility = ImportEligibility::kRetryable;
    plan.rejection_reason = RecoveryRejectionReason::kUnsupported;
    plan.rejection_detail = "quarantined_selector_arm";
    return plan;
  }

  if (resolution &&
      (resolution->disposition ==
           ContinuationResolutionDisposition::kImportableTrustedEntry ||
       resolution->disposition ==
           ContinuationResolutionDisposition::kImportableClosedSliceRoot ||
       resolution->disposition ==
           ContinuationResolutionDisposition::kBoundaryModeledChild)) {
    plan.eligibility = ImportEligibility::kImportable;
    plan.rejection_reason = RecoveryRejectionReason::kNone;
    if (resolution->updated_proof.selected_root_import_class)
      plan.import_class = *resolution->updated_proof.selected_root_import_class;
    plan.allowed_declaration_callees = artifact.reachable_declaration_callees;
    plan.lowering_helper_callees = artifact.lowering_helper_callees;
    return plan;
  }

  if (artifact.import_safety == ChildImportClass::kTrustedTerminalEntry ||
      artifact.import_safety == ChildImportClass::kClosedSliceRoot ||
      artifact.import_safety == ChildImportClass::kBoundaryModeledChild) {
    plan.eligibility = ImportEligibility::kImportable;
    plan.rejection_reason = RecoveryRejectionReason::kNone;
    plan.allowed_declaration_callees = artifact.reachable_declaration_callees;
    plan.lowering_helper_callees = artifact.lowering_helper_callees;
    return plan;
  }

  if (resolution &&
      resolution->disposition ==
          ContinuationResolutionDisposition::kRetryableOpenRegion) {
    plan.eligibility = ImportEligibility::kRetryable;
    plan.rejection_reason = RecoveryRejectionReason::kNotSelfContained;
    plan.rejection_detail = artifact.rejection_detail.empty()
                                ? "resolver_retryable_open_region"
                                : artifact.rejection_detail;
    return plan;
  }

  plan.eligibility = ImportEligibility::kRejected;
  plan.rejection_reason = artifact.rejection_reason;
  plan.rejection_detail = artifact.rejection_detail.empty()
                              ? "terminal_only_child"
                              : artifact.rejection_detail;
  return plan;
}

enum class ChildRootSelectionMode {
  kExecutable,
  kVmEnter,
};

struct ChildRootCandidate {
  uint64_t pc = 0;
  const char *source = "";
};

struct ChildRootSelectionResult {
  ChildLiftArtifact artifact;
  ChildImportPlan plan;
  bool changed = false;
};

struct ChildVariantSelectionResult {
  ChildLiftArtifact artifact;
  ChildImportPlan plan;
  bool used_prepared_variant = false;
};

unsigned childImportPlanPreferenceRank(const ChildImportPlan &plan) {
  switch (plan.eligibility) {
    case ImportEligibility::kImportable:
      return 0;
    case ImportEligibility::kRetryable:
      return 1;
    case ImportEligibility::kRejected:
      break;
  }

  switch (plan.rejection_reason) {
    case RecoveryRejectionReason::kNotSelfContained:
      return 2;
    case RecoveryRejectionReason::kDisallowedFunction:
      return 3;
    case RecoveryRejectionReason::kUnsupported:
      return 4;
    case RecoveryRejectionReason::kRuntimeLeak:
      return 5;
    case RecoveryRejectionReason::kDeclarationRejected:
    case RecoveryRejectionReason::kGlobalRejected:
      return 6;
    case RecoveryRejectionReason::kImportFailed:
    case RecoveryRejectionReason::kTypeMismatch:
      return 7;
    case RecoveryRejectionReason::kChildLiftFailed:
    case RecoveryRejectionReason::kParseFailed:
    case RecoveryRejectionReason::kMissingRoot:
      return 8;
    case RecoveryRejectionReason::kNone:
      return 9;
  }
  return 9;
}

ChildImportPlan buildChildImportPlanForMode(
    ChildRootSelectionMode mode, uint64_t target_pc,
    const ChildLiftArtifact &artifact,
    const std::optional<ContinuationProof> &proof,
    const std::optional<ContinuationResolutionResult> &resolution) {
  switch (mode) {
    case ChildRootSelectionMode::kExecutable:
      return planExecutableChildImport(target_pc, artifact, proof, resolution);
    case ChildRootSelectionMode::kVmEnter:
      return buildVmEnterChildImportPlan(artifact);
  }
  return buildVmEnterChildImportPlan(artifact);
}

llvm::SmallVector<ChildRootCandidate, 8> collectPreparedChildRootCandidates(
    const ChildLiftArtifact &artifact) {
  llvm::SmallVector<ChildRootCandidate, 8> candidates;
  llvm::SmallDenseSet<uint64_t, 8> seen;
  auto add_candidate = [&](uint64_t pc, const char *source) {
    if (!pc || pc == artifact.target_pc)
      return;
    if (artifact.selected_root_pc && *artifact.selected_root_pc == pc)
      return;
    if (!seen.insert(pc).second)
      return;
    candidates.push_back({pc, source});
  };

  for (uint64_t pc : artifact.localized_continuation_targets)
    add_candidate(pc, "localized_continuation");
  for (uint64_t pc : artifact.frontier_target_pcs)
    add_candidate(pc, "frontier_target");
  for (const auto &name : artifact.closed_slice_function_names) {
    if (auto pc = parseSyntheticBlockLikePcFromName(name))
      add_candidate(*pc, "closed_slice_handler");
  }
  return candidates;
}

ChildRootSelectionResult selectPreparedChildImportRoot(
    llvm::LLVMContext &llvm_context, const ChildLiftArtifact &artifact,
    ChildRootSelectionMode mode,
    const std::optional<ContinuationProof> &proof = std::nullopt,
    const std::optional<ContinuationResolutionResult> &resolution =
        std::nullopt) {
  ChildRootSelectionResult best;
  best.artifact = artifact;
  best.plan = buildChildImportPlanForMode(mode, artifact.target_pc, artifact,
                                          proof, resolution);

  const auto candidates = collectPreparedChildRootCandidates(artifact);
  for (const auto &candidate : candidates) {
    ChildLiftArtifact candidate_artifact = artifact;
    const auto original_root_pc = artifact.selected_root_pc;
    candidate_artifact.selected_root_pc = candidate.pc;
    candidate_artifact.selected_root_was_retargeted = true;
    candidate_artifact.selected_root_selection_detail =
        (llvm::Twine("retargeted_from=") +
         (original_root_pc ? llvm::Twine("0x") + llvm::utohexstr(*original_root_pc)
                           : llvm::Twine("none")) +
         ",source=" + candidate.source + ",to=0x" +
         llvm::utohexstr(candidate.pc))
            .str();
    candidate_artifact =
        analyzeChildLiftArtifact(llvm_context, std::move(candidate_artifact));
    auto candidate_plan = buildChildImportPlanForMode(
        mode, artifact.target_pc, candidate_artifact, proof, resolution);

    const auto candidate_rank = childImportPlanPreferenceRank(candidate_plan);
    const auto best_rank = childImportPlanPreferenceRank(best.plan);
    const bool better =
        candidate_rank < best_rank ||
        (candidate_rank == best_rank &&
         candidate_plan.eligibility == ImportEligibility::kImportable &&
         candidate_artifact.selected_root_is_terminal_modeled !=
             best.artifact.selected_root_is_terminal_modeled &&
         candidate_artifact.selected_root_is_terminal_modeled) ||
        (candidate_rank == best_rank &&
         candidate_plan.eligibility == ImportEligibility::kImportable &&
         candidate_artifact.selected_root_pc &&
         best.artifact.selected_root_pc &&
         *candidate_artifact.selected_root_pc < *best.artifact.selected_root_pc);
    if (!better)
      continue;

    best.artifact = std::move(candidate_artifact);
    best.plan = std::move(candidate_plan);
    best.changed = true;
  }

  if (!best.changed) {
    best.artifact.selected_root_was_retargeted = false;
    if (best.artifact.selected_root_selection_detail.empty())
      best.artifact.selected_root_selection_detail = "selected_root_unchanged";
  }
  return best;
}

ChildVariantSelectionResult selectBestChildImportArtifact(
    llvm::LLVMContext &llvm_context, const ChildLiftArtifact &raw_artifact,
    const ChildLiftArtifact &prepared_artifact, ChildRootSelectionMode mode,
    const std::optional<ContinuationProof> &proof = std::nullopt,
    const std::optional<ContinuationResolutionResult> &resolution =
        std::nullopt) {
  auto raw_selection = selectPreparedChildImportRoot(
      llvm_context, raw_artifact, mode, proof, resolution);
  auto prepared_selection = selectPreparedChildImportRoot(
      llvm_context, prepared_artifact, mode, proof, resolution);

  const auto raw_rank = childImportPlanPreferenceRank(raw_selection.plan);
  const auto prepared_rank =
      childImportPlanPreferenceRank(prepared_selection.plan);

  ChildVariantSelectionResult best;
  const bool prepared_only_collapsed_same_root =
      mode == ChildRootSelectionMode::kVmEnter &&
      raw_selection.artifact.selected_root_pc &&
      prepared_selection.artifact.selected_root_pc &&
      raw_selection.artifact.selected_root_pc ==
          prepared_selection.artifact.selected_root_pc &&
      raw_selection.plan.eligibility != ImportEligibility::kImportable &&
      prepared_selection.plan.eligibility == ImportEligibility::kImportable &&
      !raw_selection.artifact.selected_root_was_retargeted &&
      !prepared_selection.artifact.selected_root_was_retargeted &&
      !raw_selection.artifact.selected_root_is_terminal_modeled &&
      prepared_selection.artifact.selected_root_is_terminal_modeled;
  const bool raw_better =
      raw_rank < prepared_rank || prepared_only_collapsed_same_root ||
      (raw_rank == prepared_rank &&
       raw_selection.plan.eligibility == ImportEligibility::kImportable &&
       raw_selection.artifact.selected_root_is_terminal_modeled !=
           prepared_selection.artifact.selected_root_is_terminal_modeled &&
       raw_selection.artifact.selected_root_is_terminal_modeled) ||
      (raw_rank == prepared_rank &&
       raw_selection.artifact.selected_root_was_retargeted !=
           prepared_selection.artifact.selected_root_was_retargeted &&
       raw_selection.artifact.selected_root_was_retargeted);

  if (raw_better) {
    best.artifact = std::move(raw_selection.artifact);
    best.plan = std::move(raw_selection.plan);
    best.used_prepared_variant = false;
    if (best.artifact.selected_root_selection_detail.empty()) {
      best.artifact.selected_root_selection_detail =
          "selected_raw_child_variant";
    } else {
      best.artifact.selected_root_selection_detail +=
          ",variant=selected_raw_child_variant";
    }
    if (prepared_only_collapsed_same_root) {
      best.plan.eligibility = ImportEligibility::kRejected;
      best.plan.rejection_reason = RecoveryRejectionReason::kNotSelfContained;
      best.plan.rejection_detail = "terminal_modeled_vm_enter_child";
      best.artifact.selected_root_selection_detail +=
          ",guarded_against_prepared_same_root_collapse";
    }
    return best;
  }

  best.artifact = std::move(prepared_selection.artifact);
  best.plan = std::move(prepared_selection.plan);
  best.used_prepared_variant = true;
  if (best.artifact.selected_root_selection_detail.empty()) {
    best.artifact.selected_root_selection_detail =
        "selected_prepared_child_variant";
  } else {
    best.artifact.selected_root_selection_detail +=
        ",variant=selected_prepared_child_variant";
  }
  return best;
}

ChildVariantSelectionResult selectCachedChildImportArtifact(
    llvm::LLVMContext &llvm_context, const ChildArtifactCacheEntry &entry,
    ChildRootSelectionMode mode,
    const std::optional<ContinuationProof> &proof = std::nullopt,
    const std::optional<ContinuationResolutionResult> &resolution =
        std::nullopt) {
  if (entry.raw_artifact.ir_text.empty()) {
    auto prepared_selection = selectPreparedChildImportRoot(
        llvm_context, entry.artifact, mode, proof, resolution);
    ChildVariantSelectionResult result;
    result.artifact = std::move(prepared_selection.artifact);
    result.plan = std::move(prepared_selection.plan);
    result.used_prepared_variant = true;
    if (result.artifact.selected_root_selection_detail.empty()) {
      result.artifact.selected_root_selection_detail =
          "selected_prepared_child_variant";
    } else {
      result.artifact.selected_root_selection_detail +=
          ",variant=selected_prepared_child_variant";
    }
    return result;
  }

  return selectBestChildImportArtifact(llvm_context, entry.raw_artifact,
                                       entry.artifact, mode, proof,
                                       resolution);
}

std::string summarizeProof(const std::optional<ContinuationProof> &proof) {
  if (!proof)
    return "proof=none";
  return "proof=" + std::string(toString(proof->resolution_kind)) +
         ",import=" + std::string(toString(proof->import_disposition)) +
         ",confidence=" + std::string(toString(proof->confidence)) +
         ",liveness=" + std::string(toString(proof->liveness));
}

bool hasMeaningfulProof(const std::optional<ContinuationProof> &proof) {
  if (!proof)
    return false;
  return proof->raw_target_pc || proof->effective_target_pc.has_value() ||
         proof->canonical_owner_pc.has_value() || !proof->edge_identity.empty() ||
         !proof->source_handler_name.empty() ||
         proof->resolution_kind != ContinuationResolutionKind::kUnknown ||
         proof->import_disposition != ContinuationImportDisposition::kUnknown ||
         proof->is_trusted_entry || proof->is_exact_fallthrough ||
         proof->is_invalidated_entry ||
         proof->invalidated_entry_source_pc.has_value() ||
         proof->invalidated_entry_failed_pc.has_value() ||
         proof->selected_root_pc.has_value() ||
         proof->selected_root_import_class.has_value() ||
         proof->binary_region_snapshot_key.has_value() ||
         !proof->resolution_detail.empty() || !proof->rationale.empty();
}

std::string summarizeResolution(
    const std::optional<ContinuationResolutionResult> &resolution) {
  if (!resolution)
    return "resolution=none";
  return "resolver=" +
         std::string(toString(resolution->disposition)) + ",region=" +
         std::string(toString(resolution->region_snapshot.closure_kind)) +
         ",blocks=" +
         std::to_string(resolution->region_snapshot.blocks_by_pc.size());
}

ImportDecisionArtifact makeImportDecisionArtifact(
    llvm::StringRef label, const ChildImportPlan &plan,
    const std::optional<ContinuationProof> &proof,
    const std::optional<ContinuationResolutionResult> &resolution,
    bool imported = false) {
  ImportDecisionArtifact artifact;
  artifact.label = label.str();
  artifact.target_pc = plan.target_pc;
  artifact.eligibility = plan.eligibility;
  artifact.rejection_reason = plan.rejection_reason;
  artifact.selected_root_pc = plan.selected_root_pc;
  artifact.import_class = plan.import_class;
  artifact.proof_summary = summarizeProof(proof);
  artifact.resolution_summary = summarizeResolution(resolution);
  artifact.detail = plan.rejection_detail;
  artifact.imported = imported;
  return artifact;
}

void populateRecoveryQualitySummary(
    RoundArtifactBundle &bundle,
    const std::map<ChildArtifactCacheKey, ChildArtifactCacheEntry> &cache,
    llvm::ArrayRef<RoundArtifactBundle> prior_bundles) {
  llvm::SmallDenseSet<uint64_t, 16> classified_targets;
  for (const auto &action : bundle.planned_recovery_actions)
    classified_targets.insert(action.target_pc);
  for (const auto &action : bundle.executed_recovery_actions) {
    classified_targets.insert(action.target_pc);
    if (action.disposition == FinalStateRecoveryDisposition::kHardRejected) {
      appendUniquePc(bundle.recovery_quality.hard_rejected_targets,
                     action.target_pc);
    }
  }
  for (const auto &rejected : bundle.rejected_imports) {
    if (rejected.reason == RecoveryRejectionReason::kRuntimeLeak ||
        rejected.reason == RecoveryRejectionReason::kUnsupported) {
      appendUniquePc(bundle.recovery_quality.hard_rejected_targets,
                     rejected.target_pc);
    }
  }
  for (const auto &decision : bundle.import_decisions) {
    if (decision.rejection_reason == RecoveryRejectionReason::kRuntimeLeak) {
      appendUniquePc(bundle.recovery_quality.hard_rejected_targets,
                     decision.target_pc);
    }
  }

  llvm::SmallDenseSet<uint64_t, 16> imported_targets;
  for (const auto &prior_bundle : prior_bundles) {
    for (uint64_t target_pc : prior_bundle.imported_targets)
      imported_targets.insert(target_pc);
  }
  for (uint64_t target_pc : bundle.imported_targets)
    imported_targets.insert(target_pc);

  for (const auto &callee : bundle.lowering_helper_callees) {
    if (llvm::find(bundle.recovery_quality.lowering_helper_callees, callee) ==
        bundle.recovery_quality.lowering_helper_callees.end()) {
      bundle.recovery_quality.lowering_helper_callees.push_back(callee);
    }
  }

  for (uint64_t target_pc : imported_targets) {
    for (const auto &[key, entry] : cache) {
      if (key.target_pc != target_pc || !entry.imported)
        continue;
      if (isTerminalModeledArtifact(entry.artifact)) {
        appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                       target_pc);
        appendUniquePc(bundle.recovery_quality.terminal_modeled_children,
                       target_pc);
      }
    }
  }

  for (const auto &action : bundle.planned_recovery_actions) {
    if (action.reason == "modeled_reentry_boundary") {
      appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                     action.target_pc);
    } else if (action.reason == "modeled_terminal_boundary") {
      appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.terminal_modeled_boundaries,
                     action.target_pc);
    } else if (action.reason == "terminal_modeled_child") {
      appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.terminal_modeled_children,
                     action.target_pc);
    }
  }
  for (const auto &action : bundle.boundary_recovery_results) {
    classified_targets.insert(action.target_pc);
    switch (action.disposition) {
      case BoundaryTailRecoveryDisposition::kContinuationLifted:
        if (action.continuation_pc)
          appendUniquePc(bundle.recovery_quality.lifted_boundary_continuations,
                         *action.continuation_pc);
        if (action.detail == "controlled_return_continuation_lifted" &&
            action.continuation_pc) {
          appendUniquePc(
              bundle.recovery_quality.lifted_controlled_return_continuations,
              *action.continuation_pc);
          appendUniquePc(bundle.recovery_quality.modeled_pc_relative_return_thunks,
                         action.target_pc);
        }
        if (action.detail == "intra_owner_continuation_lifted") {
          appendUniquePc(bundle.recovery_quality.lifted_intra_owner_continuations,
                         action.target_pc);
        }
        break;
      case BoundaryTailRecoveryDisposition::kMaterializedTerminalBoundary:
      case BoundaryTailRecoveryDisposition::kReclassified:
      case BoundaryTailRecoveryDisposition::kKeptModeledBoundary:
        if (action.detail == "modeled_reentry_boundary" ||
            action.detail == "boundary_continuation_materialized" ||
            action.detail == "modeled_controlled_return" ||
            action.detail == "controlled_return_continuation_lifted") {
          appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                         action.target_pc);
          if (action.detail == "modeled_controlled_return") {
            appendUniquePc(bundle.recovery_quality.modeled_controlled_returns,
                           action.target_pc);
          }
        } else if (action.detail == "terminal_modeled_boundary") {
          appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                         action.target_pc);
          appendUniquePc(bundle.recovery_quality.terminal_modeled_boundaries,
                         action.target_pc);
        } else if (action.detail == "controlled_return_unresolved") {
          appendUniquePc(bundle.recovery_quality.controlled_return_unresolved,
                         action.target_pc);
          appendUniquePc(bundle.recovery_quality.modeled_pc_relative_return_thunks,
                         action.target_pc);
        } else if (action.detail == "modeled_intra_owner_continuation") {
          appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                         action.target_pc);
          appendUniquePc(bundle.recovery_quality.modeled_intra_owner_continuations,
                         action.target_pc);
        }
        break;
      case BoundaryTailRecoveryDisposition::kHardRejected:
        appendUniquePc(bundle.recovery_quality.hard_rejected_targets,
                       action.target_pc);
        break;
      case BoundaryTailRecoveryDisposition::kPlanned:
      case BoundaryTailRecoveryDisposition::kSkipped:
        break;
    }
  }
  for (const auto &action : bundle.executed_recovery_actions) {
    if (action.detail == "modeled_reentry_boundary" ||
        action.detail == "boundary_reentry_still_modeled" ||
        action.detail == "modeled_controlled_return") {
      appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                     action.target_pc);
      if (action.detail == "modeled_controlled_return") {
        appendUniquePc(bundle.recovery_quality.modeled_controlled_returns,
                       action.target_pc);
      }
    } else if (action.detail == "modeled_terminal_boundary") {
      appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.terminal_modeled_boundaries,
                     action.target_pc);
    } else if (action.detail == "terminal_modeled_child") {
      appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.terminal_modeled_children,
                     action.target_pc);
    } else if (action.detail == "controlled_return_unresolved") {
      appendUniquePc(bundle.recovery_quality.controlled_return_unresolved,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.modeled_pc_relative_return_thunks,
                     action.target_pc);
    } else if (action.detail == "modeled_intra_owner_continuation") {
      appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.modeled_intra_owner_continuations,
                     action.target_pc);
    } else if (action.detail == "intra_owner_continuation_lifted") {
      appendUniquePc(bundle.recovery_quality.lifted_intra_owner_continuations,
                     action.target_pc);
    }
  }
  for (const auto &callee : bundle.external_callees) {
    if (isAcceptedExternalLeafCall(callee) &&
        llvm::find(bundle.recovery_quality.accepted_external_leaf_calls,
                   callee) ==
            bundle.recovery_quality.accepted_external_leaf_calls.end()) {
      bundle.recovery_quality.accepted_external_leaf_calls.push_back(callee);
    }
  }

  bool all_remaining_edges_classified = true;
  for (uint64_t target_pc : bundle.executable_placeholder_targets) {
    if (!classified_targets.contains(target_pc) &&
        llvm::find(bundle.recovery_quality.terminal_modeled_targets, target_pc) ==
            bundle.recovery_quality.terminal_modeled_targets.end() &&
        llvm::find(bundle.recovery_quality.hard_rejected_targets, target_pc) ==
            bundle.recovery_quality.hard_rejected_targets.end()) {
      all_remaining_edges_classified = false;
      break;
    }
  }
  if (all_remaining_edges_classified) {
    for (uint64_t target_pc : bundle.native_boundary_targets) {
      if (!classified_targets.contains(target_pc) &&
          llvm::find(bundle.recovery_quality.modeled_reentry_boundaries,
                     target_pc) ==
              bundle.recovery_quality.modeled_reentry_boundaries.end() &&
          llvm::find(bundle.recovery_quality.terminal_modeled_boundaries,
                     target_pc) ==
              bundle.recovery_quality.terminal_modeled_boundaries.end()) {
        all_remaining_edges_classified = false;
        break;
      }
    }
  }

  bundle.recovery_quality.structurally_closed =
      bundle.remill_runtime_callees.empty() && all_remaining_edges_classified;
  bundle.recovery_quality.dispatcher_heavy =
      !bundle.recovery_quality.terminal_modeled_targets.empty() ||
      !bundle.executable_placeholder_targets.empty() ||
      !bundle.native_boundary_targets.empty();
  const bool has_unclassified_executable_placeholder = llvm::any_of(
      bundle.executable_placeholder_targets, [&](uint64_t target_pc) {
        return llvm::find(bundle.recovery_quality.terminal_modeled_targets,
                          target_pc) ==
                   bundle.recovery_quality.terminal_modeled_targets.end() &&
               llvm::find(bundle.recovery_quality.hard_rejected_targets,
                          target_pc) ==
                   bundle.recovery_quality.hard_rejected_targets.end();
      });
  const bool has_unclassified_boundary = llvm::any_of(
      bundle.native_boundary_targets, [&](uint64_t target_pc) {
        return llvm::find(bundle.recovery_quality.modeled_reentry_boundaries,
                          target_pc) ==
                   bundle.recovery_quality.modeled_reentry_boundaries.end() &&
               llvm::find(bundle.recovery_quality.terminal_modeled_boundaries,
                          target_pc) ==
                   bundle.recovery_quality.terminal_modeled_boundaries.end();
      });
  bundle.recovery_quality.functionally_recovered =
      bundle.recovery_quality.structurally_closed &&
      bundle.recovery_quality.terminal_modeled_children.empty() &&
      bundle.recovery_quality.modeled_controlled_returns.empty() &&
      bundle.recovery_quality.controlled_return_unresolved.empty() &&
      !has_unclassified_executable_placeholder &&
      !has_unclassified_boundary &&
      bundle.recovery_quality.hard_rejected_targets.empty();
}

void augmentRecoveryQualityFromTailGraph(
    RoundArtifactBundle &bundle, const FinalTailGraph &graph) {
  bool has_unclassified_tail = false;
  for (const auto &node : graph.nodes) {
    switch (node.kind) {
      case FinalTailNodeKind::kExecutablePlaceholder:
        has_unclassified_tail = true;
        break;
      case FinalTailNodeKind::kModeledReentryBoundary:
        appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                       node.target_pc);
        if (node.detail == "modeled_controlled_return") {
          appendUniquePc(bundle.recovery_quality.modeled_controlled_returns,
                         node.target_pc);
          appendUniquePc(bundle.recovery_quality.modeled_pc_relative_return_thunks,
                         node.target_pc);
        } else if (node.detail == "modeled_intra_owner_continuation") {
          appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                         node.target_pc);
          appendUniquePc(bundle.recovery_quality.modeled_intra_owner_continuations,
                         node.target_pc);
        }
        break;
      case FinalTailNodeKind::kTerminalModeledBoundary:
        appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                       node.target_pc);
        appendUniquePc(bundle.recovery_quality.terminal_modeled_boundaries,
                       node.target_pc);
        break;
      case FinalTailNodeKind::kTerminalModeledChild:
        appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                       node.target_pc);
        appendUniquePc(bundle.recovery_quality.terminal_modeled_children,
                       node.target_pc);
        break;
      case FinalTailNodeKind::kHardRejectedBoundary:
      case FinalTailNodeKind::kHardRejectedExecutable:
        appendUniquePc(bundle.recovery_quality.hard_rejected_targets,
                       node.target_pc);
        break;
      case FinalTailNodeKind::kRetryableBoundary:
        if (node.detail == "controlled_return_unresolved") {
          appendUniquePc(bundle.recovery_quality.controlled_return_unresolved,
                         node.target_pc);
          appendUniquePc(bundle.recovery_quality.modeled_pc_relative_return_thunks,
                         node.target_pc);
        }
        has_unclassified_tail = true;
        break;
    }
  }

  if (!graph.nodes.empty())
    bundle.recovery_quality.dispatcher_heavy = true;

  if (!bundle.recovery_quality.modeled_reentry_boundaries.empty() ||
      !bundle.recovery_quality.modeled_controlled_returns.empty() ||
      !bundle.recovery_quality.controlled_return_unresolved.empty() ||
      !bundle.recovery_quality.terminal_modeled_children.empty() ||
      !bundle.recovery_quality.hard_rejected_targets.empty()) {
    bundle.recovery_quality.functionally_recovered = false;
  }

  if (has_unclassified_tail)
    bundle.recovery_quality.structurally_closed = false;

  if (!bundle.recovery_quality.structurally_closed)
    bundle.recovery_quality.functionally_recovered = false;
}

bool isSelfLoopOnlyTerminator(const llvm::BasicBlock &BB) {
  auto *branch = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
  return branch && branch->isUnconditional() &&
         branch->getSuccessor(0) == &BB;
}

bool isInternalSelfLoopOutputRoot(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (!F.hasFnAttribute("omill.internal_output_root") &&
      !F.getName().contains("internal_output_root")) {
    return false;
  }
  if (F.empty())
    return false;

  llvm::SmallVector<const llvm::BasicBlock *, 8> worklist = {&F.getEntryBlock()};
  llvm::SmallPtrSet<const llvm::BasicBlock *, 8> visited;
  bool saw_self_loop = false;
  bool saw_return = false;
  while (!worklist.empty()) {
    const auto *BB = worklist.pop_back_val();
    if (!BB || !visited.insert(BB).second)
      continue;

    for (const auto &I : *BB) {
      const auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      const auto *callee = call ? call->getCalledFunction() : nullptr;
      if (!callee || callee->isIntrinsic())
        continue;
      return false;
    }

    if (isSelfLoopOnlyTerminator(*BB)) {
      saw_self_loop = true;
      continue;
    }

    const auto *term = BB->getTerminator();
    if (llvm::isa<llvm::ReturnInst>(term)) {
      saw_return = true;
      continue;
    }
    if (llvm::isa<llvm::UnreachableInst>(term))
      continue;
    for (unsigned i = 0; i < term->getNumSuccessors(); ++i)
      worklist.push_back(term->getSuccessor(i));
  }

  return saw_self_loop && !saw_return;
}

const llvm::Function *findDispatcherShellInternalRoot(
    const llvm::Function &root) {
  if (root.isDeclaration() || root.empty() ||
      root.hasFnAttribute("omill.internal_output_root")) {
    return nullptr;
  }

  bool has_state_alloca = false;
  bool has_large_stack_alloca = false;
  bool saw_memset = false;
  llvm::SmallPtrSet<const llvm::Function *, 4> defined_callees;
  const auto &DL = root.getParent()->getDataLayout();
  for (const auto &BB : root) {
    for (const auto &I : BB) {
      if (const auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
        if (const auto *allocated_struct =
                llvm::dyn_cast<llvm::StructType>(alloca->getAllocatedType());
            allocated_struct && allocated_struct->hasName() &&
            allocated_struct->getName() == "struct.State") {
          has_state_alloca = true;
        }
        if (const auto *AT =
                llvm::dyn_cast<llvm::ArrayType>(alloca->getAllocatedType());
            AT && DL.getTypeAllocSize(alloca->getAllocatedType()) >= 4096) {
          has_large_stack_alloca = true;
        }
      }

      const auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      const auto *callee = call ? call->getCalledFunction() : nullptr;
      if (!callee)
        continue;
      if (callee->isIntrinsic()) {
        if (callee->getName().starts_with("llvm.memset"))
          saw_memset = true;
        continue;
      }
      if (callee->isDeclaration())
        return nullptr;
      defined_callees.insert(callee);
    }
  }

  if (!(has_state_alloca || has_large_stack_alloca || saw_memset) ||
      defined_callees.size() != 1) {
    return nullptr;
  }

  const auto *internal_root = *defined_callees.begin();
  return isInternalSelfLoopOutputRoot(*internal_root) ? internal_root : nullptr;
}

void refineRecoveryQualityFromModuleShape(const llvm::Module &M,
                                          RoundArtifactBundle &bundle) {
  bundle.recovery_quality.dispatcher_shell = false;

  if (!bundle.executable_placeholder_targets.empty() ||
      !bundle.native_boundary_targets.empty() ||
      !bundle.remill_runtime_callees.empty()) {
    return;
  }

  llvm::SmallVector<const llvm::Function *, 8> output_roots;
  for (const auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
        F.hasFnAttribute("omill.internal_output_root")) {
      continue;
    }
    output_roots.push_back(&F);
  }
  if (output_roots.empty()) {
    for (const auto &F : M) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        output_roots.push_back(&F);
    }
  }

  for (const auto *root : output_roots) {
    if (!findDispatcherShellInternalRoot(*root))
      continue;
    bundle.recovery_quality.dispatcher_shell = true;
    bundle.recovery_quality.dispatcher_heavy = true;
    bundle.recovery_quality.functionally_recovered = false;
    return;
  }
}

CleanupActionArtifact makeCleanupActionArtifact(llvm::StringRef label,
                                                bool changed,
                                                llvm::StringRef detail = {}) {
  CleanupActionArtifact artifact;
  artifact.label = label.str();
  artifact.changed = changed;
  artifact.detail = detail.str();
  return artifact;
}

void emitPreciseLog(const OutputRecoveryOptions &options,
                    const OutputRecoveryCallbacks &callbacks,
                    llvm::StringRef component, llvm::StringRef stage,
                    llvm::StringRef message,
                    std::optional<uint64_t> target_pc = std::nullopt,
                    std::optional<unsigned> round = std::nullopt,
                    std::optional<std::string> detail = std::nullopt) {
  if (!options.enable_precise_logs || !callbacks.precise_log)
    return;
  RuntimePreciseLogEvent event;
  event.component = component.str();
  event.stage = stage.str();
  event.message = message.str();
  event.target_pc = target_pc;
  event.round = round;
  event.detail = std::move(detail);
  callbacks.precise_log(event);
}

llvm::SmallVector<const llvm::Function *, 8> collectArtifactOutputRoots(
    const llvm::Module &M) {
  llvm::SmallVector<const llvm::Function *, 8> output_roots;
  for (const auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
        F.hasFnAttribute("omill.internal_output_root")) {
      continue;
    }
    output_roots.push_back(&F);
  }
  if (output_roots.empty()) {
    for (const auto &F : M) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        output_roots.push_back(&F);
    }
  }
  return output_roots;
}

void appendUniqueString(std::vector<std::string> &values, llvm::StringRef value) {
  if (value.empty())
    return;
  if (llvm::find(values, value.str()) == values.end())
    values.push_back(value.str());
}

std::optional<uint64_t> extractTailGraphSourcePC(llvm::StringRef name) {
  if (uint64_t pc = extractStructuralCodeTargetPC(name))
    return pc;

  auto parseWithPrefix = [&](llvm::StringRef prefix) -> std::optional<uint64_t> {
    if (!name.starts_with(prefix))
      return std::nullopt;
    llvm::StringRef rest = name.drop_front(prefix.size());
    size_t hex_len = 0;
    while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
      ++hex_len;
    if (hex_len == 0)
      return std::nullopt;
    uint64_t pc = 0;
    if (rest.substr(0, hex_len).getAsInteger(16, pc))
      return std::nullopt;
    return pc;
  };

  for (llvm::StringRef prefix :
       {"execchild_sub_", "execchild_blk_", "execchild_block_", "execchild_vm_entry_"}) {
    if (auto pc = parseWithPrefix(prefix))
      return pc;
  }
  return std::nullopt;
}

std::optional<uint64_t> extractTailGraphSourcePC(const llvm::Function &F) {
  return extractTailGraphSourcePC(F.getName());
}

std::pair<std::string, std::optional<uint64_t>> findTailGraphSource(
    const FinalTailGraph &graph, uint64_t target_pc) {
  auto it = llvm::find_if(graph.edges, [&](const FinalTailGraphEdge &edge) {
    return edge.target_pc == target_pc;
  });
  if (it == graph.edges.end())
    return {};
  return {it->source_name, it->source_pc};
}

unsigned finalTailNodePriority(FinalTailNodeKind kind) {
  switch (kind) {
    case FinalTailNodeKind::kHardRejectedBoundary:
    case FinalTailNodeKind::kHardRejectedExecutable:
      return 0;
    case FinalTailNodeKind::kTerminalModeledBoundary:
    case FinalTailNodeKind::kTerminalModeledChild:
      return 1;
    case FinalTailNodeKind::kModeledReentryBoundary:
      return 2;
    case FinalTailNodeKind::kRetryableBoundary:
      return 3;
    case FinalTailNodeKind::kExecutablePlaceholder:
      return 4;
  }
  return 5;
}

bool isTailPlaceholderDeclarationName(llvm::StringRef name) {
  return name.starts_with("omill_executable_target_") ||
         name.starts_with("omill_native_target_") ||
         name.starts_with("omill_native_boundary_") ||
         name.starts_with("omill_vm_enter_target_") ||
         name.starts_with("omill_vm_enter_boundary_");
}

bool isBoundaryTailDeclarationName(llvm::StringRef name) {
  return name.starts_with("omill_native_target_") ||
         name.starts_with("omill_native_boundary_") ||
         name.starts_with("omill_vm_enter_target_") ||
         name.starts_with("omill_vm_enter_boundary_");
}

std::vector<uint64_t> parseTailTargetListAttr(llvm::StringRef value) {
  std::vector<uint64_t> targets;
  llvm::SmallVector<llvm::StringRef, 8> parts;
  value.split(parts, ',', -1, false);
  for (auto part : parts) {
    auto trimmed = part.trim();
    if (trimmed.empty())
      continue;
    uint64_t pc = 0;
    if (trimmed.consume_front("0x")) {
      if (trimmed.getAsInteger(16, pc))
        continue;
    } else if (trimmed.getAsInteger(16, pc)) {
      continue;
    }
    appendUniquePc(targets, pc);
  }
  return targets;
}

std::string joinTailTargetList(llvm::ArrayRef<uint64_t> targets) {
  std::string joined;
  llvm::raw_string_ostream os(joined);
  bool first = true;
  for (uint64_t target_pc : targets) {
    if (!first)
      os << ",";
    first = false;
    os << llvm::utohexstr(target_pc);
  }
  return joined;
}

std::string defaultTailSymbolName(const FinalTailGraphNode &node) {
  if (!node.symbol_name.empty())
    return node.symbol_name;

  switch (node.kind) {
    case FinalTailNodeKind::kExecutablePlaceholder:
    case FinalTailNodeKind::kTerminalModeledChild:
    case FinalTailNodeKind::kHardRejectedExecutable:
      return "omill_executable_target_" + llvm::utohexstr(node.target_pc);
    case FinalTailNodeKind::kModeledReentryBoundary:
      return "omill_native_target_" + llvm::utohexstr(node.target_pc);
    case FinalTailNodeKind::kTerminalModeledBoundary:
    case FinalTailNodeKind::kHardRejectedBoundary:
    case FinalTailNodeKind::kRetryableBoundary:
      return "omill_native_boundary_" + llvm::utohexstr(node.target_pc);
  }
  return "omill_native_boundary_" + llvm::utohexstr(node.target_pc);
}

constexpr llvm::StringLiteral kTailGraphTargetsAttr =
    "omill.final_tail_graph_targets";
constexpr llvm::StringLiteral kTailGraphSummaryAttr =
    "omill.final_tail_graph_summary";
constexpr llvm::StringLiteral kTailGraphKindAttr =
    "omill.final_tail_graph_kind";
constexpr llvm::StringLiteral kTailGraphDetailAttr =
    "omill.final_tail_graph_detail";
constexpr llvm::StringLiteral kTailGraphContinuationAttr =
    "omill.final_tail_graph_continuation";

std::optional<FinalTailNodeKind> parseFinalTailNodeKind(llvm::StringRef text) {
  for (FinalTailNodeKind kind :
       {FinalTailNodeKind::kExecutablePlaceholder,
        FinalTailNodeKind::kModeledReentryBoundary,
        FinalTailNodeKind::kTerminalModeledBoundary,
        FinalTailNodeKind::kTerminalModeledChild,
        FinalTailNodeKind::kHardRejectedBoundary,
        FinalTailNodeKind::kHardRejectedExecutable,
        FinalTailNodeKind::kRetryableBoundary}) {
    if (text == toString(kind))
      return kind;
  }
  return std::nullopt;
}

void populateRoundArtifactBundleFromModule(const llvm::Module &M,
                                           RoundArtifactBundle &bundle) {
  bundle.module_fingerprint = llvm::StructuralHash(M);
  auto output_roots = collectArtifactOutputRoots(M);
  for (const auto *root : output_roots)
    appendUniqueString(bundle.output_root_names, root->getName());

  for (const auto *root : output_roots) {
    llvm::SmallVector<const llvm::Function *, 16> worklist = {root};
    llvm::SmallPtrSet<const llvm::Function *, 16> visited;
    while (!worklist.empty()) {
      const auto *current = worklist.pop_back_val();
      if (!current || !visited.insert(current).second)
        continue;
      for (const auto &BB : *current) {
        for (const auto &I : BB) {
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          const auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (!callee)
            continue;
          if (callee->isIntrinsic())
            continue;
          if (callee->isDeclaration()) {
            const uint64_t target_pc = extractStructuralCodeTargetPC(*callee);
            if (callee->getName().starts_with("omill_executable_target_")) {
              appendUniquePc(bundle.executable_placeholder_targets, target_pc);
            } else if (callee->getName().starts_with("omill_native_target_") ||
                       callee->getName().starts_with("omill_native_boundary_") ||
                       callee->getName().starts_with("omill_vm_enter_target_") ||
                       callee->getName().starts_with("omill_vm_enter_boundary_")) {
              appendUniquePc(bundle.native_boundary_targets, target_pc);
            } else if (callee->getName().starts_with("__remill_")) {
              appendUniqueString(bundle.remill_runtime_callees,
                                 callee->getName());
            } else if (isLoweringHelperCalleeName(callee->getName())) {
              appendUniqueString(bundle.lowering_helper_callees,
                                 callee->getName());
            } else if (callee->getName() != "__omill_missing_block_handler") {
              appendUniqueString(bundle.external_callees, callee->getName());
            }
            continue;
          }
          worklist.push_back(callee);
        }
      }
    }
  }
}

BoundaryFact mergeRuntimeBoundaryFacts(const BoundaryFact &primary,
                                      const BoundaryFact &fallback) {
  BoundaryFact merged = primary;
  if (!merged.boundary_pc)
    merged.boundary_pc = fallback.boundary_pc;
  if (!merged.native_target_pc)
    merged.native_target_pc = fallback.native_target_pc;
  if (!merged.continuation_pc)
    merged.continuation_pc = fallback.continuation_pc;
  if (!merged.continuation_vip_pc)
    merged.continuation_vip_pc = fallback.continuation_vip_pc;
  if (!merged.controlled_return_pc)
    merged.controlled_return_pc = fallback.controlled_return_pc;
  if (!merged.continuation_slot_id)
    merged.continuation_slot_id = fallback.continuation_slot_id;
  if (!merged.continuation_stack_cell_id)
    merged.continuation_stack_cell_id = fallback.continuation_stack_cell_id;
  if (!merged.continuation_owner_id)
    merged.continuation_owner_id = fallback.continuation_owner_id;
  if (merged.continuation_owner_kind == VirtualStackOwnerKind::kUnknown)
    merged.continuation_owner_kind = fallback.continuation_owner_kind;
  if (!merged.covered_entry_pc)
    merged.covered_entry_pc = fallback.covered_entry_pc;
  if (!merged.continuation_entry_transform)
    merged.continuation_entry_transform = fallback.continuation_entry_transform;
  if (merged.return_address_control_kind ==
      VirtualReturnAddressControlKind::kUnknown) {
    merged.return_address_control_kind = fallback.return_address_control_kind;
  }
  if (merged.kind == BoundaryKind::kUnknown)
    merged.kind = fallback.kind;
  if (merged.exit_disposition == BoundaryDisposition::kUnknown)
    merged.exit_disposition = fallback.exit_disposition;
  merged.is_partial_exit = merged.is_partial_exit || fallback.is_partial_exit;
  merged.is_full_exit = merged.is_full_exit || fallback.is_full_exit;
  merged.reenters_vm = merged.reenters_vm || fallback.reenters_vm;
  merged.is_vm_enter = merged.is_vm_enter || fallback.is_vm_enter;
  merged.is_nested_vm_enter =
      merged.is_nested_vm_enter || fallback.is_nested_vm_enter;
  merged.suppresses_normal_fallthrough =
      merged.suppresses_normal_fallthrough ||
      fallback.suppresses_normal_fallthrough;
  return merged;
}

std::optional<uint64_t> effectiveBoundaryContinuationPc(const BoundaryFact &fact) {
  if (fact.continuation_entry_transform &&
      fact.continuation_entry_transform->jump_target_pc) {
    return fact.continuation_entry_transform->jump_target_pc;
  }
  if (fact.suppresses_normal_fallthrough)
    return fact.controlled_return_pc;
  return fact.continuation_pc;
}

std::optional<BoundaryFact> findBoundaryFactForTargetInSession(
    const DevirtualizationOrchestrator &orchestrator, uint64_t target_pc) {
  const auto &session = orchestrator.session();
  if (auto it = session.graph.boundary_facts_by_target.find(target_pc);
      it != session.graph.boundary_facts_by_target.end() && it->second.boundary) {
    return it->second.boundary;
  }
  for (const auto &[key, entry] : session.graph.boundary_facts_by_target) {
    (void)key;
    if (!entry.boundary)
      continue;
    if ((entry.boundary->native_target_pc &&
         *entry.boundary->native_target_pc == target_pc) ||
        (entry.boundary->boundary_pc &&
         *entry.boundary->boundary_pc == target_pc)) {
      return entry.boundary;
    }
  }
  for (const auto &[identity, edge] : session.graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.boundary)
      continue;
    if ((edge.target_pc && *edge.target_pc == target_pc) ||
        (edge.boundary->native_target_pc &&
         *edge.boundary->native_target_pc == target_pc) ||
        (edge.boundary->boundary_pc &&
         *edge.boundary->boundary_pc == target_pc)) {
      return edge.boundary;
    }
  }
  return std::nullopt;
}

std::optional<BoundaryFact> findBoundaryFactForTargetInModule(
    const llvm::Module &module, uint64_t target_pc) {
  std::optional<BoundaryFact> module_boundary;
  int best_score = -1;
  auto candidateScore = [&](const llvm::Function &F,
                            const BoundaryFact &fact) -> int {
    int score = 0;
    if (extractStructuralCodeTargetPC(F) == target_pc)
      score += 1;
    if (fact.native_target_pc && *fact.native_target_pc == target_pc)
      score += 2;
    if (fact.boundary_pc && *fact.boundary_pc == target_pc)
      score += 1;
    if (fact.reenters_vm || fact.is_vm_enter || fact.is_nested_vm_enter ||
        fact.continuation_pc || fact.continuation_vip_pc ||
        fact.controlled_return_pc ||
        fact.continuation_slot_id || fact.continuation_stack_cell_id) {
      score += 16;
    }
    if (fact.kind == BoundaryKind::kVmEnterBoundary ||
        fact.kind == BoundaryKind::kNestedVmEnterBoundary) {
      score += 8;
    }
    return score;
  };

  for (auto &F : module) {
    auto fact = readBoundaryFact(F);
    if (!fact)
      continue;
    if (extractStructuralCodeTargetPC(F) != target_pc &&
        (!fact->native_target_pc || *fact->native_target_pc != target_pc) &&
        (!fact->boundary_pc || *fact->boundary_pc != target_pc)) {
      continue;
    }
    const int score = candidateScore(F, *fact);
    if (!module_boundary || score > best_score) {
      module_boundary = *fact;
      best_score = score;
    }
  }

  return module_boundary;
}

std::optional<BoundaryFact> findBoundaryFactForTarget(
    const DevirtualizationOrchestrator &orchestrator, const llvm::Module *module,
    uint64_t target_pc) {
  auto session_boundary =
      findBoundaryFactForTargetInSession(orchestrator, target_pc);
  if (!module)
    return session_boundary;

  auto module_boundary = findBoundaryFactForTargetInModule(*module, target_pc);
  if (module_boundary) {
    if (module_boundary->boundary_pc &&
        *module_boundary->boundary_pc != target_pc) {
      if (auto boundary_pc_module =
              findBoundaryFactForTargetInModule(*module,
                                                *module_boundary->boundary_pc)) {
        module_boundary =
            mergeRuntimeBoundaryFacts(*module_boundary, *boundary_pc_module);
      }
    }
    if (module_boundary->native_target_pc &&
        *module_boundary->native_target_pc != target_pc) {
      if (auto native_target_module =
              findBoundaryFactForTargetInModule(*module,
                                                *module_boundary->native_target_pc)) {
        module_boundary =
            mergeRuntimeBoundaryFacts(*module_boundary, *native_target_module);
      }
    }
  }

  if (!session_boundary && module_boundary) {
    if (module_boundary->boundary_pc &&
        *module_boundary->boundary_pc != target_pc) {
      session_boundary = findBoundaryFactForTargetInSession(
          orchestrator, *module_boundary->boundary_pc);
    }
    if (!session_boundary && module_boundary->native_target_pc &&
        *module_boundary->native_target_pc != target_pc) {
      session_boundary = findBoundaryFactForTargetInSession(
          orchestrator, *module_boundary->native_target_pc);
    }
  }

  if (session_boundary && module_boundary)
    return mergeRuntimeBoundaryFacts(*session_boundary, *module_boundary);
  if (session_boundary)
    return session_boundary;
  return module_boundary;
}

std::optional<FrontierWorkStatus> findBoundaryContinuationStatus(
    const DevirtualizationOrchestrator &orchestrator, uint64_t boundary_pc,
    uint64_t continuation_pc) {
  std::optional<FrontierWorkStatus> fallback_status;
  for (const auto &[identity, edge] :
       orchestrator.session().graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.from_boundary_continuation || !edge.boundary ||
        !edge.boundary->boundary_pc || *edge.boundary->boundary_pc != boundary_pc) {
      continue;
    }
    if (edge.target_pc && *edge.target_pc == continuation_pc)
      return edge.status;
    if (edge.executable_target && edge.executable_target->effective_target_pc &&
        *edge.executable_target->effective_target_pc == continuation_pc) {
      return edge.status;
    }
    if (!fallback_status)
      fallback_status = edge.status;
  }
  return fallback_status;
}

std::optional<std::string> findVmEnterChildImportFailureReasonForTarget(
    const DevirtualizationOrchestrator &orchestrator, uint64_t target_pc) {
  std::optional<std::string> fallback_reason;
  for (const auto &[identity, edge] :
       orchestrator.session().graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc || *edge.target_pc != target_pc)
      continue;
    const bool is_vm_enter_candidate =
        edge.kind == FrontierWorkKind::kVmEnterBoundary ||
        (edge.boundary &&
         (edge.boundary->is_vm_enter || edge.boundary->is_nested_vm_enter ||
          edge.boundary->kind == BoundaryKind::kVmEnterBoundary ||
          edge.boundary->kind == BoundaryKind::kNestedVmEnterBoundary));
    if (!is_vm_enter_candidate || edge.failure_reason.empty())
      continue;
    if (edge.failure_reason != "vm_entry_boundary")
      return edge.failure_reason;
    if (!fallback_reason)
      fallback_reason = edge.failure_reason;
  }
  return fallback_reason;
}

std::optional<std::string> findVmEnterChildImportFailureReason(
    const DevirtualizationOrchestrator &orchestrator, llvm::Module &M,
    uint64_t continuation_pc) {
  if (auto exact =
          findVmEnterChildImportFailureReasonForTarget(orchestrator,
                                                      continuation_pc)) {
    return exact;
  }

  if (auto *continuation = findBoundaryContinuationFunction(M, continuation_pc)) {
    if (auto target_pc = extractStructuralCodeTargetPC(*continuation)) {
      if (auto normalized =
              findVmEnterChildImportFailureReasonForTarget(orchestrator,
                                                          target_pc)) {
        return normalized;
      }
    }
    if (uint64_t entry_pc = extractEntryVA(continuation->getName());
        entry_pc != 0) {
      if (auto normalized =
              findVmEnterChildImportFailureReasonForTarget(orchestrator,
                                                          entry_pc)) {
        return normalized;
      }
    }
  }

  std::optional<std::pair<uint64_t, std::string>> nearest_reason;
  for (const auto &[identity, edge] :
       orchestrator.session().graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc || edge.failure_reason.empty())
      continue;
    const bool is_vm_enter_candidate =
        edge.kind == FrontierWorkKind::kVmEnterBoundary ||
        (edge.boundary &&
         (edge.boundary->is_vm_enter || edge.boundary->is_nested_vm_enter ||
          edge.boundary->kind == BoundaryKind::kVmEnterBoundary ||
          edge.boundary->kind == BoundaryKind::kNestedVmEnterBoundary));
    if (!is_vm_enter_candidate || edge.failure_reason == "vm_entry_boundary")
      continue;
    const uint64_t delta =
        *edge.target_pc > continuation_pc ? *edge.target_pc - continuation_pc
                                          : continuation_pc - *edge.target_pc;
    if (delta > 0x80u)
      continue;
    if (!nearest_reason || delta < nearest_reason->first) {
      nearest_reason = std::make_pair(delta, edge.failure_reason);
    }
  }
  if (nearest_reason)
    return nearest_reason->second;
  return std::nullopt;
}

uint64_t canonicalizeVmEnterImportTarget(llvm::Module &M, uint64_t target_pc) {
  if (auto *continuation = findBoundaryContinuationFunction(M, target_pc)) {
    if (auto structural_pc = extractStructuralCodeTargetPC(*continuation))
      return structural_pc;
    if (uint64_t entry_pc = extractEntryVA(continuation->getName());
        entry_pc != 0) {
      return entry_pc;
    }
  }
  return target_pc;
}

bool wasTargetImportedAcrossBundles(
    llvm::ArrayRef<RoundArtifactBundle> bundles, uint64_t target_pc) {
  for (const auto &bundle : bundles) {
    if (llvm::find(bundle.imported_targets, target_pc) !=
        bundle.imported_targets.end()) {
      return true;
    }
  }
  return false;
}

llvm::Function *findBoundaryContinuationFunction(llvm::Module &M,
                                                 uint64_t continuation_pc) {
  if (auto *exact_structural =
          findStructuralCodeTargetFunctionByPC(M, continuation_pc)) {
    return exact_structural;
  }
  if (auto *exact_block = findLiftedOrBlockFunctionByPC(M, continuation_pc))
    return exact_block;
  if (auto *exact = findLiftedOrCoveredFunctionByPC(M, continuation_pc))
    return exact;
  if (auto nearby_pc =
          findNearestCoveredLiftedOrBlockPC(M, continuation_pc, 0x80)) {
    if (auto *nearby = findLiftedOrCoveredFunctionByPC(M, *nearby_pc))
      return nearby;
    if (auto *nearby_structural =
            findStructuralCodeTargetFunctionByPC(M, *nearby_pc)) {
      return nearby_structural;
    }
  }
  if (auto *nearby_structural =
          findNearestStructuralCodeTargetFunctionByPC(M, continuation_pc, 0x80)) {
    if (!nearby_structural->isDeclaration())
      return nearby_structural;
    if (auto fact = readBoundaryFact(*nearby_structural);
        fact && (fact->is_vm_enter || fact->is_nested_vm_enter ||
                 fact->kind == BoundaryKind::kVmEnterBoundary ||
                 fact->kind == BoundaryKind::kNestedVmEnterBoundary)) {
      return nearby_structural;
    }
  }
  return nullptr;
}

bool isUsableBoundaryContinuationFunction(
    const DevirtualizationOrchestrator &orchestrator, llvm::Function *function,
    std::optional<uint64_t> continuation_pc) {
  if (!function || function->isDeclaration())
    return false;

  if (continuation_pc) {
    if (auto imported_it =
            orchestrator.session().imported_vm_enter_child_roots.find(
                *continuation_pc);
        imported_it != orchestrator.session().imported_vm_enter_child_roots.end()) {
      return function->getName() == imported_it->second;
    }
  }

  if (function->getName().starts_with("omill_vm_enter_target_")) {
    if (auto fact = readBoundaryFact(*function);
        fact && (fact->is_vm_enter || fact->is_nested_vm_enter ||
                 fact->kind == BoundaryKind::kVmEnterBoundary ||
                 fact->kind == BoundaryKind::kNestedVmEnterBoundary)) {
      return false;
    }
  }

  return true;
}

bool isQuarantinedProof(const std::optional<ContinuationProof> &proof) {
  if (!proof)
    return false;
  return proof->liveness == ContinuationLiveness::kQuarantined ||
         proof->scheduling_class ==
             FrontierSchedulingClass::kQuarantinedSelectorArm ||
         proof->resolution_kind ==
             ContinuationResolutionKind::kQuarantinedSelectorArm ||
         proof->import_disposition == ContinuationImportDisposition::kDeferred;
}

bool boundaryHasReentryEvidence(const BoundaryFact &boundary) {
  return boundary.reenters_vm || boundary.is_vm_enter ||
         boundary.is_nested_vm_enter || boundary.continuation_pc.has_value() ||
         boundary.continuation_vip_pc.has_value() ||
         boundary.continuation_slot_id.has_value() ||
         boundary.continuation_stack_cell_id.has_value() ||
         boundary.covered_entry_pc.has_value() ||
         boundary.continuation_entry_transform.has_value();
}

unsigned finalStateRecoveryPriority(FinalStateRecoveryActionKind kind) {
  switch (kind) {
    case FinalStateRecoveryActionKind::kRetryTerminalExecutableChild:
      return 0;
    case FinalStateRecoveryActionKind::kRetryExecutableChildImport:
    case FinalStateRecoveryActionKind::kHardReject:
      return 1;
    case FinalStateRecoveryActionKind::kRetryNativeBoundaryRecovery:
      return 2;
    case FinalStateRecoveryActionKind::kKeepModeledPlaceholder:
      return 3;
  }
  return 4;
}

}  // namespace

FrontierRoundSummary DevirtualizationRuntime::runFrontierRound(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &callbacks, FrontierDiscoveryPhase phase) const {
  return orchestrator_.runFrontierRound(M, block_lifter, iterative_session,
                                        callbacks, phase);
}

FrontierIterationSummary DevirtualizationRuntime::runFrontierIterations(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &frontier_callbacks, FrontierDiscoveryPhase phase,
    unsigned max_rounds, const FrontierIterationCallbacks &iteration_callbacks,
    const VmEnterChildImportCallbacks *vm_enter_import_callbacks) const {
  FrontierIterationCallbacks wrapped_callbacks = iteration_callbacks;
  auto original_after = iteration_callbacks.after_frontier_round;
  wrapped_callbacks.after_frontier_round =
      [&](unsigned round, const FrontierRoundSummary &round_summary,
          const VmEnterChildImportSummary &import_summary) {
        const bool should_continue =
            original_after
                ? original_after(round, round_summary, import_summary)
                : round_summary.changed;
        RoundArtifactBundle bundle;
        bundle.stage = RuntimeArtifactStage::kFrontierRound;
        bundle.label =
            (llvm::Twine("phase:") + toString(phase)).str();
        bundle.round = round;
        bundle.changed = round_summary.changed || import_summary.changed;
        bundle.notes = round_summary.discover.notes;
        bundle.notes.insert(bundle.notes.end(), round_summary.advance.notes.begin(),
                            round_summary.advance.notes.end());
        bundle.notes.insert(bundle.notes.end(), import_summary.notes.begin(),
                            import_summary.notes.end());
        populateRoundArtifactBundleFromModule(M, bundle);
        populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                      round_artifact_bundles_);
        bundle.final_tail_graph = buildFinalTailGraph(M);
        augmentRecoveryQualityFromTailGraph(bundle, *bundle.final_tail_graph);
        refineRecoveryQualityFromModuleShape(M, bundle);
        round_artifact_bundles_.push_back(bundle);
        return should_continue;
      };

  return orchestrator_.runFrontierIterations(
      M, block_lifter, iterative_session, frontier_callbacks, phase,
      max_rounds, wrapped_callbacks, vm_enter_import_callbacks);
}

FrontierIterationSummary DevirtualizationRuntime::runPrimaryDevirtualization(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &frontier_callbacks, FrontierDiscoveryPhase phase,
    unsigned max_rounds, const FrontierIterationCallbacks &iteration_callbacks,
    const VmEnterChildImportCallbacks *vm_enter_import_callbacks) const {
  return runFrontierIterations(M, block_lifter, iterative_session,
                               frontier_callbacks, phase, max_rounds,
                               iteration_callbacks,
                               vm_enter_import_callbacks);
}

OutputRecoverySummary DevirtualizationRuntime::runOutputRecovery(
    llvm::Module &M, BlockLifter *block_lifter,
    IterativeLiftingSession *iterative_session,
    const FrontierCallbacks *frontier_callbacks,
    const OutputRecoveryOptions &options,
    const OutputRecoveryCallbacks &callbacks) const {
  OutputRecoverySummary summary;
  const llvm::stable_hash module_fingerprint = llvm::StructuralHash(M);
  if (!child_cache_module_fingerprint_ ||
      *child_cache_module_fingerprint_ != module_fingerprint) {
    child_artifact_cache_.clear();
    boundary_resolution_cache_.clear();
    child_cache_module_fingerprint_ = module_fingerprint;
  }

  std::vector<ImportDecisionArtifact> pending_import_decisions;
  std::vector<CleanupActionArtifact> pending_cleanup_actions;
  auto rememberCleanupAction = [&](llvm::StringRef label, bool changed,
                                   llvm::StringRef detail = {}) {
    pending_cleanup_actions.push_back(
        makeCleanupActionArtifact(label, changed, detail));
  };
  auto noteAbiStep = [&](llvm::StringRef label, auto &&fn) {
    emitPreciseLog(options, callbacks, "output-recovery", "abi-step-begin",
                   label);
    if (callbacks.note_abi_post_cleanup_step)
      callbacks.note_abi_post_cleanup_step(label, true);
    fn();
    if (callbacks.note_abi_post_cleanup_step)
      callbacks.note_abi_post_cleanup_step(label, false);
    rememberCleanupAction(label, /*changed=*/false, "executed");
    emitPreciseLog(options, callbacks, "output-recovery", "abi-step-end",
                   label);
  };
  auto recordArtifactBundle = [&](RoundArtifactBundle bundle) {
    populateRoundArtifactBundleFromModule(M, bundle);
    bundle.import_decisions = std::move(pending_import_decisions);
    bundle.cleanup_actions = std::move(pending_cleanup_actions);
    populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                  round_artifact_bundles_);
    bundle.final_tail_graph = buildFinalTailGraph(M);
    augmentRecoveryQualityFromTailGraph(bundle, *bundle.final_tail_graph);
    refineRecoveryQualityFromModuleShape(M, bundle);
    summary.artifact_bundles.push_back(bundle);
    round_artifact_bundles_.push_back(bundle);
  };
  auto rememberImportDecision =
      [&](llvm::StringRef label, const ChildImportPlan &plan,
          const std::optional<ContinuationProof> &proof,
          const std::optional<ContinuationResolutionResult> &resolution,
          bool imported = false) {
        pending_import_decisions.push_back(makeImportDecisionArtifact(
            label, plan, proof, resolution, imported));
      };

  auto appendImportPlanNote =
      [&](llvm::StringRef label, const ChildImportPlan &plan,
          const std::optional<ContinuationProof> &proof =
              std::optional<ContinuationProof>{},
          const std::optional<ContinuationResolutionResult> &resolution =
              std::optional<ContinuationResolutionResult>{}) {
        rememberImportDecision(
            label, plan, proof, resolution,
            plan.eligibility == ImportEligibility::kImportable &&
                plan.imported_root != nullptr);
    if (plan.eligibility == ImportEligibility::kImportable)
      return;
    std::string note =
        (label + ":0x" + llvm::utohexstr(plan.target_pc) + ":" +
         toString(plan.rejection_reason))
            .str();
    if (!plan.rejection_detail.empty())
      note += ":" + plan.rejection_detail;
    summary.notes.push_back(std::move(note));
    emitPreciseLog(options, callbacks, "output-recovery", label,
                   "child import not accepted", plan.target_pc, std::nullopt,
                   plan.rejection_detail.empty()
                       ? std::optional<std::string>(toString(
                             plan.rejection_reason))
                       : std::optional<std::string>(plan.rejection_detail));
      };
  auto lookupCachedChildArtifact =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode,
          bool dump_virtual_model) -> std::optional<ChildLiftArtifact> {
    ChildArtifactCacheKey key;
    key.target_pc = target_pc;
    key.no_abi = no_abi;
    key.enable_gsd = enable_gsd;
    key.enable_recovery_mode = enable_recovery_mode;
    key.dump_virtual_model = dump_virtual_model;

    auto cache_it = child_artifact_cache_.find(key);
    if (cache_it != child_artifact_cache_.end()) {
      if (cache_it->second.skipped_child_lift) {
        emitPreciseLog(options, callbacks, "output-recovery",
                       "child-cache-negative-hit",
                       "reusing cached failed child lift", target_pc,
                       std::nullopt, cache_it->second.diagnostics);
        return std::nullopt;
      }
      if (!cache_it->second.artifact.ir_text.empty()) {
        emitPreciseLog(options, callbacks, "output-recovery",
                       "child-cache-hit", "reusing cached child artifact",
                       target_pc, std::nullopt, cache_it->second.diagnostics);
        return cache_it->second.artifact;
      }
    }

    emitPreciseLog(options, callbacks, "output-recovery", "child-cache-miss",
                   "lifting child artifact", target_pc);
    if (!callbacks.lift_child_target)
      return std::nullopt;
    auto raw_child = callbacks.lift_child_target(
        target_pc, no_abi, enable_gsd, enable_recovery_mode, dump_virtual_model);
    if (!raw_child) {
      auto &entry = child_artifact_cache_[key];
      entry.raw_artifact = ChildLiftArtifact{};
      entry.raw_artifact.target_pc = target_pc;
      entry.raw_artifact.rejection_reason =
          RecoveryRejectionReason::kChildLiftFailed;
      entry.artifact = entry.raw_artifact;
      entry.prepared_artifact.reset();
      entry.leak_kind = ChildArtifactLeakKind::kNone;
      entry.skipped_child_lift = true;
      entry.diagnostics = "child_lift_failed";
      emitPreciseLog(options, callbacks, "output-recovery",
                     "child-cache-record-failure",
                     "caching failed child lift", target_pc, std::nullopt,
                     entry.diagnostics);
      return std::nullopt;
    }
    auto analyzed_raw_child =
        analyzeChildLiftArtifact(M.getContext(), std::move(*raw_child));
    auto prepared_child = prepareChildLiftArtifact(M.getContext(),
                                                   analyzed_raw_child, no_abi);
    auto analyzed_child = analyzeChildLiftArtifact(
        M.getContext(), prepared_child.artifact);
    auto &entry = child_artifact_cache_[key];
    entry.raw_artifact = std::move(analyzed_raw_child);
    entry.prepared_artifact = std::move(prepared_child);
    entry.artifact = analyzed_child;
    entry.leak_kind = classifyLeakKind(entry.artifact);
    entry.skipped_child_lift = false;
    entry.diagnostics =
        "raw_class=" + std::string(toString(entry.raw_artifact.import_safety)) +
        ",prepared_class=" +
        std::string(toString(entry.artifact.import_safety)) + ",leak=" +
        toString(entry.leak_kind) +
        (entry.prepared_artifact
             ? (",prep=" + entry.prepared_artifact->summary.detail)
             : "");
    emitPreciseLog(options, callbacks, "output-recovery", "child-prepared",
                   "prepared child artifact for analysis", target_pc,
                   std::nullopt, entry.diagnostics);
    return analyzed_child;
  };
  auto findCachedChildArtifactEntry =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode,
          bool dump_virtual_model) -> ChildArtifactCacheEntry * {
    ChildArtifactCacheKey key;
    key.target_pc = target_pc;
    key.no_abi = no_abi;
    key.enable_gsd = enable_gsd;
    key.enable_recovery_mode = enable_recovery_mode;
    key.dump_virtual_model = dump_virtual_model;
    auto it = child_artifact_cache_.find(key);
    if (it == child_artifact_cache_.end())
      return nullptr;
    return &it->second;
  };
  auto rememberChildPlan = [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
                               bool enable_recovery_mode,
                               bool dump_virtual_model,
                               const ChildImportPlan &plan, bool imported) {
    ChildArtifactCacheKey key;
    key.target_pc = target_pc;
    key.no_abi = no_abi;
    key.enable_gsd = enable_gsd;
    key.enable_recovery_mode = enable_recovery_mode;
    key.dump_virtual_model = dump_virtual_model;
    auto it = child_artifact_cache_.find(key);
    if (it == child_artifact_cache_.end())
      return;
    it->second.last_plan = plan;
    it->second.imported = imported;
  };
  auto resolveExecutableContinuation =
      [&](uint64_t target_pc,
          const std::optional<ContinuationProof> &proof)
          -> std::optional<ContinuationResolutionResult> {
    if (!frontier_callbacks)
      return std::nullopt;

    ChildArtifactCacheKey key;
    key.target_pc = target_pc;
    key.no_abi = true;
    key.enable_gsd = false;
    key.enable_recovery_mode = false;
    key.dump_virtual_model = true;

    const bool has_meaningful_proof = hasMeaningfulProof(proof);
    const std::string proof_summary =
        has_meaningful_proof ? summarizeProof(proof) : "proof=none";
    emitPreciseLog(options, callbacks, "output-recovery", "resolver-enter",
                   "starting continuation resolution", target_pc,
                   std::nullopt, proof_summary);

    if (!has_meaningful_proof) {
      ContinuationResolutionResult result;
      result.kind = ContinuationResolverKind::kExecutable;
      result.updated_proof.raw_target_pc = target_pc;
      result.updated_proof.import_disposition =
          ContinuationImportDisposition::kRetryable;
      result.disposition =
          ContinuationResolutionDisposition::kRetryableOpenRegion;
      result.rationale = "missing_proof_skips_reconstruction";
      emitPreciseLog(options, callbacks, "output-recovery", "resolver-skip",
                     "skipping binary reconstruction because continuation proof is missing",
                     target_pc, std::nullopt, proof_summary);
      auto [entry_it, inserted] =
          child_artifact_cache_.try_emplace(key, ChildArtifactCacheEntry{});
      (void)inserted;
      entry_it->second.resolver_result = result;
      entry_it->second.proof_summary = proof_summary;
      entry_it->second.diagnostics =
          "proof=" + proof_summary + ",resolver=missing_proof";
      return result;
    }

    const bool proof_allows_binary_reconstruction =
        proof->resolution_kind ==
            ContinuationResolutionKind::kExactFallthrough ||
        proof->resolution_kind ==
            ContinuationResolutionKind::kTrustedEntry ||
        proof->resolution_kind ==
            ContinuationResolutionKind::kCanonicalOwnerRedirect ||
        proof->resolution_kind ==
            ContinuationResolutionKind::kBoundaryModeled ||
        (proof->resolution_kind ==
             ContinuationResolutionKind::kTerminalModeled &&
         proof->import_disposition ==
             ContinuationImportDisposition::kRetryable &&
         frontier_callbacks->is_exact_call_fallthrough_target &&
         frontier_callbacks->is_exact_call_fallthrough_target(target_pc)) ||
        proof->confidence == ContinuationConfidence::kTrusted;
    emitPreciseLog(
        options, callbacks, "output-recovery", "resolver-gate",
        proof_allows_binary_reconstruction ? "proof_allows_reconstruction"
                                           : "proof_skips_reconstruction",
        target_pc, std::nullopt, proof_summary);

    const bool exact_fallthrough_target =
        frontier_callbacks->is_exact_call_fallthrough_target &&
        frontier_callbacks->is_exact_call_fallthrough_target(target_pc);
    if (!proof_allows_binary_reconstruction ||
        (frontier_callbacks->can_decode_target &&
         !frontier_callbacks->can_decode_target(target_pc) &&
         !exact_fallthrough_target)) {
      ContinuationResolutionResult result;
      result.kind = ContinuationResolverKind::kExecutable;
      result.updated_proof = proof.value_or(ContinuationProof{});
      result.updated_proof.raw_target_pc =
          result.updated_proof.raw_target_pc ? result.updated_proof.raw_target_pc
                                             : target_pc;
      switch (result.updated_proof.import_disposition) {
        case ContinuationImportDisposition::kDeferred:
          result.disposition =
              ContinuationResolutionDisposition::
                  kDeferredQuarantinedSelectorArm;
          break;
        case ContinuationImportDisposition::kRetryable:
        case ContinuationImportDisposition::kUnknown:
          result.disposition =
              ContinuationResolutionDisposition::kRetryableOpenRegion;
          result.updated_proof.import_disposition =
              ContinuationImportDisposition::kRetryable;
          break;
        case ContinuationImportDisposition::kRejected:
          result.disposition =
              ContinuationResolutionDisposition::kRejectedUnsupported;
          break;
        case ContinuationImportDisposition::kImportable:
          result.disposition =
              ContinuationResolutionDisposition::kRetryableOpenRegion;
          result.updated_proof.import_disposition =
              ContinuationImportDisposition::kRetryable;
          break;
      }
      result.rationale = "nondecodable_target_skips_reconstruction";
      emitPreciseLog(options, callbacks, "output-recovery", "resolver-skip",
                     "skipping binary reconstruction for non-importable proof target",
                     target_pc, std::nullopt, proof_summary);
      auto [entry_it, inserted] =
          child_artifact_cache_.try_emplace(key, ChildArtifactCacheEntry{});
      (void)inserted;
      entry_it->second.resolver_result = result;
      entry_it->second.proof_summary = proof_summary;
      entry_it->second.diagnostics =
          "proof=" + proof_summary + ",resolver=skipped_nondecodable";
      return result;
    }

    auto [entry_it, inserted] =
        child_artifact_cache_.try_emplace(key, ChildArtifactCacheEntry{});
    (void)inserted;
    auto &entry = entry_it->second;
    if (entry.resolver_result && entry.proof_summary == proof_summary) {
      emitPreciseLog(options, callbacks, "output-recovery",
                     "resolver-cache-hit",
                     "reusing continuation reconstruction", target_pc,
                     std::nullopt, summarizeResolution(entry.resolver_result));
      return entry.resolver_result;
    }

    ContinuationResolutionRequest request;
    request.kind = ContinuationResolverKind::kExecutable;
    request.target_pc = target_pc;
    request.proof = proof;
    emitPreciseLog(options, callbacks, "output-recovery", "resolver-begin",
                   "building continuation reconstruction request", target_pc,
                   std::nullopt, proof_summary);
    request.learned_edges_by_source =
        collectLearnedOutgoingEdges(iterative_session, target_pc, proof);

    ExecutableContinuationResolver resolver;
    emitPreciseLog(options, callbacks, "output-recovery", "resolver-run",
                   "running executable continuation resolver", target_pc);
    auto result = resolver.resolve(request, *frontier_callbacks);
    emitPreciseLog(options, callbacks, "output-recovery",
                   "resolver-after-run", "resolver produced region snapshot",
                   target_pc, std::nullopt,
                   summarizeResolution(
                       std::optional<ContinuationResolutionResult>(result)));
    entry.resolver_result = result;
    entry.region_snapshot = result.region_snapshot;
    entry.proof_summary = proof_summary;
    entry.diagnostics =
        ("proof=" + proof_summary + "," +
         summarizeResolution(std::optional<ContinuationResolutionResult>(result)));
    emitPreciseLog(options, callbacks, "output-recovery", "resolver-record",
                   "recording binary region snapshot", target_pc,
                   std::nullopt, result.region_snapshot.snapshot_key);
    if (iterative_session)
      iterative_session->recordBinaryRegionSnapshot(result.region_snapshot);
    emitPreciseLog(options, callbacks, "output-recovery", "resolver-merge",
                   "merging resolved proof into session", target_pc);
    mergeResolvedProofIntoSession(orchestrator_, target_pc, result.updated_proof);
    emitPreciseLog(options, callbacks, "output-recovery", "resolver-cache-miss",
                   "resolved continuation through binary region reconstruction",
                   target_pc, std::nullopt,
                   summarizeResolution(
                       std::optional<ContinuationResolutionResult>(result)));
    return result;
  };

  if (!options.raw_binary && options.no_abi &&
      options.allow_noabi_postmain_rounds && options.use_block_lifting &&
      block_lifter && iterative_session && frontier_callbacks) {
    FrontierIterationCallbacks iteration_callbacks;
    iteration_callbacks.before_frontier_round = [&](unsigned round) {
      emitPreciseLog(options, callbacks, "output-recovery",
                     "noabi-frontier-round-begin", "starting no-abi round",
                     std::nullopt, round);
      if (callbacks.before_noabi_frontier_round)
        return callbacks.before_noabi_frontier_round(round);
      if (callbacks.run_late_closure_canonicalization)
        callbacks.run_late_closure_canonicalization(
            "noabi_late_output_root_closure");
      return true;
    };
    iteration_callbacks.after_frontier_round =
        [&](unsigned round, const FrontierRoundSummary &round_summary,
            const VmEnterChildImportSummary &) {
          emitPreciseLog(options, callbacks, "output-recovery",
                         "noabi-frontier-round-end",
                         round_summary.changed ? "no-abi round changed"
                                               : "no-abi round stable",
                         std::nullopt, round);
          if (callbacks.after_noabi_frontier_round)
            return callbacks.after_noabi_frontier_round(round, round_summary);
          if (callbacks.annotate_vm_unresolved_continuations)
            callbacks.annotate_vm_unresolved_continuations();
          return round_summary.changed;
        };
    auto late_summary = runPrimaryDevirtualization(
        M, *block_lifter, *iterative_session, *frontier_callbacks,
        FrontierDiscoveryPhase::kCombined, options.late_noabi_closure_rounds,
        iteration_callbacks);
    summary.changed |= late_summary.changed;
    RoundArtifactBundle bundle;
    bundle.stage = RuntimeArtifactStage::kOutputRecoveryRound;
    bundle.label = "noabi_late_frontier";
    bundle.changed = late_summary.changed;
    for (const auto &round_summary : late_summary.round_summaries) {
      bundle.notes.push_back(
          "discover_changed=" + std::to_string(round_summary.discover.changed));
      bundle.notes.push_back(
          "advance_changed=" + std::to_string(round_summary.advance.changed));
    }
    recordArtifactBundle(std::move(bundle));
  }

  if (!options.raw_binary && options.no_abi &&
      options.allow_noabi_postmain_rounds && options.use_block_lifting &&
      callbacks.lift_child_target && callbacks.import_executable_child &&
      callbacks.collect_executable_placeholder_declaration_targets &&
      callbacks.patch_declared_lifted_or_block_calls_to_defined_targets &&
      callbacks.run_final_output_cleanup) {
    llvm::DenseSet<uint64_t> seen_import_targets;
    llvm::DenseSet<uint64_t> exhausted_import_targets;
    for (unsigned import_round = 0;
         import_round < options.max_noabi_executable_child_import_rounds;
         ++import_round) {
      std::vector<uint64_t> imported_executable_children;
      std::vector<RejectedImportArtifact> rejected_imports;
      if (frontier_callbacks) {
        for (const auto &item : collectOutputRootClosureWorkItems(
                 M, frontier_callbacks->is_code_address,
                 frontier_callbacks->has_defined_target,
                 frontier_callbacks->normalize_target_pc)) {
          if (!item.executable_target || !item.target_pc ||
              seen_import_targets.contains(item.target_pc) ||
              exhausted_import_targets.contains(item.target_pc))
            continue;
          auto proof = findContinuationProofForTarget(orchestrator_,
                                                      item.target_pc);
          emitPreciseLog(options, callbacks, "output-recovery",
                         "noabi-child-proof", "evaluating child proof",
                         item.target_pc, std::nullopt, summarizeProof(proof));
          auto resolution =
              resolveExecutableContinuation(item.target_pc, proof);
          emitPreciseLog(options, callbacks, "output-recovery",
                         "noabi-child-resolution",
                         "resolved executable continuation", item.target_pc,
                         std::nullopt, summarizeResolution(resolution));
          if (resolution &&
              resolution->disposition ==
                  ContinuationResolutionDisposition::
                      kDeferredQuarantinedSelectorArm) {
            ChildImportPlan deferred_plan;
            deferred_plan.target_pc = item.target_pc;
            deferred_plan.eligibility = ImportEligibility::kRetryable;
            deferred_plan.rejection_reason = RecoveryRejectionReason::kUnsupported;
            deferred_plan.rejection_detail = "quarantined_selector_arm";
            deferred_plan.proof = proof;
            appendImportPlanNote("noabi_child_plan", deferred_plan, proof,
                                 resolution);
            rejected_imports.push_back(
                {item.target_pc, deferred_plan.rejection_reason,
                 deferred_plan.rejection_detail});
            rememberChildPlan(item.target_pc, /*no_abi=*/true,
                              /*enable_gsd=*/false,
                              /*enable_recovery_mode=*/false,
                              /*dump_virtual_model=*/true, deferred_plan,
                              false);
            continue;
          }
          emitPreciseLog(options, callbacks, "output-recovery",
                         "noabi-child-lift", "lifting executable child",
                         item.target_pc);
          auto child = lookupCachedChildArtifact(
              item.target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
              /*enable_recovery_mode=*/false, /*dump_virtual_model=*/true);
          if (!child) {
            ChildImportPlan failed_plan;
            failed_plan.target_pc = item.target_pc;
            failed_plan.rejection_reason =
                RecoveryRejectionReason::kChildLiftFailed;
            appendImportPlanNote("noabi_child_import", failed_plan, proof,
                                 resolution);
            rejected_imports.push_back(
                {item.target_pc, failed_plan.rejection_reason,
                 failed_plan.rejection_detail});
            exhausted_import_targets.insert(item.target_pc);
            continue;
          }
          auto *cache_entry = findCachedChildArtifactEntry(
              item.target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
              /*enable_recovery_mode=*/false, /*dump_virtual_model=*/true);
          ChildVariantSelectionResult selected_child;
          if (cache_entry) {
            selected_child = selectCachedChildImportArtifact(
                M.getContext(), *cache_entry, ChildRootSelectionMode::kExecutable,
                proof, resolution);
          } else {
            auto prepared_selection = selectPreparedChildImportRoot(
                M.getContext(), *child, ChildRootSelectionMode::kExecutable,
                proof, resolution);
            selected_child.artifact = std::move(prepared_selection.artifact);
            selected_child.plan = std::move(prepared_selection.plan);
            selected_child.used_prepared_variant = true;
          }
          if (selected_child.artifact.selected_root_was_retargeted ||
              !selected_child.used_prepared_variant) {
            emitPreciseLog(options, callbacks, "output-recovery",
                           "noabi-child-root-select",
                           "selected executable child import root", item.target_pc,
                           std::nullopt,
                           selected_child.artifact.selected_root_selection_detail);
          }
          *child = selected_child.artifact;
          auto preimport_plan = selected_child.plan;
          emitPreciseLog(
              options, callbacks, "output-recovery", "noabi-child-plan",
              "classified executable child", item.target_pc, std::nullopt,
              "class=" + std::string(toString(*preimport_plan.import_class)) +
                  ",eligibility=" +
                  std::string(toString(preimport_plan.eligibility)));
          appendImportPlanNote("noabi_child_plan", preimport_plan, proof,
                               resolution);
          if (preimport_plan.eligibility != ImportEligibility::kImportable) {
            rejected_imports.push_back(
                {item.target_pc, preimport_plan.rejection_reason,
                 preimport_plan.rejection_detail});
          }
          rememberChildPlan(item.target_pc, /*no_abi=*/true,
                            /*enable_gsd=*/false,
                            /*enable_recovery_mode=*/false,
                            /*dump_virtual_model=*/true, preimport_plan,
                            false);
          if (preimport_plan.eligibility != ImportEligibility::kImportable) {
            if (preimport_plan.eligibility == ImportEligibility::kRejected)
              exhausted_import_targets.insert(item.target_pc);
            continue;
          }
          auto plan = callbacks.import_executable_child(
              item.target_pc, *child, preimport_plan, "execchild_");
          plan.import_class = preimport_plan.import_class;
          plan.proof = proof;
          if (!plan.selected_root_pc)
            plan.selected_root_pc = preimport_plan.selected_root_pc;
          appendImportPlanNote("noabi_child_import", plan, proof, resolution);
          if (plan.eligibility != ImportEligibility::kImportable ||
              !plan.imported_root) {
            rejected_imports.push_back(
                {item.target_pc, plan.rejection_reason,
                 plan.rejection_detail});
          }
          rememberChildPlan(item.target_pc, /*no_abi=*/true,
                            /*enable_gsd=*/false,
                            /*enable_recovery_mode=*/false,
                            /*dump_virtual_model=*/true, plan,
                            plan.eligibility == ImportEligibility::kImportable &&
                                plan.imported_root != nullptr);
          if (plan.eligibility != ImportEligibility::kImportable ||
              !plan.imported_root) {
            exhausted_import_targets.insert(item.target_pc);
            continue;
          }
          emitPreciseLog(options, callbacks, "output-recovery",
                         "noabi-child-import", "imported executable child",
                         item.target_pc);
          seen_import_targets.insert(item.target_pc);
          imported_executable_children.push_back(item.target_pc);
          ++summary.noabi_imported_children;
        }
      }

      for (uint64_t target_pc :
           callbacks.collect_executable_placeholder_declaration_targets()) {
        if (seen_import_targets.contains(target_pc) ||
            exhausted_import_targets.contains(target_pc))
          continue;
        auto proof = findContinuationProofForTarget(orchestrator_, target_pc);
        emitPreciseLog(options, callbacks, "output-recovery",
                       "noabi-decl-proof", "evaluating declaration proof",
                       target_pc, std::nullopt, summarizeProof(proof));
        auto resolution = resolveExecutableContinuation(target_pc, proof);
        emitPreciseLog(options, callbacks, "output-recovery",
                       "noabi-decl-resolution",
                       "resolved declaration-backed continuation", target_pc,
                       std::nullopt, summarizeResolution(resolution));
        if (resolution &&
            resolution->disposition ==
                ContinuationResolutionDisposition::
                    kDeferredQuarantinedSelectorArm) {
          ChildImportPlan deferred_plan;
          deferred_plan.target_pc = target_pc;
          deferred_plan.eligibility = ImportEligibility::kRetryable;
          deferred_plan.rejection_reason = RecoveryRejectionReason::kUnsupported;
          deferred_plan.rejection_detail = "quarantined_selector_arm";
          deferred_plan.proof = proof;
          appendImportPlanNote("noabi_decl_plan", deferred_plan, proof,
                               resolution);
          rejected_imports.push_back(
              {target_pc, deferred_plan.rejection_reason,
               deferred_plan.rejection_detail});
          rememberChildPlan(target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
                            /*enable_recovery_mode=*/false,
                            /*dump_virtual_model=*/true, deferred_plan, false);
          continue;
        }
        emitPreciseLog(options, callbacks, "output-recovery",
                       "noabi-declaration-lift",
                       "lifting declaration-backed executable child",
                       target_pc);
        auto child = lookupCachedChildArtifact(
            target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
            /*enable_recovery_mode=*/false, /*dump_virtual_model=*/true);
        if (!child) {
          ChildImportPlan failed_plan;
          failed_plan.target_pc = target_pc;
          failed_plan.rejection_reason =
              RecoveryRejectionReason::kChildLiftFailed;
          appendImportPlanNote("noabi_decl_import", failed_plan, proof,
                               resolution);
          rejected_imports.push_back(
              {target_pc, failed_plan.rejection_reason,
               failed_plan.rejection_detail});
          exhausted_import_targets.insert(target_pc);
          continue;
        }
        auto *cache_entry = findCachedChildArtifactEntry(
            target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
            /*enable_recovery_mode=*/false, /*dump_virtual_model=*/true);
        ChildVariantSelectionResult selected_child;
        if (cache_entry) {
          selected_child = selectCachedChildImportArtifact(
              M.getContext(), *cache_entry, ChildRootSelectionMode::kExecutable,
              proof, resolution);
        } else {
          auto prepared_selection = selectPreparedChildImportRoot(
              M.getContext(), *child, ChildRootSelectionMode::kExecutable, proof,
              resolution);
          selected_child.artifact = std::move(prepared_selection.artifact);
          selected_child.plan = std::move(prepared_selection.plan);
          selected_child.used_prepared_variant = true;
        }
        if (selected_child.artifact.selected_root_was_retargeted ||
            !selected_child.used_prepared_variant) {
          emitPreciseLog(options, callbacks, "output-recovery",
                         "noabi-decl-root-select",
                         "selected declaration child import root",
                         target_pc, std::nullopt,
                         selected_child.artifact.selected_root_selection_detail);
        }
        *child = selected_child.artifact;
        auto preimport_plan = selected_child.plan;
        emitPreciseLog(
            options, callbacks, "output-recovery", "noabi-decl-plan",
            "classified declaration-backed child", target_pc, std::nullopt,
            "class=" + std::string(toString(*preimport_plan.import_class)) +
                ",eligibility=" +
                std::string(toString(preimport_plan.eligibility)));
        appendImportPlanNote("noabi_decl_plan", preimport_plan, proof,
                             resolution);
        if (preimport_plan.eligibility != ImportEligibility::kImportable) {
          rejected_imports.push_back(
              {target_pc, preimport_plan.rejection_reason,
               preimport_plan.rejection_detail});
        }
        rememberChildPlan(target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
                          /*enable_recovery_mode=*/false,
                          /*dump_virtual_model=*/true, preimport_plan, false);
        if (preimport_plan.eligibility != ImportEligibility::kImportable) {
          if (preimport_plan.eligibility == ImportEligibility::kRejected)
            exhausted_import_targets.insert(target_pc);
          continue;
        }
        auto plan =
            callbacks.import_executable_child(target_pc, *child,
                                              preimport_plan, "execchild_");
        plan.import_class = preimport_plan.import_class;
        plan.proof = proof;
        if (!plan.selected_root_pc)
          plan.selected_root_pc = preimport_plan.selected_root_pc;
        appendImportPlanNote("noabi_decl_import", plan, proof, resolution);
        if (plan.eligibility != ImportEligibility::kImportable ||
            !plan.imported_root) {
          rejected_imports.push_back(
              {target_pc, plan.rejection_reason, plan.rejection_detail});
        }
        rememberChildPlan(target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
                          /*enable_recovery_mode=*/false,
                          /*dump_virtual_model=*/true, plan,
                          plan.eligibility == ImportEligibility::kImportable &&
                              plan.imported_root != nullptr);
        if (plan.eligibility != ImportEligibility::kImportable ||
            !plan.imported_root) {
          exhausted_import_targets.insert(target_pc);
          continue;
        }
        emitPreciseLog(options, callbacks, "output-recovery",
                       "noabi-declaration-import",
                       "imported declaration-backed executable child",
                       target_pc);
        seen_import_targets.insert(target_pc);
        imported_executable_children.push_back(target_pc);
        ++summary.noabi_imported_children;
      }

      RoundArtifactBundle import_bundle;
      import_bundle.stage = RuntimeArtifactStage::kOutputRecoveryImportRound;
      import_bundle.label = "noabi_executable_children";
      import_bundle.round = import_round;
      import_bundle.changed = !imported_executable_children.empty();
      import_bundle.imported_targets.assign(imported_executable_children.begin(),
                                            imported_executable_children.end());
      import_bundle.rejected_imports = std::move(rejected_imports);
      if (imported_executable_children.empty()) {
        recordArtifactBundle(std::move(import_bundle));
        break;
      }
      auto patched_targets =
          callbacks.patch_declared_lifted_or_block_calls_to_defined_targets(
              imported_executable_children,
              "noabi_imported_executable_child_patch",
              "patched output-root executable placeholders to imported child roots");
      summary.patched_declared_targets += patched_targets;
      rememberCleanupAction(
          "noabi_imported_executable_child_patch", patched_targets != 0,
          (llvm::Twine("patched_targets=") + llvm::Twine(patched_targets))
              .str());
      callbacks.run_final_output_cleanup();
      rememberCleanupAction("noabi_post_import_final_output_cleanup", true,
                            "executed");
      summary.changed = true;
      recordArtifactBundle(std::move(import_bundle));
    }
  }

  if (!options.raw_binary && !options.no_abi &&
      options.allow_abi_postmain_rounds) {
    if (callbacks.sanitize_remaining_poison_native_helper_args) {
      noteAbiStep("sanitize_remaining_poison_native_helper_args", [&] {
        callbacks.sanitize_remaining_poison_native_helper_args();
      });
    }
    if (callbacks.erase_noop_self_recursive_native_calls) {
      noteAbiStep("erase_noop_self_recursive_native_calls", [&] {
        callbacks.erase_noop_self_recursive_native_calls();
      });
    }
    if (callbacks.run_final_output_cleanup) {
      noteAbiStep("initial_final_output_cleanup",
                  [&] { callbacks.run_final_output_cleanup(); });
    }
    if (callbacks.prune_to_defined_output_root_closure) {
      noteAbiStep("initial_prune_defined_output_root_closure", [&] {
        callbacks.prune_to_defined_output_root_closure();
      });
    }
    if (callbacks.run_final_output_cleanup) {
      noteAbiStep("post_prune_final_output_cleanup",
                  [&] { callbacks.run_final_output_cleanup(); });
    }
    if (callbacks.rerun_late_output_root_target_pipeline) {
      noteAbiStep("initial_rerun_late_output_root_target_pipeline", [&] {
        callbacks.rerun_late_output_root_target_pipeline();
      });
    }
    if (callbacks.advance_session_owned_frontier_work &&
        callbacks.advance_session_owned_frontier_work(
            FrontierDiscoveryPhase::kVmUnresolvedContinuations,
            "abi_late_vm_continuations")) {
      if (callbacks.run_final_output_cleanup) {
        noteAbiStep("vm_continuations_final_output_cleanup",
                    [&] { callbacks.run_final_output_cleanup(); });
      }
      if (callbacks.prune_to_defined_output_root_closure) {
        noteAbiStep("vm_continuations_prune_defined_output_root_closure", [&] {
          callbacks.prune_to_defined_output_root_closure();
        });
      }
      if (callbacks.run_final_output_cleanup) {
        noteAbiStep("vm_continuations_post_prune_final_output_cleanup",
                    [&] { callbacks.run_final_output_cleanup(); });
      }
      if (callbacks.rerun_late_output_root_target_pipeline) {
        noteAbiStep("vm_continuations_rerun_late_output_root_target_pipeline",
                    [&] {
                      callbacks.rerun_late_output_root_target_pipeline();
                    });
      }
      summary.changed = true;
    }

    if (block_lifter && iterative_session && frontier_callbacks) {
      std::optional<VmEnterChildImportCallbacks> vm_enter_import_callbacks;
      if (options.enable_nested_vm_enter_child_import &&
          callbacks.lift_child_target && callbacks.import_vm_enter_child) {
        VmEnterChildImportCallbacks import_callbacks;
        import_callbacks.enabled = true;
        import_callbacks.max_imports = options.max_vm_enter_child_imports;
        import_callbacks.try_import_target =
            [&](uint64_t target_pc, llvm::Function &placeholder,
                std::string &failure_reason,
                llvm::Function *&imported_root) -> bool {
              auto child = callbacks.lift_child_target(
                  target_pc, /*no_abi=*/true, /*enable_gsd=*/true,
                  /*enable_recovery_mode=*/true, /*dump_virtual_model=*/true);
              if (!child) {
                emitPreciseLog(options, callbacks, "output-recovery",
                               "abi-vm-enter-lift-failed",
                               "failed to lift vm-enter child", target_pc);
                failure_reason = "child_lift_failed";
                return false;
              }
              auto analyzed_raw_child = analyzeChildLiftArtifactForPlanning(
                  M.getContext(), std::move(*child));
              auto prepared_child = prepareChildLiftArtifact(
                  M.getContext(), analyzed_raw_child, /*no_abi_mode=*/true);
              auto analyzed_child = analyzeChildLiftArtifactForPlanning(
                  M.getContext(), prepared_child.artifact);
              auto selected_child = selectBestChildImportArtifact(
                  M.getContext(), analyzed_raw_child, analyzed_child,
                  ChildRootSelectionMode::kVmEnter);
              analyzed_child = selected_child.artifact;
              auto preimport_plan = selected_child.plan;
              auto plan = callbacks.import_vm_enter_child(
                  target_pc, analyzed_child, preimport_plan, placeholder);
              appendImportPlanNote("abi_vm_enter_import", plan);
              if (plan.eligibility != ImportEligibility::kImportable ||
                  !plan.imported_root) {
                emitPreciseLog(options, callbacks, "output-recovery",
                               "abi-vm-enter-import-rejected",
                               "vm-enter child import rejected", target_pc,
                               std::nullopt,
                               plan.rejection_detail.empty()
                                   ? std::optional<std::string>(toString(
                                         plan.rejection_reason))
                                   : std::optional<std::string>(
                                         plan.rejection_detail));
                failure_reason = plan.rejection_detail.empty()
                                     ? toString(plan.rejection_reason)
                                     : plan.rejection_detail;
                return false;
              }
              emitPreciseLog(options, callbacks, "output-recovery",
                             "abi-vm-enter-import",
                             "imported vm-enter child", target_pc);
              imported_root = plan.imported_root;
              return true;
            };
        import_callbacks.on_imported_target = [&](uint64_t target_pc) {
          if (callbacks.note_imported_target)
            callbacks.note_imported_target(target_pc);
        };
        vm_enter_import_callbacks = std::move(import_callbacks);
      }

      FrontierIterationCallbacks iteration_callbacks;
      iteration_callbacks.after_frontier_round =
          [&](unsigned, const FrontierRoundSummary &round_summary,
              const VmEnterChildImportSummary &import_summary) {
            for (const auto &note : import_summary.notes)
              summary.notes.push_back("abi_late_output_root_closure:" + note);
            summary.abi_imported_vm_enter_children += import_summary.imported;
            const bool imported_vm_enter_children = import_summary.changed;
            if (imported_vm_enter_children)
              summary.changed = true;

            auto final_code_targets =
                callbacks.collect_output_root_constant_code_call_targets
                    ? callbacks.collect_output_root_constant_code_call_targets()
                    : std::vector<uint64_t>{};
            auto final_calli_targets =
                callbacks.collect_output_root_constant_calli_targets
                    ? callbacks.collect_output_root_constant_calli_targets()
                    : std::vector<uint64_t>{};
            auto final_dispatch_targets =
                callbacks.collect_output_root_constant_dispatch_targets
                    ? callbacks.collect_output_root_constant_dispatch_targets()
                    : std::vector<uint64_t>{};

            if (callbacks.patch_constant_inttoptr_calls_to_native)
              callbacks.patch_constant_inttoptr_calls_to_native(
                  final_code_targets, "abi_post_final_constant_code_patch",
                  "patched final constant code callsites");
            if (callbacks.patch_declared_lifted_or_block_calls_to_defined_targets) {
              summary.patched_declared_targets +=
                  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets(
                      final_code_targets, "abi_post_final_declared_code_patch",
                      "patched final declared lifted/block callsites");
            }
            if (callbacks.patch_constant_calli_targets_to_direct_calls) {
              summary.patched_calli_targets +=
                  callbacks.patch_constant_calli_targets_to_direct_calls(
                      final_calli_targets, "abi_post_final_calli_patch",
                      "patched final constant CALLI callsites");
            }
            if (callbacks.patch_constant_dispatch_targets_to_direct_calls) {
              summary.patched_dispatch_targets +=
                  callbacks.patch_constant_dispatch_targets_to_direct_calls(
                      final_dispatch_targets, "abi_post_final_dispatch_patch",
                      "patched final constant dispatch callsites");
            }
            if (!final_code_targets.empty())
              summary.patched_code_targets +=
                  static_cast<unsigned>(final_code_targets.size());

            const bool callback_changed =
                imported_vm_enter_children ||
                summary.patched_declared_targets != 0 ||
                summary.patched_calli_targets != 0 ||
                summary.patched_dispatch_targets != 0 ||
                !final_code_targets.empty();
            if (!round_summary.changed && !callback_changed)
              return false;

            if (callbacks.run_final_output_cleanup) {
              noteAbiStep("late_output_root_final_output_cleanup",
                          [&] { callbacks.run_final_output_cleanup(); });
            }
            if (callbacks.prune_to_defined_output_root_closure) {
              noteAbiStep("late_output_root_prune_defined_output_root_closure",
                          [&] {
                            callbacks.prune_to_defined_output_root_closure();
                          });
            }
            if (callbacks.run_final_output_cleanup) {
              noteAbiStep("late_output_root_post_prune_final_output_cleanup",
                          [&] { callbacks.run_final_output_cleanup(); });
            }
            if (callbacks.run_late_closure_canonicalization) {
              noteAbiStep("late_output_root_canonicalization", [&] {
                callbacks.run_late_closure_canonicalization(
                    "abi_late_output_root_closure");
              });
            }
            if (callbacks.run_post_patch_cleanup) {
              noteAbiStep("late_output_root_post_patch_cleanup", [&] {
                callbacks.run_post_patch_cleanup("abi_late_output_root_closure");
              });
            }
            if (callbacks.annotate_vm_unresolved_continuations)
              callbacks.annotate_vm_unresolved_continuations();
            summary.changed = true;
            return true;
          };

      auto late_summary = runPrimaryDevirtualization(
          M, *block_lifter, *iterative_session, *frontier_callbacks,
          FrontierDiscoveryPhase::kOutputRootClosure,
          options.late_abi_closure_rounds, iteration_callbacks,
          vm_enter_import_callbacks ? &*vm_enter_import_callbacks : nullptr);
      summary.changed |= late_summary.changed;
      RoundArtifactBundle bundle;
      bundle.stage = RuntimeArtifactStage::kOutputRecoveryRound;
      bundle.label = "abi_late_frontier";
      bundle.changed = late_summary.changed;
      for (const auto &import_summary : late_summary.import_summaries) {
        bundle.notes.insert(bundle.notes.end(), import_summary.notes.begin(),
                            import_summary.notes.end());
      }
      recordArtifactBundle(std::move(bundle));
    }
  }

  if (callbacks.collect_declared_structural_targets_with_defined_implementations &&
      callbacks.patch_declared_lifted_or_block_calls_to_defined_targets) {
    auto late_declared_structural_targets =
        callbacks
            .collect_declared_structural_targets_with_defined_implementations();
    if (!late_declared_structural_targets.empty()) {
      auto patched =
          callbacks.patch_declared_lifted_or_block_calls_to_defined_targets(
              late_declared_structural_targets,
              "late_declared_structural_target_patch",
              "patched declared structural targets to late-defined implementations");
      summary.patched_declared_targets += patched;
      rememberCleanupAction(
          "late_declared_structural_target_patch", patched > 0,
          (llvm::Twine("patched_targets=") + llvm::Twine(patched)).str());
      if (patched > 0 && callbacks.run_final_output_cleanup) {
        callbacks.run_final_output_cleanup();
        rememberCleanupAction("late_declared_structural_final_output_cleanup",
                              true, "executed");
        summary.changed = true;
      }
    }
  }

  RoundArtifactBundle final_bundle;
  final_bundle.stage = RuntimeArtifactStage::kOutputRecoveryRound;
  final_bundle.label = options.no_abi ? "output_recovery_noabi_final"
                                      : "output_recovery_abi_final";
  final_bundle.changed = summary.changed;
  final_bundle.notes = summary.notes;
  recordArtifactBundle(std::move(final_bundle));

  return summary;
}

ProtectorValidationReport DevirtualizationRuntime::buildValidationReport(
    const llvm::Module &M) const {
  auto report = orchestrator_.buildProtectorValidationReport(M);
  auto bump = [&](ProtectorValidationIssueClass klass) {
    ++report.counts_by_class[toString(klass)];
  };

  llvm::SmallVector<const llvm::Function *, 8> output_roots;
  for (const auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
        F.hasFnAttribute("omill.internal_output_root")) {
      continue;
    }
    output_roots.push_back(&F);
  }
  if (output_roots.empty()) {
    for (const auto &F : M) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        output_roots.push_back(&F);
    }
  }

  for (const auto *root : output_roots) {
    llvm::SmallVector<const llvm::Function *, 16> worklist = {root};
    llvm::SmallPtrSet<const llvm::Function *, 16> visited;
    while (!worklist.empty()) {
      const auto *current = worklist.pop_back_val();
      if (!current || !visited.insert(current).second)
        continue;
      for (const auto &BB : *current) {
        for (const auto &I : BB) {
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          const auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (!callee)
            continue;
          if (callee->isIntrinsic())
            continue;
          if (callee->isDeclaration()) {
            if (isLoweringHelperCalleeName(callee->getName()))
              continue;
            ProtectorValidationIssue issue;
            issue.root_name = root->getName().str();
            issue.caller_name = current->getName().str();
            issue.callee_name = callee->getName().str();
            if (callee->getName().starts_with("omill_executable_target_")) {
              issue.issue_class =
                  ProtectorValidationIssueClass::kExecutablePlaceholder;
            } else if (callee->getName().starts_with("omill_native_target_") ||
                       callee->getName().starts_with("omill_native_boundary_") ||
                       callee->getName().starts_with("omill_vm_enter_target_")) {
              issue.issue_class =
                  ProtectorValidationIssueClass::kNativeOrVmEnterBoundary;
            } else if (callee->getName() == "__omill_missing_block_handler") {
              issue.issue_class = ProtectorValidationIssueClass::kTerminalEdge;
            } else if (callee->getName().starts_with("__remill_")) {
              issue.issue_class =
                  ProtectorValidationIssueClass::kRemillRuntimeLeak;
            } else {
              issue.issue_class =
                  ProtectorValidationIssueClass::kNativeOrVmEnterBoundary;
            }
            issue.message = issue.caller_name + " -> " + issue.callee_name;
            report.issues.push_back(issue);
            bump(issue.issue_class);
            continue;
          }
          worklist.push_back(callee);
        }
      }
    }
  }

  return report;
}

RecoveryQualitySummary DevirtualizationRuntime::classifyRecoveryQuality(
    const llvm::Module &M) const {
  RoundArtifactBundle bundle;
  populateRoundArtifactBundleFromModule(M, bundle);
  populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                 round_artifact_bundles_);
  bundle.final_tail_graph = buildFinalTailGraph(M);
  augmentRecoveryQualityFromTailGraph(bundle, *bundle.final_tail_graph);
  refineRecoveryQualityFromModuleShape(M, bundle);
  return bundle.recovery_quality;
}

FinalTailGraph DevirtualizationRuntime::buildFinalTailGraph(
    const llvm::Module &M) const {
  FinalTailGraph graph;

  llvm::SmallDenseSet<uint64_t, 16> terminal_modeled_children;
  llvm::SmallDenseSet<uint64_t, 16> terminal_modeled_boundaries;
  llvm::SmallDenseSet<uint64_t, 16> modeled_reentry_boundaries;
  llvm::SmallDenseSet<uint64_t, 16> hard_rejected_targets;

  for (const auto &bundle : round_artifact_bundles_) {
    for (uint64_t pc : bundle.recovery_quality.terminal_modeled_children)
      terminal_modeled_children.insert(pc);
    for (uint64_t pc : bundle.recovery_quality.terminal_modeled_boundaries)
      terminal_modeled_boundaries.insert(pc);
    for (uint64_t pc : bundle.recovery_quality.modeled_reentry_boundaries)
      modeled_reentry_boundaries.insert(pc);
    for (uint64_t pc : bundle.recovery_quality.hard_rejected_targets)
      hard_rejected_targets.insert(pc);
  }
  for (const auto &[key, entry] : child_artifact_cache_) {
    if (!key.no_abi)
      continue;
    if (entry.imported && isTerminalModeledArtifact(entry.artifact))
      terminal_modeled_children.insert(key.target_pc);
    if (entry.last_plan.rejection_reason == RecoveryRejectionReason::kRuntimeLeak ||
        entry.artifact.rejection_reason == RecoveryRejectionReason::kRuntimeLeak ||
        entry.leak_kind != ChildArtifactLeakKind::kNone) {
      hard_rejected_targets.insert(key.target_pc);
    }
  }

  auto resolveBoundaryTarget = [&](uint64_t target_pc)
      -> std::optional<BoundaryResolutionResult> {
    if (auto it = boundary_resolution_cache_.find(target_pc);
        it != boundary_resolution_cache_.end()) {
      return it->second;
    }
    auto boundary = findBoundaryFactForTarget(orchestrator_, &M, target_pc);
    if (!boundary)
      return std::nullopt;
    BoundaryResolutionRequest request;
    request.target_pc = target_pc;
    request.boundary = boundary;
    request.proof = findContinuationProofForTarget(orchestrator_, target_pc);
    BoundaryContinuationResolver resolver;
    auto result = resolver.resolve(request);
    boundary_resolution_cache_[target_pc] = result;
    return result;
  };

  auto findDeclaredTailSymbol = [&](uint64_t target_pc) -> std::string {
    for (const auto &F : M) {
      if (extractStructuralCodeTargetPC(F) != target_pc)
        continue;
      if (isTailPlaceholderDeclarationName(F.getName()) ||
          F.getFnAttribute(kTailGraphKindAttr).isValid()) {
        return F.getName().str();
      }
    }
    return {};
  };

  auto classifyNode = [&](uint64_t target_pc, llvm::StringRef symbol_name,
                          bool terminal_child_hint) {
    FinalTailGraphNode node;
    node.target_pc = target_pc;
    node.symbol_name = symbol_name.str();
    const bool is_native_target_symbol =
        symbol_name.starts_with("omill_native_target_");
    const bool is_vm_enter_symbol =
        symbol_name.starts_with("omill_vm_enter_target_");

    auto explicit_kind_attr = [&]() -> std::optional<FinalTailNodeKind> {
      if (node.symbol_name.empty())
        return std::nullopt;
      if (auto *F = M.getFunction(node.symbol_name)) {
        if (auto attr = F->getFnAttribute(kTailGraphKindAttr);
            attr.isValid() && attr.isStringAttribute()) {
          return parseFinalTailNodeKind(attr.getValueAsString());
        }
      }
      return std::nullopt;
    }();
    if (explicit_kind_attr) {
      node.kind = *explicit_kind_attr;
      if (auto *F = M.getFunction(node.symbol_name)) {
        if (auto attr = F->getFnAttribute(kTailGraphDetailAttr);
            attr.isValid() && attr.isStringAttribute()) {
          node.detail = attr.getValueAsString().str();
        }
        if (auto attr = F->getFnAttribute(kTailGraphContinuationAttr);
            attr.isValid() && attr.isStringAttribute()) {
          llvm::StringRef text = attr.getValueAsString();
          if (text.consume_front("0x"))
            ;
          uint64_t continuation_pc = 0;
          if (!text.empty() && !text.getAsInteger(16, continuation_pc) &&
              continuation_pc) {
            node.continuation_pc = continuation_pc;
          }
        }
      }
      return node;
    }

    if (terminal_child_hint || terminal_modeled_children.contains(target_pc)) {
      node.kind = FinalTailNodeKind::kTerminalModeledChild;
      node.detail = "terminal_modeled_child";
      return node;
    }

    const bool is_boundary_symbol =
        isBoundaryTailDeclarationName(symbol_name) ||
        modeled_reentry_boundaries.contains(target_pc) ||
        terminal_modeled_boundaries.contains(target_pc);
    if (is_boundary_symbol) {
      auto boundary_for_control =
          findBoundaryFactForTarget(orchestrator_, &M, target_pc);
      const bool has_controlled_return =
          boundary_for_control &&
          boundary_for_control->suppresses_normal_fallthrough;
      const bool has_intra_owner_continuation =
          boundary_for_control &&
          (boundary_for_control->covered_entry_pc.has_value() ||
           boundary_for_control->continuation_entry_transform.has_value());
      if (hard_rejected_targets.contains(target_pc)) {
        node.kind = FinalTailNodeKind::kHardRejectedBoundary;
        node.detail = "hard_rejected_boundary";
        return node;
      }
      if (terminal_modeled_boundaries.contains(target_pc)) {
        node.kind = FinalTailNodeKind::kTerminalModeledBoundary;
        node.detail = "terminal_modeled_boundary";
        return node;
      }
      if (modeled_reentry_boundaries.contains(target_pc)) {
        node.kind = FinalTailNodeKind::kModeledReentryBoundary;
        if (has_controlled_return) {
          node.detail = "modeled_controlled_return";
        } else if (has_intra_owner_continuation) {
          node.detail = "modeled_intra_owner_continuation";
        } else {
          node.detail = "modeled_reentry_boundary";
        }
        if (auto boundary_result = resolveBoundaryTarget(target_pc);
            boundary_result && boundary_result->boundary &&
            effectiveBoundaryContinuationPc(*boundary_result->boundary)) {
          node.continuation_pc =
              effectiveBoundaryContinuationPc(*boundary_result->boundary);
        } else if (auto boundary = findBoundaryFactForTarget(orchestrator_, &M,
                                                             target_pc);
                   boundary && effectiveBoundaryContinuationPc(*boundary)) {
          node.continuation_pc = effectiveBoundaryContinuationPc(*boundary);
        }
        return node;
      }
      if (is_vm_enter_symbol) {
        node.kind = FinalTailNodeKind::kModeledReentryBoundary;
        if (has_controlled_return) {
          node.detail = "modeled_controlled_return";
        } else if (has_intra_owner_continuation) {
          node.detail = "modeled_intra_owner_continuation";
        } else {
          node.detail = "modeled_reentry_boundary";
        }
        if (auto boundary = findBoundaryFactForTarget(orchestrator_, &M,
                                                      target_pc);
            boundary && effectiveBoundaryContinuationPc(*boundary)) {
          node.continuation_pc = effectiveBoundaryContinuationPc(*boundary);
        }
        return node;
      }
      if (auto boundary_result = resolveBoundaryTarget(target_pc)) {
        switch (boundary_result->disposition) {
          case BoundaryResolutionDisposition::kModeledReentryBoundary:
            node.kind = FinalTailNodeKind::kModeledReentryBoundary;
            if (has_controlled_return) {
              node.detail = "modeled_controlled_return";
            } else if (has_intra_owner_continuation) {
              node.detail = "modeled_intra_owner_continuation";
            } else {
              node.detail = "modeled_reentry_boundary";
            }
            if (boundary_result->boundary &&
                effectiveBoundaryContinuationPc(*boundary_result->boundary)) {
              node.continuation_pc =
                  effectiveBoundaryContinuationPc(*boundary_result->boundary);
            }
            return node;
          case BoundaryResolutionDisposition::kModeledTerminalBoundary:
            node.kind = FinalTailNodeKind::kTerminalModeledBoundary;
            node.detail = "terminal_modeled_boundary";
            return node;
          case BoundaryResolutionDisposition::kHardRejectedUnsupportedBoundary:
            node.kind = FinalTailNodeKind::kHardRejectedBoundary;
            node.detail = "hard_rejected_boundary";
            return node;
          case BoundaryResolutionDisposition::kRetryableBoundaryRecovery:
            node.kind = FinalTailNodeKind::kRetryableBoundary;
            node.detail = boundary_result->rationale.empty()
                              ? "retryable_boundary"
                              : boundary_result->rationale;
            return node;
        }
      }
      if (has_controlled_return &&
          (!boundary_for_control ||
           !effectiveBoundaryContinuationPc(*boundary_for_control))) {
        node.kind = FinalTailNodeKind::kRetryableBoundary;
        node.detail = "controlled_return_unresolved";
        return node;
      }
      if (is_native_target_symbol) {
        node.kind = FinalTailNodeKind::kRetryableBoundary;
        node.detail = "retryable_boundary";
        return node;
      }
      node.kind = FinalTailNodeKind::kRetryableBoundary;
      node.detail = "retryable_boundary";
      return node;
    }

    if (hard_rejected_targets.contains(target_pc)) {
      node.kind = FinalTailNodeKind::kHardRejectedExecutable;
      node.detail = "hard_rejected_executable";
      return node;
    }

    node.kind = FinalTailNodeKind::kExecutablePlaceholder;
    node.detail = "executable_placeholder";
    return node;
  };

  auto addOrUpdateNode = [&](const FinalTailGraphNode &node) {
    auto it = llvm::find_if(graph.nodes, [&](const FinalTailGraphNode &existing) {
      return existing.target_pc == node.target_pc;
    });
    if (it == graph.nodes.end()) {
      graph.nodes.push_back(node);
      return;
    }
    if (finalTailNodePriority(node.kind) < finalTailNodePriority(it->kind)) {
      it->kind = node.kind;
      it->detail = node.detail;
    }
    if (it->symbol_name.empty() && !node.symbol_name.empty())
      it->symbol_name = node.symbol_name;
    if (!it->continuation_pc && node.continuation_pc)
      it->continuation_pc = node.continuation_pc;
  };

  auto addEdge = [&](std::optional<uint64_t> source_pc, llvm::StringRef source_name,
                     uint64_t target_pc) {
    if (!target_pc)
      return;
    if (llvm::any_of(graph.edges, [&](const FinalTailGraphEdge &existing) {
          return existing.source_pc == source_pc &&
                 existing.source_name == source_name && existing.target_pc == target_pc;
        })) {
      return;
    }
    FinalTailGraphEdge edge;
    edge.source_pc = source_pc;
    edge.source_name = source_name.str();
    edge.target_pc = target_pc;
    graph.edges.push_back(std::move(edge));
  };

  for (const auto &F : M) {
    if (auto attr = F.getFnAttribute(kTailGraphTargetsAttr);
        attr.isValid() && attr.isStringAttribute()) {
      auto targets = parseTailTargetListAttr(attr.getValueAsString());
      auto source_pc = extractTailGraphSourcePC(F);
      for (uint64_t target_pc : targets) {
        auto symbol_name = findDeclaredTailSymbol(target_pc);
        addOrUpdateNode(classifyNode(target_pc, symbol_name, false));
        addEdge(source_pc, F.getName(), target_pc);
      }
    }
    if (!F.getFnAttribute(kTailGraphKindAttr).isValid())
      continue;
    const uint64_t target_pc = extractStructuralCodeTargetPC(F);
    if (!target_pc)
      continue;
    auto node = classifyNode(target_pc, F.getName(), false);
    if (auto attr = F.getFnAttribute(kTailGraphDetailAttr);
        attr.isValid() && attr.isStringAttribute()) {
      node.detail = attr.getValueAsString().str();
    }
    addOrUpdateNode(node);
  }

  auto output_roots = collectArtifactOutputRoots(M);
  for (const auto *root : output_roots) {
    llvm::SmallVector<const llvm::Function *, 16> worklist = {root};
    llvm::SmallPtrSet<const llvm::Function *, 16> visited;
    while (!worklist.empty()) {
      const auto *current = worklist.pop_back_val();
      if (!current || !visited.insert(current).second)
        continue;
      const auto source_pc = extractTailGraphSourcePC(*current);

      for (const auto &BB : *current) {
        for (const auto &I : BB) {
          const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          const auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (!callee || callee->isIntrinsic())
            continue;

          if (callee->isDeclaration() &&
              isTailPlaceholderDeclarationName(callee->getName())) {
            const uint64_t target_pc = extractStructuralCodeTargetPC(*callee);
            if (!target_pc)
              continue;
            addOrUpdateNode(classifyNode(target_pc, callee->getName(), false));
            addEdge(source_pc, current->getName(), target_pc);
            continue;
          }

          if (!callee->isDeclaration()) {
            if (auto callee_pc = extractTailGraphSourcePC(*callee);
                callee_pc && terminal_modeled_children.contains(*callee_pc)) {
              addOrUpdateNode(
                  classifyNode(*callee_pc, callee->getName(), true));
              addEdge(source_pc, current->getName(), *callee_pc);
            }
            worklist.push_back(callee);
          }
        }
      }
    }
  }

  llvm::sort(graph.nodes, [](const FinalTailGraphNode &lhs,
                             const FinalTailGraphNode &rhs) {
    return lhs.target_pc < rhs.target_pc;
  });
  llvm::sort(graph.edges, [](const FinalTailGraphEdge &lhs,
                             const FinalTailGraphEdge &rhs) {
    if (lhs.source_pc != rhs.source_pc)
      return lhs.source_pc < rhs.source_pc;
    if (lhs.source_name != rhs.source_name)
      return lhs.source_name < rhs.source_name;
    return lhs.target_pc < rhs.target_pc;
  });
  return graph;
}

bool DevirtualizationRuntime::refineFinalTailGraphWithBoundaryReplay(
    llvm::Module &M, FinalTailGraph &graph,
    const OutputRecoveryCallbacks &callbacks, bool enable_gsd) const {
  bool changed = false;
  for (auto &node : graph.nodes) {
    if (node.kind != FinalTailNodeKind::kRetryableBoundary &&
        node.kind != FinalTailNodeKind::kModeledReentryBoundary &&
        node.kind != FinalTailNodeKind::kTerminalModeledBoundary) {
      continue;
    }

    auto boundary = findBoundaryFactForTarget(orchestrator_, &M, node.target_pc);
    if (boundary) {
      BoundaryResolutionRequest request;
      request.target_pc = node.target_pc;
      request.boundary = boundary;
      request.proof = findContinuationProofForTarget(orchestrator_, node.target_pc);
      BoundaryContinuationResolver resolver;
      auto result = resolver.resolve(request);
      FinalTailNodeKind new_kind = node.kind;
      std::string new_detail = node.detail;
      switch (result.disposition) {
        case BoundaryResolutionDisposition::kModeledReentryBoundary:
          new_kind = FinalTailNodeKind::kModeledReentryBoundary;
          new_detail = "modeled_reentry_boundary";
          if (result.boundary && result.boundary->continuation_pc)
            node.continuation_pc = result.boundary->continuation_pc;
          break;
        case BoundaryResolutionDisposition::kModeledTerminalBoundary:
          new_kind = FinalTailNodeKind::kTerminalModeledBoundary;
          new_detail = "terminal_modeled_boundary";
          break;
        case BoundaryResolutionDisposition::kHardRejectedUnsupportedBoundary:
          new_kind = FinalTailNodeKind::kHardRejectedBoundary;
          new_detail = "hard_rejected_boundary";
          break;
        case BoundaryResolutionDisposition::kRetryableBoundaryRecovery:
          new_kind = FinalTailNodeKind::kRetryableBoundary;
          new_detail = result.rationale.empty() ? "retryable_boundary"
                                                : result.rationale;
          break;
      }
      const bool preserve_modeled_reentry =
          node.kind == FinalTailNodeKind::kModeledReentryBoundary &&
          new_kind != FinalTailNodeKind::kTerminalModeledBoundary &&
          (boundaryHasReentryEvidence(*boundary) ||
           llvm::StringRef(node.symbol_name).starts_with(
               "omill_vm_enter_target_"));
      if (preserve_modeled_reentry) {
        new_kind = FinalTailNodeKind::kModeledReentryBoundary;
        new_detail = "modeled_reentry_boundary";
      }
      if (new_kind != node.kind || new_detail != node.detail) {
        node.kind = new_kind;
        node.detail = new_detail;
        changed = true;
      }
      if (new_kind != FinalTailNodeKind::kRetryableBoundary)
        continue;
    }

    if (node.kind == FinalTailNodeKind::kModeledReentryBoundary) {
      continue;
    }

    if (!callbacks.lift_child_target)
      continue;

    auto child_artifact = callbacks.lift_child_target(
        node.target_pc, /*no_abi=*/true, enable_gsd,
        /*enable_recovery_mode=*/true, /*dump_virtual_model=*/true);
    if (!child_artifact || child_artifact->ir_text.empty())
      continue;

    llvm::LLVMContext temp_ctx;
    auto analyzed_raw_artifact =
        analyzeChildLiftArtifact(temp_ctx, *child_artifact);
    auto prepared = prepareChildLiftArtifact(temp_ctx, *child_artifact,
                                             /*no_abi_mode=*/true);
    auto prepared_artifact =
        analyzeChildLiftArtifact(temp_ctx, prepared.artifact);
    const auto leak_kind = classifyLeakKind(prepared_artifact);
    const auto jump_tail_continuation_pc =
        prepared_artifact.jump_tail_continuation_pc
            ? prepared_artifact.jump_tail_continuation_pc
            : analyzed_raw_artifact.jump_tail_continuation_pc;
    const bool has_local_controlled_return =
        prepared_artifact.has_local_controlled_return ||
        analyzed_raw_artifact.has_local_controlled_return;

    FinalTailNodeKind new_kind = node.kind;
    std::string new_detail = node.detail;
    if (isJumpContinuationTailArtifact(prepared_artifact) &&
        has_local_controlled_return &&
        jump_tail_continuation_pc) {
      new_kind = FinalTailNodeKind::kModeledReentryBoundary;
      new_detail = "modeled_controlled_return";
      node.continuation_pc = jump_tail_continuation_pc;
    } else if (isJumpContinuationTailArtifact(prepared_artifact) &&
               has_local_controlled_return) {
      new_kind = FinalTailNodeKind::kRetryableBoundary;
      new_detail = "controlled_return_unresolved";
      node.continuation_pc.reset();
    } else if (isJumpContinuationTailArtifact(prepared_artifact) &&
               jump_tail_continuation_pc) {
      new_kind = FinalTailNodeKind::kModeledReentryBoundary;
      new_detail = "jump_tail_modeled_reentry_boundary";
      node.continuation_pc = jump_tail_continuation_pc;
    } else if (isJumpContinuationTailArtifact(prepared_artifact)) {
      new_kind = FinalTailNodeKind::kRetryableBoundary;
      new_detail = "jump_tail_retryable_boundary";
    } else if (leak_kind != ChildArtifactLeakKind::kNone ||
               prepared_artifact.rejection_reason ==
                   RecoveryRejectionReason::kRuntimeLeak) {
      new_kind = FinalTailNodeKind::kHardRejectedBoundary;
      new_detail = ("runtime_leak:" + toString(leak_kind));
    } else if (prepared_artifact.selected_root_is_terminal_modeled ||
               prepared_artifact.rejection_detail == "terminal_modeled_child" ||
               prepared_artifact.rejection_detail == "terminal_only_child") {
      new_kind = FinalTailNodeKind::kTerminalModeledBoundary;
      new_detail = "terminal_modeled_boundary";
    } else {
      new_kind = FinalTailNodeKind::kRetryableBoundary;
      new_detail = prepared.summary.detail.empty()
                       ? "retryable_boundary"
                       : prepared.summary.detail;
    }

    if (new_kind != node.kind || new_detail != node.detail) {
      node.kind = new_kind;
      node.detail = new_detail;
      changed = true;
    }
  }

  llvm::sort(graph.nodes, [](const FinalTailGraphNode &lhs,
                             const FinalTailGraphNode &rhs) {
    return lhs.target_pc < rhs.target_pc;
  });
  return changed;
}

bool DevirtualizationRuntime::projectFinalTailGraphIntoAbiModule(
    llvm::Module &M, const FinalTailGraph &graph) const {
  if (graph.nodes.empty() && graph.edges.empty())
    return false;

  auto &Ctx = M.getContext();
  auto *ptr_ty = llvm::PointerType::getUnqual(Ctx);
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, llvm::Type::getInt64Ty(Ctx), ptr_ty},
                              false);
  bool changed = false;

  auto ensureFunction = [&](llvm::StringRef name) -> llvm::Function * {
    if (auto *existing = M.getFunction(name))
      return existing;
    changed = true;
    return llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage, name, M);
  };

  for (const auto &node : graph.nodes) {
    auto *F = ensureFunction(defaultTailSymbolName(node));
    if (auto attr = F->getFnAttribute(kTailGraphKindAttr);
        !attr.isValid() || attr.getValueAsString() != toString(node.kind)) {
      F->addFnAttr(kTailGraphKindAttr, toString(node.kind));
      changed = true;
    }
    if (!node.detail.empty()) {
      if (auto attr = F->getFnAttribute(kTailGraphDetailAttr);
          !attr.isValid() || attr.getValueAsString() != node.detail) {
        F->addFnAttr(kTailGraphDetailAttr, node.detail);
        changed = true;
      }
    }
    if (node.continuation_pc) {
      const std::string value =
          (llvm::Twine("0x") + llvm::utohexstr(*node.continuation_pc)).str();
      if (auto attr = F->getFnAttribute(kTailGraphContinuationAttr);
          !attr.isValid() || attr.getValueAsString() != value) {
        F->addFnAttr(kTailGraphContinuationAttr, value);
        changed = true;
      }
    }
  }

  std::map<std::pair<uint64_t, std::string>, std::vector<uint64_t>> grouped_targets;
  for (const auto &edge : graph.edges) {
    grouped_targets[{edge.source_pc.value_or(0), edge.source_name}].push_back(
        edge.target_pc);
  }

  auto summarizeTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    std::string summary;
    llvm::raw_string_ostream os(summary);
    bool first = true;
    for (uint64_t target_pc : targets) {
      auto it = llvm::find_if(graph.nodes, [&](const FinalTailGraphNode &node) {
        return node.target_pc == target_pc;
      });
      if (!first)
        os << ",";
      first = false;
      os << "0x" << llvm::utohexstr(target_pc);
      if (it != graph.nodes.end())
        os << ":" << toString(it->kind);
    }
    return summary;
  };

  for (auto &[key, targets] : grouped_targets) {
    llvm::sort(targets);
    targets.erase(std::unique(targets.begin(), targets.end()), targets.end());

    llvm::SmallVector<llvm::Function *, 4> matches;
    for (auto &F : M) {
      if (key.first != 0) {
        if (auto pc = extractTailGraphSourcePC(F); pc && *pc == key.first) {
          matches.push_back(&F);
          continue;
        }
      }
      if (!key.second.empty() && F.getName() == key.second)
        matches.push_back(&F);
    }

    if (matches.empty() && key.first != 0) {
      auto synthetic_name = "blk_" + llvm::utohexstr(key.first);
      auto *synthetic = ensureFunction(synthetic_name);
      matches.push_back(synthetic);
    }

    const auto targets_attr = joinTailTargetList(targets);
    const auto summary_attr = summarizeTargets(targets);
    for (auto *F : matches) {
      if (auto attr = F->getFnAttribute(kTailGraphTargetsAttr);
          !attr.isValid() || attr.getValueAsString() != targets_attr) {
        F->addFnAttr(kTailGraphTargetsAttr, targets_attr);
        changed = true;
      }
      if (auto attr = F->getFnAttribute(kTailGraphSummaryAttr);
          !attr.isValid() || attr.getValueAsString() != summary_attr) {
        F->addFnAttr(kTailGraphSummaryAttr, summary_attr);
        changed = true;
      }
    }
  }

  return changed;
}

FinalizationSummary DevirtualizationRuntime::finalizeOutput(
    const llvm::Module &M, bool devirtualization_enabled) const {
  FinalizationSummary summary;
  RoundArtifactBundle bundle;
  bundle.stage = RuntimeArtifactStage::kFinalization;
  bundle.label = "finalize_output";
  bundle.changed = false;
  if (devirtualization_enabled) {
    summary.protector_report = buildValidationReport(M);
    summary.has_protector_report = true;
    bundle.cleanup_actions.push_back(
        makeCleanupActionArtifact("build_validation_report", false, "executed"));
    for (const auto &issue : summary.protector_report.issues) {
      bundle.notes.push_back(issue.message);
    }
  }
  populateRoundArtifactBundleFromModule(M, bundle);
  populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                round_artifact_bundles_);
  bundle.final_tail_graph = buildFinalTailGraph(M);
  augmentRecoveryQualityFromTailGraph(bundle, *bundle.final_tail_graph);
  refineRecoveryQualityFromModuleShape(M, bundle);
  summary.recovery_quality = bundle.recovery_quality;
  summary.final_tail_graph = bundle.final_tail_graph;
  summary.artifact_bundles.push_back(bundle);
  round_artifact_bundles_.push_back(bundle);
  return summary;
}

std::optional<FinalStateRecoveryPlan>
DevirtualizationRuntime::planFinalStateRecovery(
    const llvm::Module &M, const FinalStateRecoveryRequest &request) const {
  (void)M;
  if (!request.enabled || !request.no_abi || round_artifact_bundles_.empty())
    return std::nullopt;

  const auto &final_bundle = round_artifact_bundles_.back();
  FinalStateRecoveryPlan plan;

  auto findCacheEntry = [&](uint64_t target_pc)
      -> const ChildArtifactCacheEntry * {
    for (const auto &[key, entry] : child_artifact_cache_) {
      if (key.target_pc == target_pc && key.no_abi)
        return &entry;
    }
    return nullptr;
  };

  auto addAction = [&](FinalStateRecoveryAction action) {
    if (!action.target_pc)
      return;
    if (llvm::any_of(plan.actions, [&](const FinalStateRecoveryAction &existing) {
          return existing.target_pc == action.target_pc;
        })) {
      return;
    }
    plan.actions.push_back(std::move(action));
  };

  auto findLatestImportDecision =
      [&](uint64_t target_pc) -> const ImportDecisionArtifact * {
    for (auto bundle_it = round_artifact_bundles_.rbegin();
         bundle_it != round_artifact_bundles_.rend(); ++bundle_it) {
      for (auto decision_it = bundle_it->import_decisions.rbegin();
           decision_it != bundle_it->import_decisions.rend(); ++decision_it) {
        if (decision_it->target_pc == target_pc)
          return &*decision_it;
      }
    }
    return nullptr;
  };

  auto resolveBoundaryTarget = [&](uint64_t target_pc)
      -> std::optional<BoundaryResolutionResult> {
    if (auto it = boundary_resolution_cache_.find(target_pc);
        it != boundary_resolution_cache_.end()) {
      return it->second;
    }
    auto boundary = findBoundaryFactForTarget(orchestrator_, &M, target_pc);
    if (!boundary)
      return std::nullopt;
    BoundaryResolutionRequest request;
    request.target_pc = target_pc;
    request.boundary = boundary;
    request.proof = findContinuationProofForTarget(orchestrator_, target_pc);
    BoundaryContinuationResolver resolver;
    auto result = resolver.resolve(request);
    boundary_resolution_cache_[target_pc] = result;
    return result;
  };

  for (uint64_t target_pc : final_bundle.executable_placeholder_targets) {
    if (wasTargetImportedAcrossBundles(round_artifact_bundles_, target_pc))
      continue;

    auto proof = findContinuationProofForTarget(orchestrator_, target_pc);
    if (isQuarantinedProof(proof))
      continue;

    FinalStateRecoveryAction action;
    action.target_pc = target_pc;
    action.source_stage = final_bundle.stage;
    action.source_label = final_bundle.label;
    action.final_state_class = "executable_placeholder";
    action.planned_resolver_path = "continuation_proof+child_artifact_cache";

    const auto *cache_entry = findCacheEntry(target_pc);
    const auto *latest_decision = findLatestImportDecision(target_pc);
    if (cache_entry &&
        (cache_entry->artifact.rejection_detail == "terminal_modeled_child" ||
         (cache_entry->artifact.selected_root_is_terminal_modeled &&
          cache_entry->leak_kind == ChildArtifactLeakKind::kNone))) {
      action.kind = FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
      action.reason = "terminal_modeled_child";
      action.retry_budget = 0;
      action.expected_outcome = "preserve explicit terminal modeled child";
      addAction(std::move(action));
      continue;
    }
    if (cache_entry &&
        ((cache_entry->raw_artifact.rejection_reason ==
              RecoveryRejectionReason::kRuntimeLeak &&
          cache_entry->artifact.rejection_reason !=
              RecoveryRejectionReason::kRuntimeLeak &&
          cache_entry->leak_kind == ChildArtifactLeakKind::kNone) ||
         cache_entry->last_plan.rejection_reason ==
             RecoveryRejectionReason::kRuntimeLeak ||
         cache_entry->artifact.rejection_reason ==
             RecoveryRejectionReason::kRuntimeLeak ||
         cache_entry->leak_kind != ChildArtifactLeakKind::kNone)) {
      if (cache_entry->raw_artifact.rejection_reason ==
              RecoveryRejectionReason::kRuntimeLeak &&
          cache_entry->artifact.rejection_reason !=
              RecoveryRejectionReason::kRuntimeLeak &&
          cache_entry->leak_kind == ChildArtifactLeakKind::kNone) {
        action.kind =
            FinalStateRecoveryActionKind::kRetryExecutableChildImport;
        action.reason = "runtime_leak_cleared_after_preparation";
        action.retry_budget = 1;
        action.expected_outcome = "import child after leak-free recheck";
      } else if (cache_entry->leak_kind == ChildArtifactLeakKind::kNone) {
        action.kind =
            FinalStateRecoveryActionKind::kRetryExecutableChildImport;
        action.reason = "runtime_leak_cleared_after_cleanup";
        action.retry_budget = 1;
        action.expected_outcome = "import child after leak-free recheck";
      } else {
        action.kind = FinalStateRecoveryActionKind::kHardReject;
        action.reason = ("runtime_leak:" + toString(cache_entry->leak_kind));
        action.retry_budget = 0;
        action.expected_outcome = "preserve explicit hard reject";
      }
      addAction(std::move(action));
      continue;
    }
    if (latest_decision &&
        (latest_decision->rejection_reason ==
             RecoveryRejectionReason::kRuntimeLeak ||
         latest_decision->detail.find("remill_") != std::string::npos)) {
      action.kind = FinalStateRecoveryActionKind::kHardReject;
      action.reason = latest_decision->detail.empty()
                          ? "runtime_leak"
                          : "runtime_leak:" + latest_decision->detail;
      action.retry_budget = 0;
      action.expected_outcome = "preserve explicit hard reject";
      addAction(std::move(action));
      continue;
    }

    const bool terminal_retry =
        (cache_entry &&
         (cache_entry->artifact.import_safety ==
              ChildImportClass::kTerminalOnlyUnknown ||
          cache_entry->artifact.rejection_detail == "terminal_only_child" ||
          cache_entry->last_plan.rejection_detail == "terminal_only_child")) ||
        (latest_decision &&
         (latest_decision->detail == "terminal_only_child" ||
          latest_decision->rejection_reason ==
              RecoveryRejectionReason::kNotSelfContained)) ||
        (proof &&
         proof->import_disposition == ContinuationImportDisposition::kRetryable &&
         proof->resolution_kind == ContinuationResolutionKind::kTerminalModeled);

    if (terminal_retry) {
      action.kind =
          FinalStateRecoveryActionKind::kRetryTerminalExecutableChild;
      action.reason = "retryable_terminal_only_child";
      action.retry_budget = 1;
      action.expected_outcome =
          "import child if proof or cache now classifies it as importable";
      addAction(std::move(action));
      continue;
    }

    if ((cache_entry &&
         cache_entry->last_plan.eligibility == ImportEligibility::kRetryable) ||
        (proof &&
         proof->import_disposition == ContinuationImportDisposition::kRetryable)) {
      action.kind = FinalStateRecoveryActionKind::kRetryExecutableChildImport;
      action.reason = "retryable_executable_child";
      action.retry_budget = 1;
      action.expected_outcome = "retry child import with current cache state";
      addAction(std::move(action));
      continue;
    }

    action.kind = FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
    action.reason = "no_retryable_executable_recovery_path";
    action.retry_budget = 0;
    action.expected_outcome = "keep modeled executable placeholder";
    addAction(std::move(action));
  }

  for (uint64_t target_pc : final_bundle.native_boundary_targets) {
    FinalStateRecoveryAction action;
    action.target_pc = target_pc;
    action.source_stage = final_bundle.stage;
    action.source_label = final_bundle.label;
    action.final_state_class = "native_boundary";
    action.planned_resolver_path = "boundary_continuation_resolver";
    auto boundary_resolution = resolveBoundaryTarget(target_pc);
    if (boundary_resolution &&
        boundary_resolution->disposition ==
            BoundaryResolutionDisposition::kModeledReentryBoundary) {
      action.kind = FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
      action.reason = "modeled_reentry_boundary";
      action.retry_budget = 0;
      action.expected_outcome = "preserve explicit modeled reentry boundary";
    } else if (boundary_resolution &&
               boundary_resolution->disposition ==
                   BoundaryResolutionDisposition::kModeledTerminalBoundary) {
      action.kind = FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
      action.reason = "modeled_terminal_boundary";
      action.retry_budget = 0;
      action.expected_outcome = "preserve explicit modeled terminal boundary";
    } else if (boundary_resolution &&
               boundary_resolution->disposition ==
                   BoundaryResolutionDisposition::kRetryableBoundaryRecovery) {
      action.kind =
          FinalStateRecoveryActionKind::kRetryNativeBoundaryRecovery;
      action.reason = boundary_resolution->rationale;
      action.retry_budget = 1;
      action.expected_outcome =
          "recheck boundary eligibility and preserve explicit modeled boundary";
    } else if (boundary_resolution) {
      action.kind = FinalStateRecoveryActionKind::kHardReject;
      action.reason = boundary_resolution->rationale.empty()
                          ? "unsupported_boundary"
                          : boundary_resolution->rationale;
      action.retry_budget = 0;
      action.expected_outcome = "preserve explicit hard reject";
    } else {
      action.kind = FinalStateRecoveryActionKind::kKeepModeledPlaceholder;
      action.reason = "boundary_has_no_reentry_evidence";
      action.retry_budget = 0;
      action.expected_outcome = "keep modeled native boundary";
    }
    addAction(std::move(action));
  }

  llvm::sort(plan.actions, [](const FinalStateRecoveryAction &lhs,
                              const FinalStateRecoveryAction &rhs) {
    const auto lhs_priority = finalStateRecoveryPriority(lhs.kind);
    const auto rhs_priority = finalStateRecoveryPriority(rhs.kind);
    if (lhs_priority != rhs_priority)
      return lhs_priority < rhs_priority;
    return lhs.target_pc < rhs.target_pc;
  });

  return plan;
}

std::optional<RoundArtifactBundle> DevirtualizationRuntime::runBoundaryTailRecovery(
    llvm::Module &M, const FinalStateRecoveryRequest &request,
    const OutputRecoveryCallbacks &callbacks) const {
  if (!request.enabled || !request.no_abi)
    return std::nullopt;

  auto original_graph = buildFinalTailGraph(M);
  const bool has_boundary_nodes = llvm::any_of(
      original_graph.nodes, [](const FinalTailGraphNode &node) {
        switch (node.kind) {
          case FinalTailNodeKind::kModeledReentryBoundary:
          case FinalTailNodeKind::kRetryableBoundary:
          case FinalTailNodeKind::kTerminalModeledBoundary:
          case FinalTailNodeKind::kHardRejectedBoundary:
            return true;
          case FinalTailNodeKind::kExecutablePlaceholder:
          case FinalTailNodeKind::kTerminalModeledChild:
          case FinalTailNodeKind::kHardRejectedExecutable:
            return false;
        }
        return false;
      });
  if (!has_boundary_nodes)
    return std::nullopt;

  std::map<uint64_t, FinalTailNodeKind> original_kinds;
  for (const auto &node : original_graph.nodes)
    original_kinds[node.target_pc] = node.kind;

  FinalTailGraph graph = original_graph;
  RoundArtifactBundle bundle;
  bundle.stage = RuntimeArtifactStage::kFinalization;
  bundle.label = request.no_abi ? "boundary_tail_recovery_noabi"
                                : "boundary_tail_recovery";
  bundle.changed = refineFinalTailGraphWithBoundaryReplay(
      M, graph, callbacks, request.enable_gsd);
  llvm::SmallVector<uint64_t, 8> lifted_boundary_targets;
  auto &vm_enter_import_attempt_cache = vm_enter_child_import_plan_cache_;
  auto noteBoundaryCleanup = [&](llvm::StringRef label) {
    if (!callbacks.run_final_output_cleanup)
      return;
    callbacks.run_final_output_cleanup();
    bundle.cleanup_actions.push_back(
        makeCleanupActionArtifact(label, true, "executed"));
  };
  auto importSeededVmEnterChildren = [&]() {
    if (!callbacks.lift_child_target || !callbacks.import_vm_enter_child)
      return false;

    for (const auto &[identity, edge] :
         orchestrator_.session().graph.edge_facts_by_identity) {
      (void)identity;
      if (!edge.target_pc ||
          edge.status != FrontierWorkStatus::kClassifiedVmEnter) {
        continue;
      }
      if (orchestrator_.session().imported_vm_enter_child_roots.count(
              *edge.target_pc) != 0) {
        continue;
      }
      const uint64_t cache_target =
          canonicalizeVmEnterImportTarget(M, *edge.target_pc);
      if (vm_enter_import_attempt_cache.count(cache_target) != 0)
        continue;
      orchestrator_.session().attempted_vm_enter_child_import_pcs.erase(
          *edge.target_pc);
      if (cache_target != *edge.target_pc) {
        orchestrator_.session().attempted_vm_enter_child_import_pcs.erase(
            cache_target);
      }
    }

    VmEnterChildImportCallbacks import_callbacks;
    import_callbacks.enabled = true;
    import_callbacks.max_imports = 4;
    import_callbacks.try_import_target =
        [&](uint64_t target_pc, llvm::Function &placeholder,
            std::string &failure_reason,
            llvm::Function *&imported_root) -> bool {
          const uint64_t cache_target =
              canonicalizeVmEnterImportTarget(M, target_pc);
          if (auto cached_it = vm_enter_import_attempt_cache.find(cache_target);
              cached_it != vm_enter_import_attempt_cache.end()) {
            const auto &cached_plan = cached_it->second;
            if (cached_plan.eligibility != ImportEligibility::kImportable ||
                !cached_plan.imported_root) {
              failure_reason = cached_plan.rejection_detail.empty()
                                   ? toString(cached_plan.rejection_reason)
                                   : cached_plan.rejection_detail;
              return false;
            }
          }
          auto raw_child = callbacks.lift_child_target(
              target_pc, /*no_abi=*/true, request.enable_gsd,
              /*enable_recovery_mode=*/true, /*dump_virtual_model=*/true);
          if (!raw_child) {
            failure_reason = "child_lift_failed";
            ChildImportPlan failed_plan;
            failed_plan.target_pc = target_pc;
            failed_plan.eligibility = ImportEligibility::kRejected;
            failed_plan.rejection_reason =
                RecoveryRejectionReason::kChildLiftFailed;
            failed_plan.rejection_detail = failure_reason;
            vm_enter_import_attempt_cache[cache_target] = failed_plan;
            return false;
          }
          auto analyzed_raw_child = analyzeChildLiftArtifactForPlanning(
              M.getContext(), std::move(*raw_child));
          auto prepared_child = prepareChildLiftArtifact(
              M.getContext(), analyzed_raw_child, /*no_abi_mode=*/true);
          auto analyzed_child = analyzeChildLiftArtifactForPlanning(
              M.getContext(), prepared_child.artifact);
          auto selected_child = selectBestChildImportArtifact(
              M.getContext(), analyzed_raw_child, analyzed_child,
              ChildRootSelectionMode::kVmEnter);
          analyzed_child = selected_child.artifact;
          auto preimport_plan = selected_child.plan;
          vm_enter_import_attempt_cache[cache_target] = preimport_plan;
          if (preimport_plan.eligibility != ImportEligibility::kImportable) {
            failure_reason = preimport_plan.rejection_detail.empty()
                                 ? toString(preimport_plan.rejection_reason)
                                 : preimport_plan.rejection_detail;
            return false;
          }
          auto plan = callbacks.import_vm_enter_child(
              target_pc, analyzed_child, preimport_plan, placeholder);
          vm_enter_import_attempt_cache[cache_target] = plan;
          if (plan.eligibility != ImportEligibility::kImportable ||
              !plan.imported_root) {
            if (!plan.rejection_detail.empty()) {
              failure_reason = plan.rejection_detail;
            } else if (!analyzed_child.rejection_detail.empty()) {
              failure_reason = analyzed_child.rejection_detail;
            } else {
              failure_reason = toString(plan.rejection_reason);
            }
            return false;
          }
          imported_root = plan.imported_root;
          return true;
        };
    import_callbacks.on_imported_target = [&](uint64_t target_pc) {
      if (callbacks.note_imported_target)
        callbacks.note_imported_target(target_pc);
    };

    auto import_summary =
        orchestrator_.importNestedVmEnterChildren(M, import_callbacks);
    if (!import_summary.changed)
      return false;

    bundle.changed = true;
    noteBoundaryCleanup("boundary_continuation_vm_enter_import_cleanup");
    return true;
  };
  auto drainBoundaryContinuationFrontier =
      [&](llvm::StringRef frontier_label, bool initial_changed) {
        if (!callbacks.advance_session_owned_frontier_work)
          return false;
        bool any_changed = false;
        bool carry_changed = initial_changed;
        constexpr unsigned kMaxDrainRounds = 2;
        for (unsigned round = 0; round < kMaxDrainRounds; ++round) {
          const bool imported_vm_enter = importSeededVmEnterChildren();
          carry_changed = carry_changed || imported_vm_enter;
          if (!carry_changed)
            break;

          const auto round_label =
              (llvm::Twine(frontier_label) + ".drain." +
               llvm::Twine(round))
                  .str();
          const bool frontier_changed =
              callbacks.advance_session_owned_frontier_work(
                  FrontierDiscoveryPhase::kUnresolvedOnly, round_label);
          if (frontier_changed) {
            noteBoundaryCleanup(
                "boundary_continuation_followup_output_cleanup");
          }
          any_changed = any_changed || imported_vm_enter || frontier_changed;
          carry_changed = frontier_changed;
        }
        return any_changed;
      };
  auto requeueBoundaryBridgeMaterialization =
      [&](uint64_t target_pc, llvm::StringRef frontier_label) {
        if (!callbacks.advance_session_owned_frontier_work)
          return false;
        if (!orchestrator_.requeueBoundaryEdgesForTarget(
                M, target_pc, "boundary_continuation_progressed")) {
          return false;
        }
        const auto requeue_label =
            (llvm::Twine(frontier_label) + ".requeue").str();
        const bool frontier_changed =
            callbacks.advance_session_owned_frontier_work(
                FrontierDiscoveryPhase::kUnresolvedOnly, requeue_label);
        if (frontier_changed)
          noteBoundaryCleanup("boundary_continuation_requeue_output_cleanup");
        const bool drained =
            drainBoundaryContinuationFrontier(requeue_label, frontier_changed);
        return frontier_changed || drained;
      };

  for (const auto &node : graph.nodes) {
    switch (node.kind) {
      case FinalTailNodeKind::kModeledReentryBoundary:
      case FinalTailNodeKind::kRetryableBoundary:
      case FinalTailNodeKind::kTerminalModeledBoundary:
      case FinalTailNodeKind::kHardRejectedBoundary:
        break;
      case FinalTailNodeKind::kExecutablePlaceholder:
      case FinalTailNodeKind::kTerminalModeledChild:
      case FinalTailNodeKind::kHardRejectedExecutable:
        continue;
    }

    const auto original_kind =
        original_kinds.count(node.target_pc) ? original_kinds[node.target_pc]
                                             : node.kind;
    auto [source_name, source_pc] = findTailGraphSource(original_graph,
                                                        node.target_pc);

    BoundaryTailRecoveryAction action;
    BoundaryTailRecoveryActionResult result;
    action.target_pc = node.target_pc;
    result.target_pc = node.target_pc;

    const bool had_session_boundary_fact =
        findBoundaryFactForTargetInSession(orchestrator_, node.target_pc)
            .has_value();
    auto boundary = findBoundaryFactForTarget(orchestrator_, &M, node.target_pc);
    std::optional<BoundaryFact> effective_boundary = boundary;
    const bool node_has_controlled_return =
        node.detail == "modeled_controlled_return" ||
        node.detail == "controlled_return_unresolved";
    std::optional<uint64_t> effective_continuation_pc;
    if (boundary)
      effective_continuation_pc = effectiveBoundaryContinuationPc(*boundary);
    else if (node.continuation_pc)
      effective_continuation_pc = node.continuation_pc;

    if (!effective_boundary && node_has_controlled_return) {
      effective_boundary = BoundaryFact{};
      effective_boundary->boundary_pc = node.target_pc;
      effective_boundary->native_target_pc = node.target_pc;
      effective_boundary->suppresses_normal_fallthrough = true;
      effective_boundary->return_address_control_kind =
          effective_continuation_pc
              ? VirtualReturnAddressControlKind::kRedirectedConstant
              : VirtualReturnAddressControlKind::kRedirectedSymbolic;
      effective_boundary->controlled_return_pc = effective_continuation_pc;
      effective_boundary->kind = BoundaryKind::kNativeBoundary;
    }

    if (effective_continuation_pc) {
      action.continuation_pc = effective_continuation_pc;
      result.continuation_pc = effective_continuation_pc;
      if (!effective_boundary)
        effective_boundary = BoundaryFact{};
      if (!effective_boundary->boundary_pc)
        effective_boundary->boundary_pc = node.target_pc;
      if (!effective_boundary->native_target_pc)
        effective_boundary->native_target_pc = node.target_pc;
      if (!effective_boundary->continuation_pc &&
          !effective_boundary->suppresses_normal_fallthrough) {
        effective_boundary->continuation_pc = effective_continuation_pc;
      }
      if (effective_boundary->suppresses_normal_fallthrough ||
          effective_boundary->return_address_control_kind !=
              VirtualReturnAddressControlKind::kUnknown) {
        effective_boundary->controlled_return_pc = effective_continuation_pc;
      }
      effective_boundary->reenters_vm = true;
      if (effective_boundary->kind == BoundaryKind::kUnknown)
        effective_boundary->kind = BoundaryKind::kNativeBoundary;
      if (effective_boundary->exit_disposition == BoundaryDisposition::kUnknown) {
        effective_boundary->exit_disposition =
            BoundaryDisposition::kVmExitNativeCallReenter;
      }
    }
    const bool boundary_has_controlled_return =
        effective_boundary &&
        effective_boundary->suppresses_normal_fallthrough &&
        effective_boundary->return_address_control_kind !=
            VirtualReturnAddressControlKind::kUnknown;
    const bool boundary_has_intra_owner_continuation =
        effective_boundary &&
        (effective_boundary->covered_entry_pc.has_value() ||
         effective_boundary->continuation_entry_transform.has_value());

    if (node.kind == FinalTailNodeKind::kModeledReentryBoundary) {
      action.kind = BoundaryTailRecoveryActionKind::kLiftBoundaryContinuation;
      action.source_label = source_name.empty() ? "boundary_tail_graph"
                                                : source_name;
      action.reason =
          original_kind == FinalTailNodeKind::kRetryableBoundary
              ? "replayed_to_modeled_reentry_boundary"
              : "modeled_reentry_boundary";
      action.expected_outcome = "lift continuation and materialize boundary bridge";

      result.kind = action.kind;
      result.attempted = true;
      auto *existing_tail_graph_continuation =
          effective_continuation_pc
              ? findBoundaryContinuationFunction(M, *effective_continuation_pc)
              : nullptr;
      if ((!had_session_boundary_fact || boundary_has_controlled_return) &&
          isUsableBoundaryContinuationFunction(
              orchestrator_, existing_tail_graph_continuation,
              effective_continuation_pc)) {
        result.disposition =
            BoundaryTailRecoveryDisposition::kContinuationLifted;
        if (boundary_has_controlled_return) {
          result.detail = "controlled_return_continuation_lifted";
        } else if (boundary_has_intra_owner_continuation) {
          result.detail = "intra_owner_continuation_lifted";
        } else {
          result.detail = "tail_graph_continuation_materialized";
        }
        lifted_boundary_targets.push_back(node.target_pc);
      } else if (!effective_continuation_pc) {
        result.disposition =
            boundary_has_controlled_return
                ? BoundaryTailRecoveryDisposition::kKeptModeledBoundary
                : BoundaryTailRecoveryDisposition::kSkipped;
        result.detail = boundary_has_controlled_return
                            ? "controlled_return_unresolved"
                            : "missing_boundary_continuation";
      } else if (!callbacks.advance_session_owned_frontier_work) {
        result.disposition = BoundaryTailRecoveryDisposition::kKeptModeledBoundary;
        result.detail = boundary_has_controlled_return
                            ? "modeled_controlled_return"
                            : "modeled_reentry_boundary";
      } else {
        const bool enqueued = orchestrator_.enqueueBoundaryContinuationWork(
            M, *effective_boundary, source_name, source_pc);
        if (!enqueued) {
          result.disposition = BoundaryTailRecoveryDisposition::kSkipped;
          result.detail = "boundary_continuation_enqueue_failed";
        } else {
          const auto frontier_label =
              (llvm::Twine("boundary_continuation_") +
               llvm::utohexstr(node.target_pc))
                  .str();
          const bool frontier_changed =
              callbacks.advance_session_owned_frontier_work(
                  FrontierDiscoveryPhase::kUnresolvedOnly, frontier_label);
          if (frontier_changed)
            noteBoundaryCleanup("boundary_continuation_final_output_cleanup");
          const bool drained_boundary_frontier =
              drainBoundaryContinuationFrontier(frontier_label, frontier_changed);
          auto preferImportedVmEnterRoot =
              [&](llvm::Function *candidate) -> llvm::Function * {
            if (!effective_continuation_pc)
              return candidate;
            if (auto imported_it =
                    orchestrator_.session().imported_vm_enter_child_roots.find(
                        *effective_continuation_pc);
                imported_it !=
                orchestrator_.session().imported_vm_enter_child_roots.end()) {
              if (auto *imported = M.getFunction(imported_it->second);
                  imported && !imported->isDeclaration()) {
                return imported;
              }
            }
            return candidate;
          };
          auto *continuation = preferImportedVmEnterRoot(
              findBoundaryContinuationFunction(M, *effective_continuation_pc));
          auto findMaterializedBoundaryBridge = [&]() -> llvm::Function * {
            auto find_by_pc = [&](std::optional<uint64_t> maybe_pc)
                -> llvm::Function * {
              if (!maybe_pc)
                return nullptr;
              if (auto *bridge =
                      findStructuralCodeTargetFunctionByPC(M, *maybe_pc);
                  bridge && !bridge->isDeclaration()) {
                return bridge;
              }
              if (auto *bridge = findLiftedOrBlockFunctionByPC(M, *maybe_pc);
                  bridge && !bridge->isDeclaration()) {
                return bridge;
              }
              return nullptr;
            };
            if (auto *bridge = find_by_pc(effective_boundary->boundary_pc))
              return bridge;
            if (auto *bridge = find_by_pc(effective_boundary->native_target_pc))
              return bridge;
            if (!node.symbol_name.empty()) {
              if (auto *bridge = M.getFunction(node.symbol_name);
                  bridge && !bridge->isDeclaration()) {
                return bridge;
              }
            }
            return nullptr;
          };
          llvm::Function *boundary_fn = findMaterializedBoundaryBridge();
          const auto continuation_status = effective_boundary->boundary_pc
                                               ? findBoundaryContinuationStatus(
                                                     orchestrator_,
                                                     *effective_boundary->boundary_pc,
                                                     *effective_continuation_pc)
                                               : std::nullopt;
          const bool continuation_lifted =
              continuation_status &&
              (*continuation_status == FrontierWorkStatus::kSkippedMaterialized ||
               *continuation_status == FrontierWorkStatus::kLifted);
          const bool boundary_bridge_materialized =
              boundary_fn && !boundary_fn->isDeclaration();
          const bool continuation_materialized =
              continuation && !continuation->isDeclaration();
          const bool usable_continuation_materialized =
              isUsableBoundaryContinuationFunction(
                  orchestrator_, continuation, effective_continuation_pc);
          if (boundary_bridge_materialized &&
              usable_continuation_materialized &&
              (continuation_lifted || continuation_materialized)) {
            result.disposition =
                BoundaryTailRecoveryDisposition::kContinuationLifted;
            if (boundary_has_controlled_return) {
              result.detail = "controlled_return_continuation_lifted";
            } else if (boundary_has_intra_owner_continuation) {
              result.detail = "intra_owner_continuation_lifted";
            } else {
              result.detail = "boundary_continuation_materialized";
            }
            result.module_changed = true;
            bundle.changed = true;
            lifted_boundary_targets.push_back(node.target_pc);
          } else if ((!had_session_boundary_fact || boundary_has_controlled_return) &&
                     !boundary_bridge_materialized &&
                     usable_continuation_materialized &&
                     continuation_materialized) {
            result.disposition =
                BoundaryTailRecoveryDisposition::kContinuationLifted;
            if (boundary_has_controlled_return) {
              result.detail = "controlled_return_continuation_lifted";
            } else if (boundary_has_intra_owner_continuation) {
              result.detail = "intra_owner_continuation_lifted";
            } else {
              result.detail = "tail_graph_continuation_materialized";
            }
            lifted_boundary_targets.push_back(node.target_pc);
          } else if (continuation &&
                     requeueBoundaryBridgeMaterialization(node.target_pc,
                                                          frontier_label)) {
            continuation = preferImportedVmEnterRoot(
                findBoundaryContinuationFunction(M, *effective_continuation_pc));
            boundary_fn = findMaterializedBoundaryBridge();
            const auto refreshed_status =
                effective_boundary->boundary_pc
                    ? findBoundaryContinuationStatus(orchestrator_,
                                                     *effective_boundary->boundary_pc,
                                                     *effective_continuation_pc)
                    : std::nullopt;
            const bool refreshed_continuation_materialized =
                continuation && !continuation->isDeclaration();
            const bool refreshed_usable_continuation_materialized =
                isUsableBoundaryContinuationFunction(
                    orchestrator_, continuation, effective_continuation_pc);
            const bool refreshed_boundary_bridge_materialized =
                boundary_fn && !boundary_fn->isDeclaration();
            if (refreshed_boundary_bridge_materialized &&
                refreshed_usable_continuation_materialized &&
                ((refreshed_status &&
                  (*refreshed_status ==
                       FrontierWorkStatus::kSkippedMaterialized ||
                   *refreshed_status == FrontierWorkStatus::kLifted)) ||
                 refreshed_continuation_materialized)) {
              result.disposition =
                  BoundaryTailRecoveryDisposition::kContinuationLifted;
              if (boundary_has_controlled_return) {
                result.detail = "controlled_return_continuation_lifted";
              } else if (boundary_has_intra_owner_continuation) {
                result.detail = "intra_owner_continuation_lifted";
              } else {
                result.detail = "boundary_continuation_materialized";
              }
              result.module_changed = true;
              bundle.changed = true;
              lifted_boundary_targets.push_back(node.target_pc);
            } else if ((!had_session_boundary_fact || boundary_has_controlled_return) &&
                       !refreshed_boundary_bridge_materialized &&
                       refreshed_usable_continuation_materialized &&
                       refreshed_continuation_materialized) {
              result.disposition =
                  BoundaryTailRecoveryDisposition::kContinuationLifted;
              if (boundary_has_controlled_return) {
                result.detail = "controlled_return_continuation_lifted";
              } else if (boundary_has_intra_owner_continuation) {
                result.detail = "intra_owner_continuation_lifted";
              } else {
                result.detail = "tail_graph_continuation_materialized";
              }
              lifted_boundary_targets.push_back(node.target_pc);
            } else {
              result.disposition =
                  BoundaryTailRecoveryDisposition::kKeptModeledBoundary;
              if (effective_continuation_pc) {
                if (boundary_has_intra_owner_continuation) {
                  result.detail = "modeled_intra_owner_continuation";
                } else if (auto failure_reason =
                               findVmEnterChildImportFailureReason(
                                   orchestrator_, M,
                                   *effective_continuation_pc);
                           failure_reason && !failure_reason->empty()) {
                  result.detail = "vm_enter_child:" + *failure_reason;
                } else if (boundary_has_controlled_return &&
                           !effectiveBoundaryContinuationPc(*effective_boundary)) {
                  result.detail = "controlled_return_unresolved";
                } else {
                  result.detail = boundary_has_controlled_return
                                      ? "modeled_controlled_return"
                                      : "boundary_reentry_still_modeled";
                }
              } else {
                result.detail = boundary_has_controlled_return
                                    ? "controlled_return_unresolved"
                                    : "boundary_reentry_still_modeled";
              }
              result.module_changed = true;
              bundle.changed = true;
            }
          } else {
            result.disposition =
                BoundaryTailRecoveryDisposition::kKeptModeledBoundary;
            if (effective_continuation_pc) {
              if (boundary_has_intra_owner_continuation) {
                result.detail = "modeled_intra_owner_continuation";
              } else if (auto failure_reason =
                             findVmEnterChildImportFailureReason(
                                 orchestrator_, M,
                                 *effective_continuation_pc);
                         failure_reason && !failure_reason->empty()) {
                result.detail = "vm_enter_child:" + *failure_reason;
              } else if (boundary_has_controlled_return &&
                         !effectiveBoundaryContinuationPc(*effective_boundary)) {
                result.detail = "controlled_return_unresolved";
              } else {
                result.detail = frontier_changed
                                    ? (boundary_has_controlled_return
                                           ? "modeled_controlled_return"
                                           : "boundary_reentry_still_modeled")
                                    : (boundary_has_controlled_return
                                           ? "modeled_controlled_return"
                                           : "modeled_reentry_boundary");
              }
            } else {
              result.detail = frontier_changed
                                  ? (boundary_has_controlled_return
                                         ? "modeled_controlled_return"
                                         : "boundary_reentry_still_modeled")
                                  : (boundary_has_controlled_return
                                         ? "modeled_controlled_return"
                                         : "modeled_reentry_boundary");
            }
            result.module_changed =
                frontier_changed || drained_boundary_frontier;
            bundle.changed =
                bundle.changed || frontier_changed || drained_boundary_frontier;
          }
        }
      }
    } else if (node.kind == FinalTailNodeKind::kTerminalModeledBoundary) {
      action.kind =
          original_kind == FinalTailNodeKind::kRetryableBoundary
              ? BoundaryTailRecoveryActionKind::kReplayBoundaryAndReclassify
              : BoundaryTailRecoveryActionKind::kMaterializeTerminalBoundary;
      action.source_label = source_name.empty() ? "boundary_tail_graph"
                                                : source_name;
      action.reason = "terminal_modeled_boundary";
      action.expected_outcome =
          "keep explicit terminal modeled boundary without retry churn";

      result.kind = action.kind;
      result.attempted =
          original_kind == FinalTailNodeKind::kRetryableBoundary;
      result.disposition =
          original_kind == FinalTailNodeKind::kRetryableBoundary
              ? BoundaryTailRecoveryDisposition::kReclassified
              : BoundaryTailRecoveryDisposition::kMaterializedTerminalBoundary;
      result.detail = "terminal_modeled_boundary";
    } else if (node.kind == FinalTailNodeKind::kHardRejectedBoundary) {
      action.kind =
          original_kind == FinalTailNodeKind::kRetryableBoundary
              ? BoundaryTailRecoveryActionKind::kReplayBoundaryAndReclassify
              : BoundaryTailRecoveryActionKind::kHardRejectBoundary;
      action.source_label = source_name.empty() ? "boundary_tail_graph"
                                                : source_name;
      action.reason = node.detail.empty() ? "hard_rejected_boundary"
                                          : node.detail;
      action.expected_outcome = "preserve explicit hard-rejected boundary";

      result.kind = action.kind;
      result.attempted =
          original_kind == FinalTailNodeKind::kRetryableBoundary;
      result.disposition = BoundaryTailRecoveryDisposition::kHardRejected;
      result.detail = action.reason;
    } else {
      action.kind = BoundaryTailRecoveryActionKind::kReplayBoundaryAndReclassify;
      action.source_label = source_name.empty() ? "boundary_tail_graph"
                                                : source_name;
      action.reason = node.detail.empty() ? "retryable_boundary" : node.detail;
      action.expected_outcome = "reclassify retryable boundary";

      result.kind = action.kind;
      result.attempted = true;
      result.disposition = BoundaryTailRecoveryDisposition::kKeptModeledBoundary;
      result.detail = action.reason;
    }

    bundle.boundary_recovery_actions.push_back(std::move(action));
    bundle.boundary_recovery_results.push_back(std::move(result));
  }

  if (!lifted_boundary_targets.empty() &&
      callbacks.patch_declared_lifted_or_block_calls_to_defined_targets) {
    std::vector<uint64_t> patch_targets(lifted_boundary_targets.begin(),
                                        lifted_boundary_targets.end());
    const auto patched =
        callbacks.patch_declared_lifted_or_block_calls_to_defined_targets(
            patch_targets, "boundary_continuation_patch",
            "patched native boundary placeholders to continuation-aware bridges");
    bundle.cleanup_actions.push_back(makeCleanupActionArtifact(
        "boundary_continuation_patch", patched != 0,
        (llvm::Twine("patched_targets=") + llvm::Twine(patched)).str()));
    if (patched != 0) {
      bundle.changed = true;
      if (callbacks.run_final_output_cleanup) {
        callbacks.run_final_output_cleanup();
        bundle.cleanup_actions.push_back(makeCleanupActionArtifact(
            "boundary_continuation_post_patch_cleanup", true, "executed"));
      }
    }
  }

  if (bundle.boundary_recovery_actions.empty() && !bundle.changed)
    return std::nullopt;

  populateRoundArtifactBundleFromModule(M, bundle);
  populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                 round_artifact_bundles_);
  bundle.final_tail_graph = buildFinalTailGraph(M);
  augmentRecoveryQualityFromTailGraph(bundle, *bundle.final_tail_graph);
  refineRecoveryQualityFromModuleShape(M, bundle);
  return bundle;
}

std::optional<RoundArtifactBundle> DevirtualizationRuntime::runFinalStateRecovery(
    llvm::Module &M, const FinalStateRecoveryRequest &request,
    const OutputRecoveryCallbacks &callbacks) const {
  vm_enter_child_import_plan_cache_.clear();
  auto plan = planFinalStateRecovery(M, request);
  if (!plan)
    return std::nullopt;

  RoundArtifactBundle bundle;
  bundle.stage = RuntimeArtifactStage::kFinalization;
  bundle.label = request.no_abi ? "final_state_recovery_noabi"
                                : "final_state_recovery";
  bundle.changed = false;
  bundle.planned_recovery_actions = plan->actions;

  auto findCacheEntry = [&](uint64_t target_pc) -> ChildArtifactCacheEntry * {
    for (auto &[key, entry] : child_artifact_cache_) {
      if (key.target_pc == target_pc && key.no_abi)
        return &entry;
    }
    return nullptr;
  };

  auto resolveBoundaryTarget = [&](uint64_t target_pc)
      -> std::optional<BoundaryResolutionResult> {
    if (auto it = boundary_resolution_cache_.find(target_pc);
        it != boundary_resolution_cache_.end()) {
      return it->second;
    }
    auto boundary = findBoundaryFactForTarget(orchestrator_, &M, target_pc);
    if (!boundary)
      return std::nullopt;
    BoundaryResolutionRequest request;
    request.target_pc = target_pc;
    request.boundary = boundary;
    request.proof = findContinuationProofForTarget(orchestrator_, target_pc);
    BoundaryContinuationResolver resolver;
    auto result = resolver.resolve(request);
    boundary_resolution_cache_[target_pc] = result;
    return result;
  };

  llvm::SmallVector<uint64_t, 8> imported_targets;
  for (const auto &action : plan->actions) {
    ExecutedRecoveryActionArtifact executed;
    executed.kind = action.kind;
    executed.target_pc = action.target_pc;

    switch (action.kind) {
      case FinalStateRecoveryActionKind::kHardReject:
        executed.disposition = FinalStateRecoveryDisposition::kHardRejected;
        executed.detail = action.reason;
        bundle.notes.push_back(
            (llvm::Twine("hard_reject target=") + llvm::utohexstr(action.target_pc) +
             " reason=" + action.reason)
                .str());
        break;

      case FinalStateRecoveryActionKind::kKeepModeledPlaceholder:
        executed.disposition = FinalStateRecoveryDisposition::kKeptPlaceholder;
        executed.detail = action.reason;
        break;

      case FinalStateRecoveryActionKind::kRetryNativeBoundaryRecovery: {
        executed.attempted = true;
        auto boundary_resolution = resolveBoundaryTarget(action.target_pc);
        if (boundary_resolution &&
            boundary_resolution->disposition ==
                BoundaryResolutionDisposition::kModeledReentryBoundary) {
          executed.disposition = FinalStateRecoveryDisposition::kKeptPlaceholder;
          executed.detail = "modeled_reentry_boundary";
        } else if (boundary_resolution &&
                   boundary_resolution->disposition ==
                       BoundaryResolutionDisposition::kModeledTerminalBoundary) {
          executed.disposition = FinalStateRecoveryDisposition::kKeptPlaceholder;
          executed.detail = "modeled_terminal_boundary";
        } else if (boundary_resolution &&
                   boundary_resolution->disposition ==
                       BoundaryResolutionDisposition::kRetryableBoundaryRecovery) {
          executed.disposition = FinalStateRecoveryDisposition::kKeptPlaceholder;
          executed.detail = "boundary_retry_still_modeled";
        } else {
          executed.disposition = FinalStateRecoveryDisposition::kHardRejected;
          executed.detail = "boundary_recovery_not_supported";
        }
        break;
      }

      case FinalStateRecoveryActionKind::kRetryExecutableChildImport:
      case FinalStateRecoveryActionKind::kRetryTerminalExecutableChild: {
        executed.attempted = true;
        auto *cache_entry = findCacheEntry(action.target_pc);
        if (!cache_entry || cache_entry->artifact.ir_text.empty()) {
          executed.disposition = FinalStateRecoveryDisposition::kSkipped;
          executed.detail = "child_artifact_missing";
          break;
        }

        auto proof = findContinuationProofForTarget(orchestrator_, action.target_pc);
        auto selected_child = selectCachedChildImportArtifact(
            M.getContext(), *cache_entry, ChildRootSelectionMode::kExecutable,
            proof, cache_entry->resolver_result);
        auto preimport_plan = selected_child.plan;
        bundle.import_decisions.push_back(makeImportDecisionArtifact(
            "final_state_recovery_plan", preimport_plan, proof,
            cache_entry->resolver_result));

        if (preimport_plan.eligibility != ImportEligibility::kImportable ||
            !callbacks.import_executable_child) {
          if (preimport_plan.rejection_detail == "terminal_modeled_child") {
            executed.disposition = FinalStateRecoveryDisposition::kKeptPlaceholder;
          } else if (preimport_plan.rejection_reason ==
              RecoveryRejectionReason::kRuntimeLeak) {
            executed.disposition = FinalStateRecoveryDisposition::kHardRejected;
          } else {
            executed.disposition =
                FinalStateRecoveryDisposition::kRetriedNoChange;
          }
          executed.detail = preimport_plan.rejection_detail.empty()
                                ? toString(preimport_plan.rejection_reason)
                                : preimport_plan.rejection_detail;
          break;
        }

        auto plan_result = callbacks.import_executable_child(
            action.target_pc, selected_child.artifact, preimport_plan,
            "execchild_");
        plan_result.import_class = preimport_plan.import_class;
        plan_result.proof = proof;
        if (!plan_result.selected_root_pc)
          plan_result.selected_root_pc = preimport_plan.selected_root_pc;
        bundle.import_decisions.push_back(makeImportDecisionArtifact(
            "final_state_recovery_import", plan_result, proof,
            cache_entry->resolver_result,
            plan_result.eligibility == ImportEligibility::kImportable &&
                plan_result.imported_root != nullptr));
        cache_entry->last_plan = plan_result;
        cache_entry->imported =
            plan_result.eligibility == ImportEligibility::kImportable &&
            plan_result.imported_root != nullptr;

        if (plan_result.eligibility == ImportEligibility::kImportable &&
            plan_result.imported_root != nullptr) {
          imported_targets.push_back(action.target_pc);
          executed.disposition = FinalStateRecoveryDisposition::kImported;
          executed.module_changed = true;
          executed.detail =
              plan_result.selected_root_pc
                  ? ("selected_root=" + llvm::utohexstr(*plan_result.selected_root_pc))
                  : "imported";
        } else {
          executed.disposition =
              plan_result.rejection_detail == "terminal_modeled_child"
                  ? FinalStateRecoveryDisposition::kKeptPlaceholder
                  : (preimport_plan.rejection_reason ==
                             RecoveryRejectionReason::kRuntimeLeak
                         ? FinalStateRecoveryDisposition::kHardRejected
                         : FinalStateRecoveryDisposition::kRetriedNoChange);
          executed.detail = plan_result.rejection_detail.empty()
                                ? toString(plan_result.rejection_reason)
                                : plan_result.rejection_detail;
        }
        break;
      }
    }

    bundle.executed_recovery_actions.push_back(std::move(executed));
  }

  if (!imported_targets.empty() &&
      callbacks.patch_declared_lifted_or_block_calls_to_defined_targets) {
    bundle.changed = true;
    std::vector<uint64_t> imported(imported_targets.begin(), imported_targets.end());
    auto patched =
        callbacks.patch_declared_lifted_or_block_calls_to_defined_targets(
            imported, "final_state_recovery_patch",
            "patched final-state approved executable child imports");
    bundle.cleanup_actions.push_back(makeCleanupActionArtifact(
        "final_state_recovery_patch", patched != 0,
        (llvm::Twine("patched_targets=") + llvm::Twine(patched)).str()));
    if (patched != 0)
      bundle.changed = true;
    if (callbacks.run_final_output_cleanup) {
      callbacks.run_final_output_cleanup();
      bundle.cleanup_actions.push_back(makeCleanupActionArtifact(
          "final_state_recovery_final_output_cleanup", true, "executed"));
      bundle.changed = true;
    }
    bundle.imported_targets.assign(imported.begin(), imported.end());
  }

  auto collectBoundaryTailTargets =
      [](const FinalTailGraph &graph) -> std::set<uint64_t> {
    std::set<uint64_t> targets;
    for (const auto &node : graph.nodes) {
      switch (node.kind) {
        case FinalTailNodeKind::kModeledReentryBoundary:
        case FinalTailNodeKind::kRetryableBoundary:
        case FinalTailNodeKind::kTerminalModeledBoundary:
        case FinalTailNodeKind::kHardRejectedBoundary:
          targets.insert(node.target_pc);
          break;
        case FinalTailNodeKind::kExecutablePlaceholder:
        case FinalTailNodeKind::kTerminalModeledChild:
        case FinalTailNodeKind::kHardRejectedExecutable:
          break;
      }
    }
    return targets;
  };

  std::set<uint64_t> seen_boundary_targets =
      collectBoundaryTailTargets(buildFinalTailGraph(M));
  constexpr unsigned kMaxBoundaryTailPasses = 3;
  for (unsigned pass = 0; pass < kMaxBoundaryTailPasses; ++pass) {
    auto boundary_bundle = runBoundaryTailRecovery(M, request, callbacks);
    if (!boundary_bundle)
      break;

    bundle.changed = bundle.changed || boundary_bundle->changed;
    bundle.cleanup_actions.insert(bundle.cleanup_actions.end(),
                                  boundary_bundle->cleanup_actions.begin(),
                                  boundary_bundle->cleanup_actions.end());
    bundle.boundary_recovery_actions.insert(
        bundle.boundary_recovery_actions.end(),
        boundary_bundle->boundary_recovery_actions.begin(),
        boundary_bundle->boundary_recovery_actions.end());
    bundle.boundary_recovery_results.insert(
        bundle.boundary_recovery_results.end(),
        boundary_bundle->boundary_recovery_results.begin(),
        boundary_bundle->boundary_recovery_results.end());
    bundle.notes.insert(bundle.notes.end(), boundary_bundle->notes.begin(),
                        boundary_bundle->notes.end());

    const auto current_boundary_targets =
        collectBoundaryTailTargets(boundary_bundle->final_tail_graph
                                       ? *boundary_bundle->final_tail_graph
                                       : buildFinalTailGraph(M));
    bool surfaced_new_boundary_targets = false;
    for (uint64_t target_pc : current_boundary_targets) {
      if (seen_boundary_targets.insert(target_pc).second)
        surfaced_new_boundary_targets = true;
    }
    if (!boundary_bundle->changed || !surfaced_new_boundary_targets)
      break;
  }

  populateRoundArtifactBundleFromModule(M, bundle);
  populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                round_artifact_bundles_);
  bundle.final_tail_graph = buildFinalTailGraph(M);
  augmentRecoveryQualityFromTailGraph(bundle, *bundle.final_tail_graph);
  refineRecoveryQualityFromModuleShape(M, bundle);
  round_artifact_bundles_.push_back(bundle);
  return bundle;
}

}  // namespace omill

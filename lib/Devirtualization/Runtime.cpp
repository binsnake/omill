#include "omill/Devirtualization/Runtime.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringSet.h>
#include <llvm/AsmParser/Parser.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/StructuralHash.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

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

namespace {

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

bool isAcceptedExternalLeafCall(llvm::StringRef name) {
  return !name.empty() && !name.starts_with("__remill_") &&
         !name.starts_with("omill_") && !name.starts_with("llvm.") &&
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

ChildLiftArtifact analyzeChildLiftArtifact(llvm::LLVMContext &llvm_context,
                                           ChildLiftArtifact artifact) {
  const auto closed_slice_root_pc =
      parseUniqueClosedRootSliceImportTarget(artifact.model_text);
  if (!artifact.selected_root_pc)
    artifact.selected_root_pc = closed_slice_root_pc;

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
            if (seen_decl_callees.insert(callee->getName()).second)
              artifact.reachable_declaration_callees.push_back(
                  callee->getName().str());
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
    return plan;
  }

  if (artifact.import_safety == ChildImportClass::kTrustedTerminalEntry ||
      artifact.import_safety == ChildImportClass::kClosedSliceRoot ||
      artifact.import_safety == ChildImportClass::kBoundaryModeledChild) {
    plan.eligibility = ImportEligibility::kImportable;
    plan.rejection_reason = RecoveryRejectionReason::kNone;
    plan.allowed_declaration_callees = artifact.reachable_declaration_callees;
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
    } else if (action.reason == "terminal_modeled_child") {
      appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.terminal_modeled_children,
                     action.target_pc);
    }
  }
  for (const auto &action : bundle.executed_recovery_actions) {
    if (action.detail == "modeled_reentry_boundary" ||
        action.detail == "boundary_reentry_still_modeled") {
      appendUniquePc(bundle.recovery_quality.modeled_reentry_boundaries,
                     action.target_pc);
    } else if (action.detail == "terminal_modeled_child") {
      appendUniquePc(bundle.recovery_quality.terminal_modeled_targets,
                     action.target_pc);
      appendUniquePc(bundle.recovery_quality.terminal_modeled_children,
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
              bundle.recovery_quality.modeled_reentry_boundaries.end()) {
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
               bundle.recovery_quality.modeled_reentry_boundaries.end();
      });
  bundle.recovery_quality.functionally_recovered =
      bundle.recovery_quality.structurally_closed &&
      bundle.recovery_quality.terminal_modeled_children.empty() &&
      !has_unclassified_executable_placeholder &&
      !has_unclassified_boundary &&
      bundle.recovery_quality.hard_rejected_targets.empty();
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

std::optional<BoundaryFact> findBoundaryFactForTarget(
    const DevirtualizationOrchestrator &orchestrator, uint64_t target_pc) {
  const auto &session = orchestrator.session();
  if (auto it = session.graph.boundary_facts_by_target.find(target_pc);
      it != session.graph.boundary_facts_by_target.end() && it->second.boundary) {
    return it->second.boundary;
  }
  for (const auto &[identity, edge] : session.graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc || *edge.target_pc != target_pc || !edge.boundary)
      continue;
    return edge.boundary;
  }
  return std::nullopt;
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
    if (cache_it != child_artifact_cache_.end() &&
        !cache_it->second.artifact.ir_text.empty()) {
      emitPreciseLog(options, callbacks, "output-recovery",
                     "child-cache-hit", "reusing cached child artifact",
                     target_pc, std::nullopt, cache_it->second.diagnostics);
      return cache_it->second.artifact;
    }

    emitPreciseLog(options, callbacks, "output-recovery", "child-cache-miss",
                   "lifting child artifact", target_pc);
    if (!callbacks.lift_child_target)
      return std::nullopt;
    auto raw_child = callbacks.lift_child_target(
        target_pc, no_abi, enable_gsd, enable_recovery_mode, dump_virtual_model);
    if (!raw_child)
      return std::nullopt;
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
              seen_import_targets.contains(item.target_pc))
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
            continue;
          }
          auto preimport_plan =
              planExecutableChildImport(item.target_pc, *child, proof,
                                        resolution);
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
        if (seen_import_targets.contains(target_pc))
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
          continue;
        }
        auto preimport_plan =
            planExecutableChildImport(target_pc, *child, proof, resolution);
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
              auto plan =
                  callbacks.import_vm_enter_child(target_pc, *child, placeholder);
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

FinalizationSummary DevirtualizationRuntime::finalizeOutput(
    const llvm::Module &M, bool devirtualization_enabled) const {
  FinalizationSummary summary;
  if (!devirtualization_enabled)
    return summary;
  summary.protector_report = buildValidationReport(M);
  summary.has_protector_report = true;
  RoundArtifactBundle bundle;
  bundle.stage = RuntimeArtifactStage::kFinalization;
  bundle.label = "finalize_output";
  bundle.changed = false;
  bundle.cleanup_actions.push_back(
      makeCleanupActionArtifact("build_validation_report", false, "executed"));
  for (const auto &issue : summary.protector_report.issues) {
    bundle.notes.push_back(issue.message);
  }
  populateRoundArtifactBundleFromModule(M, bundle);
  populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                round_artifact_bundles_);
  summary.recovery_quality = bundle.recovery_quality;
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
    auto boundary = findBoundaryFactForTarget(orchestrator_, target_pc);
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

std::optional<RoundArtifactBundle> DevirtualizationRuntime::runFinalStateRecovery(
    llvm::Module &M, const FinalStateRecoveryRequest &request,
    const OutputRecoveryCallbacks &callbacks) const {
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
    auto boundary = findBoundaryFactForTarget(orchestrator_, target_pc);
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
        auto preimport_plan = planExecutableChildImport(
            action.target_pc, cache_entry->artifact, proof,
            cache_entry->resolver_result);
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
            action.target_pc, cache_entry->artifact, preimport_plan,
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

  populateRoundArtifactBundleFromModule(M, bundle);
  populateRecoveryQualitySummary(bundle, child_artifact_cache_,
                                round_artifact_bundles_);
  round_artifact_bundles_.push_back(bundle);
  return bundle;
}

}  // namespace omill

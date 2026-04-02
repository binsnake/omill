#include "omill/Devirtualization/Orchestrator.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/ADT/Twine.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/StructuralHash.h>

#include <algorithm>
#include <cstring>
#include <limits>
#include <map>
#include <optional>
#include <set>

#include "omill/Analysis/VMTraceEmulator.h"
#include "Analysis/VirtualModel/CoreDecls.h"
#include "omill/BC/BlockLifter.h"
#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Devirtualization/OutputRootClosure.h"
#include "omill/Remill/Normalization.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

unsigned countUnresolvedDispatches(const llvm::Module &M,
                                   std::vector<uint64_t> *frontier_pcs);

bool isDispatchName(llvm::StringRef name) {
  return isDispatchIntrinsicName(name);
}

struct SessionGraphProjectionCacheEntry {
  llvm::stable_hash module_fingerprint = 0;
  uint64_t projection_serial = 0;
  SessionGraphState state;
};

constexpr const char *kSessionGraphProjectionSerialMetadata =
    "omill.session_graph_projection.serial";

uint64_t nextSessionGraphProjectionSerial() {
  static uint64_t serial = 1;
  return serial++;
}

std::optional<uint64_t> moduleSessionGraphProjectionSerial(
    const llvm::Module &M) {
  auto *named = M.getNamedMetadata(kSessionGraphProjectionSerialMetadata);
  if (!named || named->getNumOperands() == 0)
    return std::nullopt;
  auto *tuple = named->getOperand(0);
  if (!tuple || tuple->getNumOperands() == 0)
    return std::nullopt;
  auto *meta =
      llvm::mdconst::dyn_extract_or_null<llvm::ConstantInt>(tuple->getOperand(0));
  if (!meta)
    return std::nullopt;
  return meta->getZExtValue();
}

std::map<const llvm::Module *, SessionGraphProjectionCacheEntry> &
sessionGraphProjectionCache() {
  static auto *cache =
      new std::map<const llvm::Module *, SessionGraphProjectionCacheEntry>();
  return *cache;
}

VirtualExitDisposition boundaryDisposition(
    const std::optional<BoundaryFact> &fact) {
  if (!fact)
    return VirtualExitDisposition::kUnknown;
  return virtualExitDispositionFromBoundaryDisposition(fact->exit_disposition);
}

std::optional<uint64_t> boundaryContinuationVipPc(
    const std::optional<BoundaryFact> &fact) {
  if (!fact)
    return std::nullopt;
  return fact->continuation_vip_pc;
}

std::optional<unsigned> boundaryContinuationSlotId(
    const std::optional<BoundaryFact> &fact) {
  if (!fact)
    return std::nullopt;
  return fact->continuation_slot_id;
}

std::optional<unsigned> boundaryContinuationStackCellId(
    const std::optional<BoundaryFact> &fact) {
  if (!fact)
    return std::nullopt;
  return fact->continuation_stack_cell_id;
}

void classifyContinuationCandidate(FrontierWorkItem &item);

bool isLiftedHelperName(llvm::StringRef name) {
  return name.starts_with("blk_") || name.starts_with("block_") ||
         (name.starts_with("sub_") && !name.ends_with("_native"));
}

bool isBlockLiftName(llvm::StringRef name) {
  return name.starts_with("blk_") || name.starts_with("block_");
}

bool isTerminalBoundaryRecoveryModeEnabled() {
  const char *value = std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY");
  return value && value[0] != '\0' && value[0] != '0';
}

bool envFlagEnabled(const char *name) {
  const char *value = std::getenv(name);
  if (!value || value[0] == '\0')
    return false;
  auto sv = llvm::StringRef(value).lower();
  return !(sv == "0" || sv == "false" || sv == "off" || sv == "no");
}

bool functionLooksLikeVmBoundary(const llvm::Function &F) {
  return F.getName().starts_with("vm_entry_") ||
         F.getFnAttribute("omill.protected_boundary").isValid() ||
         F.getFnAttribute("omill.boundary_entry_va").isValid();
}

std::optional<uint64_t> parseMaybeHex(llvm::StringRef text) {
  if (text.empty())
    return std::nullopt;
  if (text.consume_front("0x") || text.consume_front("0X")) {
  }
  uint64_t value = 0;
  if (text.getAsInteger(16, value))
    return std::nullopt;
  return value;
}

std::optional<uint64_t> extractLiftUnitVA(const llvm::Function &F) {
  if (auto entry_va = extractEntryVA(F.getName()))
    return entry_va;
  if (auto block_pc = extractBlockPC(F.getName()))
    return block_pc;
  auto attr = F.getFnAttribute("omill.boundary_entry_va");
  if (!attr.isValid())
    return std::nullopt;
  return parseMaybeHex(attr.getValueAsString());
}

bool isTrackedLiftUnit(const llvm::Function &F) {
  if (F.isDeclaration() || F.getName().ends_with("_native"))
    return false;
  if (!isLiftedHelperName(F.getName()) && !functionLooksLikeVmBoundary(F))
    return false;
  return extractLiftUnitVA(F).has_value();
}

bool isSessionGraphTrackedFunction(const llvm::Function &F) {
  return isTrackedLiftUnit(F) || F.hasFnAttribute("omill.output_root") ||
         F.hasFnAttribute("omill.closed_root_slice_root");
}

bool hasKnownMaterializedTarget(const llvm::Module &M, uint64_t pc) {
  if (M.getFunction(liftedFunctionName(pc)))
    return true;
  auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (M.getFunction(block_name))
    return true;
  auto trace_name = (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  return M.getFunction(trace_name) != nullptr;
}

bool canMaterializeFrontierTarget(const llvm::Module &M, uint64_t pc,
                                  const FrontierCallbacks &callbacks) {
  if (findLiftedOrCoveredFunctionByPC(const_cast<llvm::Module &>(M), pc))
    return true;
  if (!callbacks.has_defined_target)
    return false;
  bool has_defined_target = false;
  __try {
    has_defined_target = callbacks.has_defined_target(pc);
  } __except (1) {
    has_defined_target = false;
  }
  return has_defined_target;
}

std::optional<uint64_t> recoverCoveredTargetEntryPc(llvm::Module &M,
                                                    uint64_t pc) {
  if (!pc)
    return std::nullopt;
  if (auto *covered = findLiftedOrCoveredFunctionByPC(M, pc)) {
    if (auto entry_pc = extractLiftUnitVA(*covered))
      return entry_pc;
  }
  if (auto nearby_pc = findNearestCoveredLiftedOrBlockPC(M, pc, 0x80))
    return nearby_pc;
  return std::nullopt;
}

uint64_t safeNormalizeTargetPc(uint64_t pc, const FrontierCallbacks &callbacks) {
  if (!callbacks.normalize_target_pc)
    return pc;
  uint64_t normalized_pc = pc;
  __try {
    normalized_pc = callbacks.normalize_target_pc(pc);
  } __except (1) {
    normalized_pc = pc;
  }
  return normalized_pc;
}

bool safeCanDecodeTarget(uint64_t pc, const FrontierCallbacks &callbacks) {
  if (!callbacks.can_decode_target)
    return false;
  bool decodable = false;
  __try {
    decodable = callbacks.can_decode_target(pc);
  } __except (1) {
    decodable = false;
  }
  return decodable;
}

bool hasExactMaterializedTarget(llvm::Module &M, uint64_t pc) {
  if (!pc)
    return false;
  if (auto *fn = findStructuralCodeTargetFunctionByPC(M, pc))
    return !fn->isDeclaration();
  if (auto *fn = findLiftedOrBlockFunctionByPC(M, pc))
    return !fn->isDeclaration();
  if (auto *fn = M.getFunction(liftedFunctionName(pc)))
    return !fn->isDeclaration();
  auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *fn = M.getFunction(block_name))
    return !fn->isDeclaration();
  auto trace_name =
      (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  if (auto *fn = M.getFunction(trace_name))
    return !fn->isDeclaration();
  return false;
}

bool compatibilityRequested(const DevirtualizationCompatInputs &compat_inputs) {
  return compat_inputs.requested_block_lift ||
         compat_inputs.requested_generic_static;
}

bool requestedCompatBlockLiftMode(const DevirtualizationRequest &request,
                                  const DevirtualizationCompatInputs &compat_inputs) {
  return compat_inputs.requested_block_lift || request.force_devirtualize ||
         compat_inputs.requested_generic_static ||
         compat_inputs.env_generic_static;
}

bool requestedCompatGenericStatic(
    const DevirtualizationRequest &request,
    const DevirtualizationCompatInputs &compat_inputs) {
  return request.force_devirtualize || compat_inputs.requested_generic_static ||
         compat_inputs.env_generic_static;
}

std::optional<ContinuationEntryTransform> detectPushImmediateJumpTransform(
    uint64_t pc, const FrontierCallbacks &callbacks) {
  if (!pc || !callbacks.read_target_bytes)
    return std::nullopt;

  uint8_t bytes[16] = {};
  bool read_ok = false;
  __try {
    read_ok = callbacks.read_target_bytes(pc, bytes, sizeof(bytes));
  } __except (1) {
    read_ok = false;
  }
  if (!read_ok || bytes[0] != 0x68)
    return std::nullopt;

  const uint32_t imm32 = static_cast<uint32_t>(bytes[1]) |
                         (static_cast<uint32_t>(bytes[2]) << 8) |
                         (static_cast<uint32_t>(bytes[3]) << 16) |
                         (static_cast<uint32_t>(bytes[4]) << 24);
  uint64_t jump_target = 0;
  if (bytes[5] == 0xE9) {
    const int32_t rel32 = static_cast<int32_t>(
        static_cast<uint32_t>(bytes[6]) |
        (static_cast<uint32_t>(bytes[7]) << 8) |
        (static_cast<uint32_t>(bytes[8]) << 16) |
        (static_cast<uint32_t>(bytes[9]) << 24));
    jump_target = static_cast<uint64_t>(
        static_cast<int64_t>(pc + 10) + static_cast<int64_t>(rel32));
  } else if (bytes[5] == 0xEB) {
    const int8_t rel8 = static_cast<int8_t>(bytes[6]);
    jump_target = static_cast<uint64_t>(
        static_cast<int64_t>(pc + 7) + static_cast<int64_t>(rel8));
  } else {
    return std::nullopt;
  }

  ContinuationEntryTransform transform;
  transform.kind = ContinuationEntryTransformKind::kPushImmediateJump;
  transform.entry_pc = pc;
  transform.jump_target_pc = jump_target;
  transform.pushed_immediate = imm32;
  transform.suppresses_normal_fallthrough = true;
  return transform;
}

std::optional<uint64_t> recoverBoundaryContinuationLiftTarget(
    llvm::Module &M, uint64_t continuation_pc,
    const FrontierCallbacks &callbacks) {
  if (!continuation_pc)
    return std::nullopt;

  const uint64_t normalized_target_pc =
      safeNormalizeTargetPc(continuation_pc, callbacks);
  llvm::SmallVector<uint64_t, 2> primary_candidates;
  primary_candidates.push_back(continuation_pc);
  if (normalized_target_pc != continuation_pc)
    primary_candidates.push_back(normalized_target_pc);

  auto candidateReady = [&](uint64_t candidate_pc) {
    if (!candidate_pc)
      return false;
    if (canMaterializeFrontierTarget(M, candidate_pc, callbacks))
      return true;
    return safeCanDecodeTarget(candidate_pc, callbacks);
  };

  for (uint64_t candidate_pc : primary_candidates) {
    if (auto covered_pc = recoverCoveredTargetEntryPc(M, candidate_pc))
      return covered_pc;
    if (auto *nearby_structural =
            findNearestStructuralCodeTargetFunctionByPC(M, candidate_pc, 0x80)) {
      if (uint64_t structural_pc = extractStructuralCodeTargetPC(*nearby_structural))
        return structural_pc;
    }
  }

  for (uint64_t candidate_pc : primary_candidates) {
    if (candidateReady(candidate_pc))
      return candidate_pc;
  }

  return std::nullopt;
}

struct FunctionNormalizationSnapshot {
  unsigned unresolved_dispatch_intrinsics = 0;
  unsigned live_memory_intrinsics = 0;
  unsigned live_runtime_intrinsics = 0;
  unsigned legacy_dispatch_intrinsics = 0;
  std::vector<std::string> dirty_dependencies;
};

FunctionNormalizationSnapshot summarizeFunctionNormalization(
    const llvm::Function &F) {
  FunctionNormalizationSnapshot snapshot;
  std::set<std::string> dependency_names;
  for (const auto &BB : F) {
    for (const auto &I : BB) {
      const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      const auto *Callee = CB ? CB->getCalledFunction() : nullptr;
      if (!Callee)
        continue;
      auto Name = Callee->getName();
      if (isDispatchIntrinsicName(Name))
        ++snapshot.unresolved_dispatch_intrinsics;
      if (isLegacyOmillDispatchName(Name))
        ++snapshot.legacy_dispatch_intrinsics;
      if (Name.starts_with("__remill_read_memory_") ||
          Name.starts_with("__remill_write_memory_")) {
        ++snapshot.live_memory_intrinsics;
      }
      if (Name.starts_with("__remill_") && !isDispatchIntrinsicName(Name) &&
          Name != "__remill_basic_block") {
        ++snapshot.live_runtime_intrinsics;
      }
      if (isTrackedLiftUnit(*Callee))
        dependency_names.insert(Callee->getName().str());
    }
  }
  snapshot.dirty_dependencies.assign(dependency_names.begin(),
                                     dependency_names.end());
  return snapshot;
}

bool passesNormalizationGate(const FunctionNormalizationSnapshot &snapshot) {
  return snapshot.legacy_dispatch_intrinsics == 0 &&
         snapshot.live_memory_intrinsics == 0 &&
         snapshot.live_runtime_intrinsics == 0;
}

std::pair<VipTrackingStatus, std::optional<uint64_t>> classifyVipTrackingForFunction(
    llvm::StringRef function_name, llvm::ArrayRef<UnresolvedExitSite> unresolved_exits) {
  bool saw_symbolic = false;
  for (const auto &site : unresolved_exits) {
    if (site.owner_function != function_name)
      continue;
    if (site.vip_pc.has_value())
      return {VipTrackingStatus::kResolved, site.vip_pc};
    saw_symbolic = saw_symbolic || site.vip_symbolic;
  }
  return {saw_symbolic ? VipTrackingStatus::kSymbolic : VipTrackingStatus::kUnknown,
          std::nullopt};
}

std::string unresolvedExitIdentity(const UnresolvedExitSite &site) {
  std::string key = site.owner_function + ":" +
                    std::to_string(site.site_index) + ":" +
                    std::to_string(static_cast<int>(site.kind)) + ":";
  if (site.site_pc)
    key += llvm::utohexstr(*site.site_pc);
  key += ":";
  if (site.target_pc)
    key += llvm::utohexstr(*site.target_pc);
  key += ":";
  if (site.vip_pc)
    key += llvm::utohexstr(*site.vip_pc);
  key += ":";
  if (site.continuation_vip_pc)
    key += llvm::utohexstr(*site.continuation_vip_pc);
  key += ":";
  if (site.continuation_slot_id)
    key += std::to_string(*site.continuation_slot_id);
  key += ":";
  if (site.continuation_stack_cell_id)
    key += std::to_string(*site.continuation_stack_cell_id);
  key += ":";
  key += site.vip_symbolic ? "sym" : "concrete";
  key += ":";
  key += std::to_string(static_cast<int>(site.exit_disposition));
  return key;
}

std::string unresolvedExitStableSiteKey(const UnresolvedExitSite &site) {
  std::string key = site.owner_function + ":" +
                    std::to_string(site.site_index) + ":" +
                    std::to_string(static_cast<int>(site.kind)) + ":";
  if (site.site_pc)
    key += llvm::utohexstr(*site.site_pc);
  return key;
}

std::string frontierStableSiteKey(const FrontierWorkItem &item) {
  std::string key =
      (item.from_boundary_continuation
           ? "boundary-continuation"
           : (item.identity.find("closure:") == 0
           ? "closure"
           : (item.owner_function == "__frontier__" ? "frontier"
                                                    : "unresolved"))) +
      std::string(":") + item.owner_function + ":" +
      std::to_string(item.site_index) + ":";
  if (item.site_pc)
    key += llvm::utohexstr(*item.site_pc);
  key += ":";
  if (item.target_pc)
    key += llvm::utohexstr(*item.target_pc);
  key += ":" + std::to_string(static_cast<int>(item.root_frontier_kind));
  return key;
}

std::string edgeStableSiteKey(const SessionEdgeFact &edge) {
  std::string key =
      (edge.from_boundary_continuation
           ? "boundary-continuation"
           : (edge.from_output_root_closure
           ? "closure"
           : (edge.owner_function == "__frontier__" ? "frontier"
                                                    : "unresolved"))) +
      std::string(":") + edge.owner_function + ":" +
      std::to_string(edge.site_index) + ":";
  if (edge.site_pc)
    key += llvm::utohexstr(*edge.site_pc);
  key += ":";
  if (edge.target_pc)
    key += llvm::utohexstr(*edge.target_pc);
  key += ":" + std::to_string(static_cast<int>(edge.root_frontier_kind));
  return key;
}

std::string buildVipContextFingerprint(
    llvm::StringRef function_name,
    llvm::ArrayRef<UnresolvedExitSite> unresolved_exits) {
  std::vector<std::string> identities;
  for (const auto &site : unresolved_exits) {
    if (site.owner_function != function_name)
      continue;
    identities.push_back(unresolvedExitIdentity(site));
  }
  std::sort(identities.begin(), identities.end());
  std::string fingerprint;
  for (size_t i = 0; i < identities.size(); ++i) {
    if (i)
      fingerprint += ";";
    fingerprint += identities[i];
  }
  return fingerprint;
}

unsigned boundaryContinuationSiteIndex(uint64_t boundary_pc,
                                       uint64_t continuation_pc) {
  const uint64_t mixed =
      (boundary_pc >> 4u) ^ (continuation_pc << 1u) ^ 0x0b0d0000u;
  return 0x80000000u | static_cast<unsigned>(mixed & 0x7fffffffu);
}

void promoteBoundaryReentrySeed(DevirtualizationSession &session,
                                uint64_t target_pc) {
  auto promoteItem = [&](FrontierWorkItem &edge_like) {
    if (!edge_like.target_pc || *edge_like.target_pc != target_pc ||
        edge_like.from_boundary_continuation) {
      return;
    }
    edge_like.continuation_confidence = ContinuationConfidence::kTrusted;
    edge_like.continuation_liveness = ContinuationLiveness::kLive;
    edge_like.scheduling_class = FrontierSchedulingClass::kTrustedLive;
    edge_like.continuation_rationale = "boundary_reentry_nearby_seed";
    if (edge_like.status == FrontierWorkStatus::kInvalidated ||
        edge_like.failure_reason == "quarantined_selector_arm_deferred") {
      edge_like.status = FrontierWorkStatus::kPending;
      edge_like.failure_reason.clear();
    }
  };

  auto promoteEdge = [&](SessionEdgeFact &edge_like) {
    if (!edge_like.target_pc || *edge_like.target_pc != target_pc ||
        edge_like.from_boundary_continuation) {
      return;
    }
    edge_like.continuation_confidence = ContinuationConfidence::kTrusted;
    edge_like.continuation_liveness = ContinuationLiveness::kLive;
    edge_like.scheduling_class = FrontierSchedulingClass::kTrustedLive;
    edge_like.continuation_rationale = "boundary_reentry_nearby_seed";
    if (edge_like.status == FrontierWorkStatus::kInvalidated ||
        edge_like.failure_reason == "quarantined_selector_arm_deferred") {
      edge_like.status = FrontierWorkStatus::kPending;
      edge_like.failure_reason.clear();
    }
    ContinuationProof proof;
    proof.edge_identity = edge_like.identity;
    proof.raw_target_pc = *edge_like.target_pc;
    proof.effective_target_pc =
        edge_like.executable_target && edge_like.executable_target->effective_target_pc
            ? edge_like.executable_target->effective_target_pc
            : edge_like.target_pc;
    proof.source_handler_name = edge_like.owner_function;
    proof.provenance = ContinuationProvenance::kExecutablePlaceholder;
    proof.confidence = ContinuationConfidence::kTrusted;
    proof.liveness = ContinuationLiveness::kLive;
    proof.scheduling_class = FrontierSchedulingClass::kTrustedLive;
    proof.is_trusted_entry = true;
    proof.resolution_kind = ContinuationResolutionKind::kTrustedEntry;
    proof.import_disposition = ContinuationImportDisposition::kRetryable;
    proof.selected_root_import_class = ChildImportClass::kClosedSliceRoot;
    proof.rationale = "boundary_reentry_nearby_seed";
    edge_like.continuation_proof = std::move(proof);
    edge_like.is_dirty = true;
  };

  for (auto &existing : session.late_frontier_work_items)
    promoteItem(existing);
  for (auto &[identity, edge] : session.graph.edge_facts_by_identity) {
    (void)identity;
    promoteEdge(edge);
  }
}

std::string makeBoundaryContinuationIdentity(
    const BoundaryFact &boundary,
    std::optional<uint64_t> continuation_target_pc = std::nullopt) {
  const auto target_pc = continuation_target_pc ? continuation_target_pc
                                                : boundary.continuation_pc;
  if (!boundary.boundary_pc || !target_pc)
    return {};
  std::string identity = "boundary-continuation:";
  identity += llvm::utohexstr(*boundary.boundary_pc);
  identity += ":";
  identity += llvm::utohexstr(*target_pc);
  identity += ":";
  if (boundary.native_target_pc)
    identity += llvm::utohexstr(*boundary.native_target_pc);
  identity += ":";
  if (boundary.continuation_slot_id)
    identity += std::to_string(*boundary.continuation_slot_id);
  identity += ":";
  if (boundary.continuation_stack_cell_id)
    identity += std::to_string(*boundary.continuation_stack_cell_id);
  return identity;
}

std::optional<uint64_t> effectiveBoundaryContinuationTarget(
    const BoundaryFact &boundary) {
  if (boundary.continuation_entry_transform &&
      boundary.continuation_entry_transform->jump_target_pc) {
    return boundary.continuation_entry_transform->jump_target_pc;
  }
  if (boundary.suppresses_normal_fallthrough)
    return boundary.controlled_return_pc;
  return boundary.continuation_pc;
}

FrontierWorkItem makeBoundaryContinuationWorkItem(const BoundaryFact &boundary,
                                                  llvm::StringRef source_name,
                                                  std::optional<uint64_t> source_pc) {
  FrontierWorkItem item;
  const auto continuation_target_pc = effectiveBoundaryContinuationTarget(boundary);
  if (!continuation_target_pc)
    return item;
  item.owner_function =
      source_name.empty() ? "__boundary_continuation__" : source_name.str();
  item.site_index = boundary.boundary_pc
                        ? boundaryContinuationSiteIndex(*boundary.boundary_pc,
                                                         *continuation_target_pc)
                        : boundaryContinuationSiteIndex(*continuation_target_pc,
                                                         *continuation_target_pc);
  item.site_pc = source_pc ? source_pc : boundary.boundary_pc;
  item.target_pc = continuation_target_pc;
  item.root_frontier_kind = VirtualRootFrontierKind::kCall;
  item.boundary = boundary;
  item.continuation_confidence = ContinuationConfidence::kTrusted;
  item.continuation_liveness = ContinuationLiveness::kLive;
  item.scheduling_class = FrontierSchedulingClass::kTrustedLive;
  item.continuation_rationale = "boundary_reentry_continuation";
  item.kind = (boundary.covered_entry_pc.has_value() ||
               boundary.continuation_entry_transform.has_value())
                  ? FrontierWorkKind::kIntraOwnerContinuation
                  : FrontierWorkKind::kBoundaryContinuation;
  item.status = FrontierWorkStatus::kPending;
  item.identity = makeBoundaryContinuationIdentity(boundary, continuation_target_pc);
  item.from_boundary_continuation = true;
  ExecutableTargetFact fact;
  fact.raw_target_pc = *continuation_target_pc;
  fact.effective_target_pc = *continuation_target_pc;
  fact.kind = ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = ExecutableTargetTrust::kTrustedEntry;
  item.executable_target = fact;
  classifyContinuationCandidate(item);
  return item;
}

FrontierWorkItem makeFrontierWorkItem(const UnresolvedExitSite &site) {
  FrontierWorkItem item;
  item.owner_function = site.owner_function;
  item.site_index = site.site_index;
  item.site_pc = site.site_pc;
  item.target_pc = site.target_pc;
  item.root_frontier_kind =
      site.kind == UnresolvedExitKind::kDispatchCall
          ? VirtualRootFrontierKind::kCall
          : VirtualRootFrontierKind::kDispatch;
  item.vip_pc = site.vip_pc;
  item.vip_symbolic = site.vip_symbolic;
  BoundaryFact fact;
  fact.boundary_pc = site.target_pc;
  fact.continuation_vip_pc = site.continuation_vip_pc;
  fact.continuation_slot_id = site.continuation_slot_id;
  fact.continuation_stack_cell_id = site.continuation_stack_cell_id;
  fact.exit_disposition =
      boundaryDispositionFromVirtualExitDisposition(site.exit_disposition);
  fact.is_vm_enter = site.exit_disposition == VirtualExitDisposition::kVmEnter;
  fact.is_nested_vm_enter =
      site.exit_disposition == VirtualExitDisposition::kNestedVmEnter;
  fact.kind =
      fact.is_nested_vm_enter ? BoundaryKind::kNestedVmEnterBoundary
                              : (fact.is_vm_enter
                                     ? BoundaryKind::kVmEnterBoundary
                                     : (site.exit_disposition ==
                                                VirtualExitDisposition::
                                                    kVmExitTerminal
                                            ? BoundaryKind::kTerminalBoundary
                                            : BoundaryKind::kContinuation));
  item.boundary = fact;
  item.identity = unresolvedExitIdentity(site);
  item.status = site.completeness == ExitCompleteness::kInvalidated
                    ? FrontierWorkStatus::kInvalidated
                    : FrontierWorkStatus::kPending;
  classifyContinuationCandidate(item);
  return item;
}

std::vector<FrontierWorkItem> collectFrontierWorkItems(
    llvm::ArrayRef<UnresolvedExitSite> unresolved_exits) {
  std::vector<FrontierWorkItem> work_items;
  for (const auto &site : unresolved_exits) {
    if (!site.target_pc)
      continue;
    if (site.kind != UnresolvedExitKind::kDispatchJump &&
        site.kind != UnresolvedExitKind::kDispatchCall &&
        site.kind != UnresolvedExitKind::kUnknownContinuation) {
      continue;
    }
    work_items.push_back(makeFrontierWorkItem(site));
  }
  return work_items;
}

FrontierWorkItem makeClosureFrontierWorkItem(
    const OutputRootClosureWorkItem &closure_item) {
  FrontierWorkItem item;
  item.owner_function = closure_item.owner_function;
  item.site_index = closure_item.site_index;
  item.site_pc = closure_item.site_pc;
  item.target_pc = closure_item.target_pc;
  item.root_frontier_kind =
      closure_item.source_kind == OutputRootClosureSourceKind::kConstantDispatchTarget
          ? VirtualRootFrontierKind::kDispatch
          : VirtualRootFrontierKind::kCall;
  item.vip_symbolic = closure_item.vip_symbolic;
  item.boundary = closure_item.boundary;
  item.executable_target = closure_item.executable_target;
  item.identity = "closure:" + closure_item.identity;
  item.status = FrontierWorkStatus::kPending;
  classifyContinuationCandidate(item);
  return item;
}

FrontierWorkItem frontierWorkItemFromEdgeFact(const SessionEdgeFact &edge) {
  FrontierWorkItem item;
  item.owner_function = edge.owner_function;
  item.site_index = edge.site_index;
  item.site_pc = edge.site_pc;
  item.target_pc = edge.target_pc;
  item.root_frontier_kind = edge.root_frontier_kind;
  item.vip_pc = edge.vip_pc;
  item.vip_symbolic = edge.vip_symbolic;
  item.boundary = edge.boundary;
  item.executable_target = edge.executable_target;
  item.continuation_confidence = edge.continuation_confidence;
  item.continuation_liveness = edge.continuation_liveness;
  item.scheduling_class = edge.scheduling_class;
  item.continuation_rationale = edge.continuation_rationale;
  item.kind = edge.kind;
  item.status = edge.status;
  item.retry_count = edge.retry_count;
  item.failure_reason = edge.failure_reason;
  item.identity = edge.identity;
  item.from_boundary_continuation = edge.from_boundary_continuation;
  if (edge.continuation_proof) {
    item.continuation_confidence = edge.continuation_proof->confidence;
    item.continuation_liveness = edge.continuation_proof->liveness;
    item.scheduling_class = edge.continuation_proof->scheduling_class;
    if (!edge.continuation_proof->rationale.empty())
      item.continuation_rationale = edge.continuation_proof->rationale;
  }
  return item;
}

void syncEdgeFactFromFrontierWorkItem(SessionEdgeFact &edge,
                                      const FrontierWorkItem &item) {
  edge.owner_function = item.owner_function;
  edge.site_index = item.site_index;
  edge.site_pc = item.site_pc;
  edge.target_pc = item.target_pc;
  edge.root_frontier_kind = item.root_frontier_kind;
  edge.vip_pc = item.vip_pc;
  edge.vip_symbolic = item.vip_symbolic;
  edge.boundary = item.boundary;
  edge.executable_target = item.executable_target;
  edge.continuation_confidence = item.continuation_confidence;
  edge.continuation_liveness = item.continuation_liveness;
  edge.scheduling_class = item.scheduling_class;
  edge.continuation_rationale = item.continuation_rationale;
  edge.kind = item.kind;
  edge.status = item.status;
  edge.retry_count = item.retry_count;
  edge.failure_reason = item.failure_reason;
  edge.from_boundary_continuation = item.from_boundary_continuation;
  edge.is_dirty = false;
}

ContinuationProvenance classifyContinuationProvenance(
    const FrontierWorkItem &item) {
  if (item.boundary) {
    if (item.boundary->suppresses_normal_fallthrough &&
        item.boundary->return_address_control_kind !=
            VirtualReturnAddressControlKind::kUnknown) {
      return ContinuationProvenance::kReturnAddressControlled;
    }
    switch (boundaryDisposition(item.boundary)) {
      case VirtualExitDisposition::kVmEnter:
      case VirtualExitDisposition::kNestedVmEnter:
        return ContinuationProvenance::kVmEnterBoundary;
      case VirtualExitDisposition::kVmExitTerminal:
        return ContinuationProvenance::kTerminalBoundary;
      case VirtualExitDisposition::kVmExitNativeCallReenter:
      case VirtualExitDisposition::kVmExitNativeExecUnknownReturn:
        return ContinuationProvenance::kNativeBoundary;
      case VirtualExitDisposition::kUnknown:
      case VirtualExitDisposition::kStayInVm:
        break;
    }
  }
  if (item.executable_target) {
    if (item.executable_target->exact_fallthrough_target)
      return ContinuationProvenance::kExactFallthrough;
    if (item.executable_target->invalidated_executable_entry)
      return ContinuationProvenance::kInvalidatedExecutableEntry;
    return ContinuationProvenance::kExecutablePlaceholder;
  }
  if (item.identity.find("closure:") == 0)
    return ContinuationProvenance::kSelectorDerived;
  return ContinuationProvenance::kUnknown;
}

ContinuationResolutionKind classifyContinuationResolutionKind(
    const ContinuationCandidate &candidate) {
  switch (candidate.provenance) {
    case ContinuationProvenance::kExactFallthrough:
      return ContinuationResolutionKind::kExactFallthrough;
    case ContinuationProvenance::kInvalidatedExecutableEntry:
      return ContinuationResolutionKind::kInvalidatedExecutableEntry;
    case ContinuationProvenance::kReturnAddressControlled:
      return ContinuationResolutionKind::kTrustedEntry;
    case ContinuationProvenance::kNativeBoundary:
    case ContinuationProvenance::kVmEnterBoundary:
      return ContinuationResolutionKind::kBoundaryModeled;
    case ContinuationProvenance::kTerminalBoundary:
      return ContinuationResolutionKind::kTerminalModeled;
    case ContinuationProvenance::kSelectorDerived:
      return ContinuationResolutionKind::kQuarantinedSelectorArm;
    case ContinuationProvenance::kExecutablePlaceholder:
      if (candidate.canonical_owner_pc)
        return ContinuationResolutionKind::kCanonicalOwnerRedirect;
      if (candidate.confidence == ContinuationConfidence::kTrusted)
        return ContinuationResolutionKind::kTrustedEntry;
      break;
    case ContinuationProvenance::kUnknown:
      break;
  }
  if (candidate.confidence == ContinuationConfidence::kTrusted)
    return ContinuationResolutionKind::kTrustedEntry;
  if (candidate.scheduling_class == FrontierSchedulingClass::kTerminalModeled)
    return ContinuationResolutionKind::kTerminalModeled;
  return ContinuationResolutionKind::kUnknown;
}

ContinuationImportDisposition classifyContinuationImportDisposition(
    const ContinuationCandidate &candidate,
    ContinuationResolutionKind resolution_kind) {
  if (candidate.liveness == ContinuationLiveness::kQuarantined)
    return ContinuationImportDisposition::kDeferred;
  switch (resolution_kind) {
    case ContinuationResolutionKind::kExactFallthrough:
    case ContinuationResolutionKind::kTrustedEntry:
    case ContinuationResolutionKind::kCanonicalOwnerRedirect:
    case ContinuationResolutionKind::kBoundaryModeled:
      return ContinuationImportDisposition::kImportable;
    case ContinuationResolutionKind::kInvalidatedExecutableEntry:
      return candidate.confidence == ContinuationConfidence::kTrusted
                 ? ContinuationImportDisposition::kRetryable
                 : ContinuationImportDisposition::kRejected;
    case ContinuationResolutionKind::kQuarantinedSelectorArm:
      return ContinuationImportDisposition::kDeferred;
    case ContinuationResolutionKind::kTerminalModeled:
      return ContinuationImportDisposition::kRetryable;
    case ContinuationResolutionKind::kUnknown:
      break;
  }
  if (candidate.confidence == ContinuationConfidence::kWeak)
    return ContinuationImportDisposition::kRetryable;
  return ContinuationImportDisposition::kRejected;
}

ContinuationProof buildContinuationProof(const ContinuationCandidate &candidate) {
  ContinuationProof proof;
  proof.edge_identity = candidate.edge_identity;
  proof.raw_target_pc = candidate.raw_target_pc.value_or(0);
  proof.effective_target_pc = candidate.effective_target_pc;
  proof.canonical_owner_pc = candidate.canonical_owner_pc;
  proof.source_handler_name = candidate.source_handler_name;
  proof.provenance = candidate.provenance;
  proof.confidence = candidate.confidence;
  proof.liveness = candidate.liveness;
  proof.scheduling_class = candidate.scheduling_class;
  proof.is_trusted_entry =
      candidate.confidence == ContinuationConfidence::kTrusted;
  if (candidate.executable_target) {
    proof.is_exact_fallthrough =
        candidate.executable_target->exact_fallthrough_target;
    proof.is_invalidated_entry =
        candidate.executable_target->invalidated_executable_entry;
    proof.invalidated_entry_source_pc =
        candidate.executable_target->invalidated_entry_source_pc;
    proof.invalidated_entry_failed_pc =
        candidate.executable_target->invalidated_entry_failed_pc;
  }
  proof.return_address_control_kind = candidate.return_address_control_kind;
  proof.controlled_return_pc = candidate.controlled_return_pc;
  proof.suppresses_normal_fallthrough =
      candidate.suppresses_normal_fallthrough;
  proof.resolution_kind = classifyContinuationResolutionKind(candidate);
  proof.import_disposition =
      classifyContinuationImportDisposition(candidate, proof.resolution_kind);
  switch (proof.resolution_kind) {
    case ContinuationResolutionKind::kExactFallthrough:
    case ContinuationResolutionKind::kTrustedEntry:
    case ContinuationResolutionKind::kCanonicalOwnerRedirect:
      proof.selected_root_import_class =
          ChildImportClass::kTrustedTerminalEntry;
      break;
    case ContinuationResolutionKind::kBoundaryModeled:
      proof.selected_root_import_class = ChildImportClass::kBoundaryModeledChild;
      break;
    case ContinuationResolutionKind::kTerminalModeled:
      proof.selected_root_import_class = ChildImportClass::kTerminalOnlyUnknown;
      break;
    default:
      break;
  }
  proof.rationale = candidate.rationale;
  return proof;
}

void classifyContinuationCandidate(FrontierWorkItem &item) {
  const auto provenance = classifyContinuationProvenance(item);
  switch (provenance) {
    case ContinuationProvenance::kExactFallthrough:
      item.continuation_confidence = ContinuationConfidence::kTrusted;
      item.continuation_liveness = ContinuationLiveness::kLive;
      item.scheduling_class = FrontierSchedulingClass::kTrustedLive;
      item.continuation_rationale = "exact_fallthrough";
      return;
    case ContinuationProvenance::kReturnAddressControlled:
      item.continuation_confidence = ContinuationConfidence::kTrusted;
      item.continuation_liveness = ContinuationLiveness::kLive;
      item.scheduling_class = FrontierSchedulingClass::kTrustedLive;
      item.continuation_rationale = "return_address_controlled";
      return;
    case ContinuationProvenance::kNativeBoundary:
    case ContinuationProvenance::kVmEnterBoundary:
      item.continuation_confidence = ContinuationConfidence::kTrusted;
      item.continuation_liveness = ContinuationLiveness::kLive;
      item.scheduling_class = FrontierSchedulingClass::kNativeOrVmEnterBoundary;
      item.continuation_rationale = toString(provenance);
      return;
    case ContinuationProvenance::kTerminalBoundary:
      item.continuation_confidence = ContinuationConfidence::kWeak;
      item.continuation_liveness = ContinuationLiveness::kUnknown;
      item.scheduling_class = FrontierSchedulingClass::kTerminalModeled;
      item.continuation_rationale = "terminal_boundary";
      return;
    case ContinuationProvenance::kInvalidatedExecutableEntry:
      item.continuation_confidence = ContinuationConfidence::kDeadArmSuspect;
      item.continuation_liveness = ContinuationLiveness::kQuarantined;
      item.scheduling_class =
          FrontierSchedulingClass::kQuarantinedSelectorArm;
      item.continuation_rationale = "invalidated_executable_entry";
      return;
    case ContinuationProvenance::kSelectorDerived:
      item.continuation_confidence = ContinuationConfidence::kDeadArmSuspect;
      item.continuation_liveness = ContinuationLiveness::kQuarantined;
      item.scheduling_class =
          FrontierSchedulingClass::kQuarantinedSelectorArm;
      item.continuation_rationale = "selector_derived";
      return;
    case ContinuationProvenance::kExecutablePlaceholder:
      item.continuation_confidence = item.executable_target &&
                                             item.executable_target
                                                 ->canonical_owner_pc.has_value()
                                         ? ContinuationConfidence::kTrusted
                                         : ContinuationConfidence::kWeak;
      item.continuation_liveness =
          item.continuation_confidence == ContinuationConfidence::kTrusted
              ? ContinuationLiveness::kLive
              : ContinuationLiveness::kUnknown;
      item.scheduling_class =
          item.continuation_confidence == ContinuationConfidence::kTrusted
              ? FrontierSchedulingClass::kTrustedLive
              : FrontierSchedulingClass::kWeakExecutable;
      item.continuation_rationale = "executable_placeholder";
      return;
    case ContinuationProvenance::kUnknown:
      break;
  }
  item.continuation_confidence = ContinuationConfidence::kWeak;
  item.continuation_liveness = ContinuationLiveness::kUnknown;
  item.scheduling_class = FrontierSchedulingClass::kWeakExecutable;
  item.continuation_rationale = "generic_continuation";
}

struct SessionGraphRefreshSummary {
  unsigned dirty_edge_facts = 0;
  unsigned dirty_boundary_facts = 0;
  unsigned dirty_root_slices = 0;
  unsigned dirty_regions = 0;
  unsigned rebuilt_boundary_facts = 0;
  unsigned rebuilt_root_slices = 0;
  unsigned rebuilt_regions = 0;
};

std::optional<ContinuationCandidate> continuationCandidateFromEdge(
    const SessionEdgeFact &edge);
ProtectorModel buildProtectorModelFromSession(
    const DevirtualizationSession &session);
void applyProtectorModelToSession(DevirtualizationSession &session,
                                  const ProtectorModel &model);
void classifyContinuationCandidate(FrontierWorkItem &item);

bool isImportedVmEnterChildFunction(const llvm::Function &F, uint64_t target_pc) {
  if (F.isDeclaration())
    return false;
  if (F.getName().equals_insensitive(
          "omill_vm_enter_target_" + llvm::utohexstr(target_pc))) {
    return false;
  }
  auto entry_va = extractLiftUnitVA(F);
  return entry_va && *entry_va == target_pc;
}

void collectDirtyFunctionsAndSites(DevirtualizationSession &session,
                                   const llvm::Module &M) {
  auto &graph = session.graph;
  graph.dirty_function_names.clear();
  graph.dirty_edge_identities.clear();
  graph.dirty_root_vas.clear();

  for (const auto &name : session.dirty_functions)
    graph.dirty_function_names.insert(name);
  for (const auto &name : session.newly_lifted_functions)
    graph.dirty_function_names.insert(name);

  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    if (!edge.is_dirty)
      continue;
    graph.dirty_edge_identities.insert(identity);
    if (!edge.owner_function.empty())
      graph.dirty_function_names.insert(edge.owner_function);
  }

  for (uint64_t root_va : session.root_slice)
    graph.dirty_root_vas.insert(root_va);

  if (graph.handler_nodes.empty()) {
    for (const auto &F : M) {
      if (!isTrackedLiftUnit(F) && !F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice_root")) {
        continue;
      }
      graph.dirty_function_names.insert(F.getName().str());
      if (auto entry_va = extractLiftUnitVA(F))
        graph.dirty_root_vas.insert(*entry_va);
    }
  }
}

void refreshHandlerLocalFacts(DevirtualizationSession &session,
                              const llvm::Module &M) {
  auto &graph = session.graph;
  const bool incremental_refresh = !graph.handler_nodes.empty();
  std::set<std::string> live_names;
  std::vector<std::string> refresh_names;
  if (incremental_refresh) {
    refresh_names.reserve(graph.handler_nodes.size() + graph.dirty_function_names.size());
    for (const auto &[name, _] : graph.handler_nodes) {
      (void)_;
      refresh_names.push_back(name);
      live_names.insert(name);
    }
    for (const auto &name : graph.dirty_function_names) {
      if (live_names.insert(name).second)
        refresh_names.push_back(name);
    }
  }

  auto refresh_node_from_function = [&](const llvm::Function &F) {
    const std::string name = F.getName().str();
    live_names.insert(name);
    auto *node = &graph.handler_nodes[name];
    const llvm::stable_hash new_fingerprint =
        virtual_model::detail::summaryRelevantFunctionFingerprint(F);
    const bool fingerprint_changed = node->fingerprint != new_fingerprint;
    node->function_name = name;
    node->entry_va = extractLiftUnitVA(F);
    node->fingerprint = new_fingerprint;
    node->is_defined = !F.isDeclaration();
    node->is_output_root = F.hasFnAttribute("omill.output_root");
    node->is_closed_root_slice_root =
        F.hasFnAttribute("omill.closed_root_slice_root");
    node->is_specialized = F.hasFnAttribute("omill.virtual_specialized");
    node->is_dirty = graph.dirty_function_names.count(name) != 0;
    node->is_preferred_seed = F.hasFnAttribute("omill.output_root") ||
                              F.hasFnAttribute("omill.virtual_specialized") ||
                              F.hasFnAttribute("omill.closed_root_slice_root") ||
                              F.hasFnAttribute("omill.vm_wrapper") ||
                              F.hasFnAttribute("omill.vm_newly_lifted") ||
                              F.hasFnAttribute("omill.newly_lifted") ||
                              F.getFnAttribute("omill.vm_demerged_clone")
                                  .isValid() ||
                              F.getFnAttribute("omill.vm_outlined_virtual_call")
                                  .isValid();
    node->is_initial_seed = virtual_model::detail::isVirtualModelInitialSeedFunction(F);
    node->is_code_bearing = virtual_model::detail::isVirtualModelCodeBearingFunction(F);
    if (node->is_defined) {
      if (!node->local_summary.has_value() || node->is_dirty ||
          fingerprint_changed ||
          node->local_summary->function_name != name ||
          node->local_summary->entry_va != node->entry_va) {
        node->local_summary = virtual_model::detail::summarizeFunction(
            const_cast<llvm::Function &>(F));
      }
    } else {
      node->local_summary.reset();
    }
    if (node->entry_va &&
        (node->is_dirty || fingerprint_changed ||
         graph.root_slices_by_va.count(*node->entry_va) == 0))
      graph.dirty_root_vas.insert(*node->entry_va);
  };

  if (incremental_refresh) {
    std::set<std::string> refreshed_names;
    for (const auto &name : refresh_names) {
      if (!refreshed_names.insert(name).second)
        continue;
      auto *F = M.getFunction(name);
      if (!F || !isSessionGraphTrackedFunction(*F)) {
        graph.handler_nodes.erase(name);
        continue;
      }
      refresh_node_from_function(*F);
    }
  } else {
    for (const auto &F : M) {
      if (!isSessionGraphTrackedFunction(F))
        continue;
      refresh_node_from_function(F);
    }

    for (auto it = graph.handler_nodes.begin(); it != graph.handler_nodes.end();) {
      if (live_names.count(it->first) != 0) {
        ++it;
        continue;
      }
      it = graph.handler_nodes.erase(it);
    }
  }
}

SessionGraphRefreshSummary refreshSessionEdgesAndFrontier(
    DevirtualizationSession &session) {
  auto &graph = session.graph;
  SessionGraphRefreshSummary summary;
  std::set<std::string> active_unresolved_edges;
  std::set<uint64_t> dirty_boundary_targets;
  for (const auto &site : session.unresolved_exits) {
    if (!site.target_pc)
      continue;
    if (site.kind != UnresolvedExitKind::kDispatchJump &&
        site.kind != UnresolvedExitKind::kDispatchCall &&
        site.kind != UnresolvedExitKind::kUnknownContinuation) {
      continue;
    }
    FrontierWorkItem work_item = makeFrontierWorkItem(site);
    active_unresolved_edges.insert(work_item.identity);
    auto it = graph.edge_facts_by_identity.find(work_item.identity);
    bool inserted = false;
    if (it == graph.edge_facts_by_identity.end()) {
      const auto stable_key = frontierStableSiteKey(work_item);
      it = llvm::find_if(graph.edge_facts_by_identity, [&](const auto &entry) {
        return edgeStableSiteKey(entry.second) == stable_key;
      });
      if (it != graph.edge_facts_by_identity.end()) {
        SessionEdgeFact preserved = std::move(it->second);
        graph.edge_facts_by_identity.erase(it);
        auto inserted_it = graph.edge_facts_by_identity.emplace(
            work_item.identity, std::move(preserved));
        it = inserted_it.first;
        it->second.identity = work_item.identity;
      } else {
        auto inserted_it = graph.edge_facts_by_identity.emplace(
            work_item.identity, SessionEdgeFact{});
        it = inserted_it.first;
        inserted = true;
      }
    }
    auto &edge = it->second;
    const auto old_target_pc = edge.target_pc;
    const auto preserved_kind = edge.kind;
    const auto preserved_status = edge.status;
    const auto preserved_retry_count = edge.retry_count;
    const auto preserved_failure_reason = edge.failure_reason;
    bool edge_dirty = false;
    if (inserted) {
      edge.identity = work_item.identity;
      edge_dirty = true;
    } else if (edge.target_pc != work_item.target_pc ||
               edge.boundary != work_item.boundary ||
               edge.vip_pc != work_item.vip_pc ||
               edge.vip_symbolic != work_item.vip_symbolic) {
      edge_dirty = true;
    }
    const bool preserve_frontier_outcome =
        !inserted && edge.target_pc == work_item.target_pc &&
        edge.status != FrontierWorkStatus::kPending &&
        edge.status != FrontierWorkStatus::kInvalidated &&
        work_item.status != FrontierWorkStatus::kInvalidated;
    syncEdgeFactFromFrontierWorkItem(edge, work_item);
    if (!inserted && (!edge_dirty || preserve_frontier_outcome)) {
      edge.kind = preserved_kind;
      edge.status = preserved_status;
      edge.retry_count = preserved_retry_count;
      edge.failure_reason = preserved_failure_reason;
    }
    edge.is_dirty = edge_dirty || inserted ||
                    session.graph.dirty_function_names.count(edge.owner_function) !=
                        0;
    edge.from_unresolved_exit = true;
    if (edge.is_dirty) {
      ++summary.dirty_edge_facts;
      if (old_target_pc && old_target_pc != edge.target_pc)
        dirty_boundary_targets.insert(*old_target_pc);
      if (edge.target_pc)
        dirty_boundary_targets.insert(*edge.target_pc);
    }
  }

  for (auto it = graph.edge_facts_by_identity.begin();
       it != graph.edge_facts_by_identity.end();) {
    if (!it->second.from_unresolved_exit ||
        active_unresolved_edges.count(it->first) != 0) {
      ++it;
      continue;
    }
    if (it->second.target_pc)
      dirty_boundary_targets.insert(*it->second.target_pc);
    it = graph.edge_facts_by_identity.erase(it);
  }

  std::set<uint64_t> active_boundary_targets;
  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc)
      continue;
    if (edge.kind != FrontierWorkKind::kNativeCallBoundary &&
        edge.kind != FrontierWorkKind::kTerminalBoundary &&
        edge.kind != FrontierWorkKind::kVmEnterBoundary) {
      continue;
    }
    active_boundary_targets.insert(*edge.target_pc);
    if (edge.is_dirty)
      dirty_boundary_targets.insert(*edge.target_pc);
  }

  for (auto it = graph.boundary_facts_by_target.begin();
       it != graph.boundary_facts_by_target.end();) {
    if (active_boundary_targets.count(it->first) != 0) {
      ++it;
      continue;
    }
    it = graph.boundary_facts_by_target.erase(it);
  }

  summary.dirty_boundary_facts =
      static_cast<unsigned>(dirty_boundary_targets.size());
  for (uint64_t target_pc : dirty_boundary_targets) {
    auto edge_it = llvm::find_if(graph.edge_facts_by_identity, [&](const auto &entry) {
      const auto &edge = entry.second;
      return edge.target_pc && *edge.target_pc == target_pc &&
             (edge.kind == FrontierWorkKind::kNativeCallBoundary ||
              edge.kind == FrontierWorkKind::kTerminalBoundary ||
              edge.kind == FrontierWorkKind::kVmEnterBoundary);
    });
    if (edge_it == graph.edge_facts_by_identity.end())
      continue;
    auto &boundary = graph.boundary_facts_by_target[target_pc];
    boundary.target_pc = target_pc;
    boundary.kind = edge_it->second.kind;
    boundary.boundary = edge_it->second.boundary;
    boundary.is_dirty = true;
    ++summary.rebuilt_boundary_facts;
  }

  return summary;
}

SessionGraphRefreshSummary refreshDerivedViewsAndLoweringInputs(
    DevirtualizationSession &session, const llvm::Module &M) {
  auto &graph = session.graph;
  SessionGraphRefreshSummary summary;
  std::set<uint64_t> active_root_vas;
  std::set<uint64_t> dirty_root_vas = graph.dirty_root_vas;
  for (const auto &[name, node] : graph.handler_nodes) {
    (void)name;
    if (!node.entry_va)
      continue;
    if (!node.is_output_root && !node.is_closed_root_slice_root &&
        llvm::find(session.root_slice, *node.entry_va) == session.root_slice.end()) {
      continue;
    }
    active_root_vas.insert(*node.entry_va);
    if (node.is_dirty || graph.root_slices_by_va.count(*node.entry_va) == 0)
      dirty_root_vas.insert(*node.entry_va);
  }
  summary.dirty_root_slices = static_cast<unsigned>(dirty_root_vas.size());

  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    (void)identity;
    auto handler_it = graph.handler_nodes.find(edge.owner_function);
    if (handler_it != graph.handler_nodes.end() && handler_it->second.entry_va &&
        active_root_vas.count(*handler_it->second.entry_va) != 0 && edge.is_dirty) {
      dirty_root_vas.insert(*handler_it->second.entry_va);
    }
  }

  for (auto it = graph.root_slices_by_va.begin();
       it != graph.root_slices_by_va.end();) {
    if (active_root_vas.count(it->first) != 0) {
      ++it;
      continue;
    }
    it = graph.root_slices_by_va.erase(it);
  }

  for (uint64_t root_va : dirty_root_vas) {
    auto handler_it = llvm::find_if(graph.handler_nodes, [&](const auto &entry) {
      return entry.second.entry_va && *entry.second.entry_va == root_va &&
             (entry.second.is_output_root || entry.second.is_closed_root_slice_root ||
              llvm::find(session.root_slice, root_va) != session.root_slice.end());
    });
    if (handler_it == graph.handler_nodes.end())
      continue;
    SessionRootSlice rebuilt;
    rebuilt.root_va = root_va;
    rebuilt.root_function = handler_it->second.function_name;
    rebuilt.is_dirty = handler_it->second.is_dirty;
    rebuilt.reachable_handler_names.push_back(handler_it->second.function_name);
    for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
      auto owner_it = graph.handler_nodes.find(edge.owner_function);
      if (owner_it == graph.handler_nodes.end() || !owner_it->second.entry_va ||
          *owner_it->second.entry_va != root_va) {
        continue;
      }
      rebuilt.frontier_edge_identities.push_back(identity);
      if (!edge.owner_function.empty())
        rebuilt.reachable_handler_names.push_back(edge.owner_function);
    }
    std::sort(rebuilt.reachable_handler_names.begin(),
              rebuilt.reachable_handler_names.end());
    rebuilt.reachable_handler_names.erase(
        std::unique(rebuilt.reachable_handler_names.begin(),
                    rebuilt.reachable_handler_names.end()),
        rebuilt.reachable_handler_names.end());
    rebuilt.is_closed = llvm::all_of(
        rebuilt.frontier_edge_identities, [&](const std::string &identity) {
          auto it = graph.edge_facts_by_identity.find(identity);
          if (it == graph.edge_facts_by_identity.end())
            return true;
          return it->second.status != FrontierWorkStatus::kPending &&
                 it->second.status != FrontierWorkStatus::kInvalidated;
        });
    graph.root_slices_by_va[root_va] = std::move(rebuilt);
    ++summary.rebuilt_root_slices;
  }

  std::set<uint64_t> active_region_targets;
  std::set<uint64_t> dirty_region_targets;
  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    (void)identity;
    if (edge.kind != FrontierWorkKind::kVmEnterBoundary || !edge.target_pc)
      continue;
    active_region_targets.insert(*edge.target_pc);
    if (edge.is_dirty || graph.region_nodes_by_entry_pc.count(*edge.target_pc) == 0)
      dirty_region_targets.insert(*edge.target_pc);
  }

  for (const auto &[target_pc, _] : session.imported_vm_enter_child_roots)
    dirty_region_targets.insert(target_pc);
  for (uint64_t target_pc : session.attempted_vm_enter_child_import_pcs)
    dirty_region_targets.insert(target_pc);
  summary.dirty_regions = static_cast<unsigned>(dirty_region_targets.size());

  for (auto it = graph.region_nodes_by_entry_pc.begin();
       it != graph.region_nodes_by_entry_pc.end();) {
    if (active_region_targets.count(it->first) != 0) {
      ++it;
      continue;
    }
    it = graph.region_nodes_by_entry_pc.erase(it);
  }

  for (uint64_t target_pc : dirty_region_targets) {
    if (active_region_targets.count(target_pc) == 0)
      continue;
    SessionRegionNode rebuilt;
    rebuilt.entry_pc = target_pc;
    rebuilt.kind = SessionRegionKind::kNestedVmEnter;
    rebuilt.status = SessionRegionStatus::kPending;
    for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
      if (edge.kind != FrontierWorkKind::kVmEnterBoundary || !edge.target_pc ||
          *edge.target_pc != target_pc) {
        continue;
      }
      rebuilt.is_dirty = rebuilt.is_dirty || edge.is_dirty;
      rebuilt.frontier_edge_identities.push_back(identity);
      auto handler_it = graph.handler_nodes.find(edge.owner_function);
      if (handler_it != graph.handler_nodes.end())
        rebuilt.parent_entry_pc = handler_it->second.entry_va;
      rebuilt.parent_target_pc = edge.target_pc;
    }

    if (auto imported_it = session.imported_vm_enter_child_roots.find(target_pc);
        imported_it != session.imported_vm_enter_child_roots.end()) {
      rebuilt.status = SessionRegionStatus::kImported;
      rebuilt.imported_root_function = imported_it->second;
    } else {
      for (const auto &F : M) {
        if (!isImportedVmEnterChildFunction(F, target_pc))
          continue;
        rebuilt.status = SessionRegionStatus::kImported;
        rebuilt.imported_root_function = F.getName().str();
        break;
      }
    }
    if (rebuilt.status != SessionRegionStatus::kImported &&
        session.attempted_vm_enter_child_import_pcs.count(target_pc) != 0) {
      rebuilt.status = SessionRegionStatus::kBlocked;
      if (rebuilt.failure_reason.empty())
        rebuilt.failure_reason = "child_import_not_materialized";
    }
    graph.region_nodes_by_entry_pc[target_pc] = std::move(rebuilt);
    ++summary.rebuilt_regions;
  }

  for (auto &[target_pc, boundary] : graph.boundary_facts_by_target) {
    if (!boundary.is_dirty && boundary.declaration_name.has_value())
      continue;
    auto &mutable_module = const_cast<llvm::Module &>(M);
    if (auto *fn = findStructuralCodeTargetFunctionByPC(mutable_module, target_pc))
      boundary.declaration_name = fn->getName().str();
    else if (auto *fn = findLiftedOrBlockFunctionByPC(mutable_module, target_pc))
      boundary.declaration_name = fn->getName().str();
    boundary.is_dirty = false;
  }
  return summary;
}

void publishSessionGraphProjectionImpl(const llvm::Module &M,
                                       const SessionGraphState &state) {
  SessionGraphProjectionCacheEntry entry;
  entry.module_fingerprint = llvm::StructuralHash(M);
  entry.projection_serial = nextSessionGraphProjectionSerial();
  entry.state = state;
  auto &mutable_module = const_cast<llvm::Module &>(M);
  auto *named =
      mutable_module.getOrInsertNamedMetadata(kSessionGraphProjectionSerialMetadata);
  named->clearOperands();
  named->addOperand(llvm::MDTuple::get(
      mutable_module.getContext(),
      {llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(
          llvm::Type::getInt64Ty(mutable_module.getContext()),
          entry.projection_serial))}));
  sessionGraphProjectionCache()[&M] = std::move(entry);
}

const SessionGraphState *findSessionGraphProjectionImpl(
    const llvm::Module &M) {
  auto &cache = sessionGraphProjectionCache();
  auto it = cache.find(&M);
  if (it == cache.end())
    return nullptr;
  if (it->second.module_fingerprint != llvm::StructuralHash(M) ||
      moduleSessionGraphProjectionSerial(M) != it->second.projection_serial) {
    cache.erase(it);
    return nullptr;
  }
  return &it->second.state;
}

SessionGraphState *findMutableSessionGraphProjectionImpl(llvm::Module &M) {
  auto &cache = sessionGraphProjectionCache();
  auto it = cache.find(&M);
  if (it == cache.end())
    return nullptr;
  const llvm::stable_hash fingerprint = llvm::StructuralHash(M);
  if (it->second.module_fingerprint != fingerprint ||
      moduleSessionGraphProjectionSerial(M) != it->second.projection_serial) {
    cache.erase(it);
    return nullptr;
  }
  return &it->second.state;
}

void refreshSessionGraphState(DevirtualizationSession &session,
                              const llvm::Module &M) {
  collectDirtyFunctionsAndSites(session, M);
  session.latest_round.dirty_handler_nodes =
      static_cast<unsigned>(session.graph.dirty_function_names.size());
  refreshHandlerLocalFacts(session, M);
  auto edge_summary = refreshSessionEdgesAndFrontier(session);
  auto derived_summary = refreshDerivedViewsAndLoweringInputs(session, M);
  session.latest_round.dirty_edge_facts = edge_summary.dirty_edge_facts;
  session.latest_round.dirty_boundary_facts =
      edge_summary.dirty_boundary_facts;
  session.latest_round.dirty_root_slices = derived_summary.dirty_root_slices;
  session.latest_round.dirty_regions = derived_summary.dirty_regions;
  session.latest_round.rebuilt_boundary_facts =
      edge_summary.rebuilt_boundary_facts;
  session.latest_round.rebuilt_root_slices =
      derived_summary.rebuilt_root_slices;
  session.latest_round.rebuilt_regions = derived_summary.rebuilt_regions;
  session.protector_model = buildProtectorModelFromSession(session);
  applyProtectorModelToSession(session, session.protector_model);
  publishSessionGraphProjectionImpl(M, session.graph);
}

std::optional<ContinuationCandidate> continuationCandidateFromEdge(
    const SessionEdgeFact &edge) {
  if (!edge.target_pc)
    return std::nullopt;
  ContinuationCandidate candidate;
  candidate.edge_identity = edge.identity;
  candidate.source_handler_name = edge.owner_function;
  candidate.raw_target_pc = edge.target_pc;
  candidate.executable_target = edge.executable_target;
  candidate.boundary = edge.boundary;
  candidate.provenance = [&]() {
    FrontierWorkItem item = frontierWorkItemFromEdgeFact(edge);
    return classifyContinuationProvenance(item);
  }();
  candidate.confidence = edge.continuation_confidence;
  candidate.liveness = edge.continuation_liveness;
  candidate.scheduling_class = edge.scheduling_class;
  candidate.rationale = edge.continuation_rationale;
  if (edge.boundary) {
    candidate.return_address_control_kind =
        edge.boundary->return_address_control_kind;
    candidate.controlled_return_pc = edge.boundary->controlled_return_pc;
    candidate.suppresses_normal_fallthrough =
        edge.boundary->suppresses_normal_fallthrough;
  }
  if (edge.executable_target) {
    candidate.effective_target_pc = edge.executable_target->effective_target_pc;
    candidate.canonical_owner_pc = edge.executable_target->canonical_owner_pc;
  }
  if ((!candidate.effective_target_pc || candidate.provenance ==
                                              ContinuationProvenance::kReturnAddressControlled) &&
      candidate.controlled_return_pc) {
    candidate.effective_target_pc = candidate.controlled_return_pc;
  }
  if (edge.continuation_proof)
    candidate.proof = edge.continuation_proof;
  return candidate;
}

ProtectorModel buildProtectorModelFromSession(
    const DevirtualizationSession &session) {
  ProtectorModel model;
  std::map<std::string, std::vector<size_t>> candidate_indices_by_site;
  for (const auto &[identity, edge] : session.graph.edge_facts_by_identity) {
    (void)identity;
    auto candidate = continuationCandidateFromEdge(edge);
    if (!candidate)
      continue;
    model.continuation_candidates.push_back(*candidate);
    std::string site_key = edge.owner_function + ":" +
                           std::to_string(edge.site_index) + ":";
    if (edge.site_pc)
      site_key += llvm::utohexstr(*edge.site_pc);
    candidate_indices_by_site[site_key].push_back(
        model.continuation_candidates.size() - 1);
    if (candidate->liveness == ContinuationLiveness::kQuarantined) {
      model.selector_outcomes_by_edge[candidate->edge_identity] =
          SelectorOutcome{candidate->edge_identity, candidate->raw_target_pc,
                          candidate->confidence, candidate->liveness,
                          candidate->rationale};
    }
  }

  for (const auto &[site_key, indices] : candidate_indices_by_site) {
    (void)site_key;
    if (indices.size() < 2)
      continue;

    bool has_trusted_structural_target = false;
    for (size_t index : indices) {
      const auto &candidate = model.continuation_candidates[index];
      if (candidate.provenance == ContinuationProvenance::kExactFallthrough ||
          candidate.provenance ==
              ContinuationProvenance::kReturnAddressControlled ||
          candidate.provenance == ContinuationProvenance::kNativeBoundary ||
          candidate.provenance == ContinuationProvenance::kVmEnterBoundary ||
          candidate.scheduling_class == FrontierSchedulingClass::kTrustedLive) {
        has_trusted_structural_target = true;
        break;
      }
    }
    if (!has_trusted_structural_target)
      continue;

    for (size_t index : indices) {
      auto &candidate = model.continuation_candidates[index];
      const bool preserve_existing_trusted_proof =
          candidate.proof && candidate.proof->confidence ==
                                 ContinuationConfidence::kTrusted &&
          candidate.proof->liveness == ContinuationLiveness::kLive &&
          candidate.proof->scheduling_class ==
              FrontierSchedulingClass::kTrustedLive &&
          candidate.proof->resolution_kind !=
              ContinuationResolutionKind::kQuarantinedSelectorArm &&
          candidate.proof->import_disposition !=
              ContinuationImportDisposition::kDeferred;
      if (candidate.provenance == ContinuationProvenance::kExactFallthrough ||
          candidate.provenance ==
              ContinuationProvenance::kReturnAddressControlled ||
          candidate.provenance == ContinuationProvenance::kNativeBoundary ||
          candidate.provenance == ContinuationProvenance::kVmEnterBoundary) {
        candidate.confidence = ContinuationConfidence::kTrusted;
        candidate.liveness = ContinuationLiveness::kLive;
        candidate.scheduling_class = FrontierSchedulingClass::kTrustedLive;
        if (candidate.rationale.empty())
          candidate.rationale = "trusted_structural_target";
        continue;
      }
      if (preserve_existing_trusted_proof)
        continue;
      if (candidate.provenance == ContinuationProvenance::kSelectorDerived ||
          candidate.provenance ==
              ContinuationProvenance::kInvalidatedExecutableEntry ||
          candidate.provenance ==
              ContinuationProvenance::kExecutablePlaceholder) {
        candidate.confidence = ContinuationConfidence::kDeadArmSuspect;
        candidate.liveness = ContinuationLiveness::kQuarantined;
        candidate.scheduling_class =
            FrontierSchedulingClass::kQuarantinedSelectorArm;
        candidate.rationale = "selector_sibling_of_trusted_target";
        model.selector_outcomes_by_edge[candidate.edge_identity] =
            SelectorOutcome{candidate.edge_identity, candidate.raw_target_pc,
                            candidate.confidence, candidate.liveness,
                            candidate.rationale};
      }
    }
  }

  for (auto &candidate : model.continuation_candidates)
    candidate.proof = buildContinuationProof(candidate);

  for (const auto &[root_va, slice] : session.graph.root_slices_by_va) {
    HandlerRegion region;
    region.id = "root:0x" + llvm::utohexstr(root_va);
    region.root_va = root_va;
    region.handler_names = slice.reachable_handler_names;
    if (!slice.root_function.empty())
      region.entry_handler_names.push_back(slice.root_function);
    region.frontier_edge_identities = slice.frontier_edge_identities;
    for (const auto &[entry_pc, node] : session.graph.region_nodes_by_entry_pc) {
      if (node.parent_entry_pc && *node.parent_entry_pc == root_va)
        region.child_entry_pcs.push_back(entry_pc);
    }
    model.handler_regions.push_back(std::move(region));
  }

  std::map<std::string, DispatcherFamily> families_by_anchor;
  for (const auto &candidate : model.continuation_candidates) {
    if (candidate.provenance != ContinuationProvenance::kSelectorDerived &&
        candidate.provenance != ContinuationProvenance::kExactFallthrough &&
        candidate.provenance !=
            ContinuationProvenance::kInvalidatedExecutableEntry) {
      continue;
    }
    auto &family = families_by_anchor[candidate.source_handler_name];
    family.anchor_handler_name = candidate.source_handler_name;
    family.id = "dispatcher:" + candidate.source_handler_name;
    family.handler_names.push_back(candidate.source_handler_name);
    family.continuation_edge_identities.push_back(candidate.edge_identity);
  }
  for (auto &[anchor, family] : families_by_anchor) {
    (void)anchor;
    std::sort(family.handler_names.begin(), family.handler_names.end());
    family.handler_names.erase(
        std::unique(family.handler_names.begin(), family.handler_names.end()),
        family.handler_names.end());
    std::sort(family.continuation_edge_identities.begin(),
              family.continuation_edge_identities.end());
    family.continuation_edge_identities.erase(
        std::unique(family.continuation_edge_identities.begin(),
                    family.continuation_edge_identities.end()),
        family.continuation_edge_identities.end());
    model.dispatcher_families.push_back(std::move(family));
  }

  return model;
}

void applyProtectorModelToSession(DevirtualizationSession &session,
                                  const ProtectorModel &model) {
  for (const auto &candidate : model.continuation_candidates) {
    auto it = session.graph.edge_facts_by_identity.find(candidate.edge_identity);
    if (it == session.graph.edge_facts_by_identity.end())
      continue;
    it->second.continuation_confidence = candidate.confidence;
    it->second.continuation_liveness = candidate.liveness;
    it->second.scheduling_class = candidate.scheduling_class;
    it->second.continuation_rationale = candidate.rationale;
    it->second.continuation_proof = candidate.proof;
  }
}

bool looksLikeNativeCallBoundary(uint64_t target_pc,
                                 const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[96] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return false;
  const bool looks_like_x64_prologue =
      (bytes[0] == 0x48 && bytes[1] == 0x83 && bytes[2] == 0xEC) ||
      (bytes[0] == 0x48 && bytes[1] == 0x89 && bytes[3] == 0x24) ||
      (bytes[0] == 0x40 && bytes[1] == 0x53) ||
      (bytes[0] == 0x55 && bytes[1] == 0x48 && bytes[2] == 0x8B);
  unsigned stack_setup_ops = 0;
  bool saw_pushfq = false;
  for (unsigned i = 0; i < 12 && i < sizeof(bytes); ++i) {
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
      case 0x9C:
      case 0x9D:
        ++stack_setup_ops;
        saw_pushfq = saw_pushfq || bytes[i] == 0x9C || bytes[i] == 0x9D;
        break;
      default:
        break;
    }
  }

    bool saw_early_direct_call = false;
    for (unsigned i = 0; i + 4 < sizeof(bytes) && i < 96; ++i) {
      if (bytes[i] == 0xE8) {
        saw_early_direct_call = true;
        break;
      }
    }
    if (!saw_early_direct_call)
      return false;
    return looks_like_x64_prologue || stack_setup_ops >= 4 || bytes[0] == 0xE8 ||
           (saw_pushfq && stack_setup_ops >= 2);
}

bool looksLikeNativeFunctionEntry(uint64_t target_pc,
                                  const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[64] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return false;

  auto looks_like_prologue_at = [&](unsigned i) {
    if (i + 2 < sizeof(bytes) && bytes[i] == 0x48 && bytes[i + 1] == 0x83 &&
        bytes[i + 2] == 0xEC) {
      return true;
    }
    if (i + 3 < sizeof(bytes) && bytes[i] == 0x48 && bytes[i + 1] == 0x89 &&
        bytes[i + 3] == 0x24) {
      return true;
    }
    if (i + 1 < sizeof(bytes) && bytes[i] == 0x40 && bytes[i + 1] == 0x53) {
      return true;
    }
    if (i + 2 < sizeof(bytes) && bytes[i] == 0x55 && bytes[i + 1] == 0x48 &&
        bytes[i + 2] == 0x8B) {
      return true;
    }
    return false;
  };

  auto has_early_unconditional_transfer = [&](unsigned limit) {
    for (unsigned i = 0; i < limit && i < sizeof(bytes); ++i) {
      if (bytes[i] == 0xE8)
        return false;
      if (bytes[i] == 0xC3 || bytes[i] == 0xC2 || bytes[i] == 0xE9 ||
          bytes[i] == 0xEB) {
        return true;
      }
      if (bytes[i] == 0xFF && i + 1 < sizeof(bytes)) {
        const uint8_t reg = (bytes[i + 1] >> 3) & 0x7u;
        // Indirect calls can still be a legitimate prologue-shaped native
        // entry; early indirect jumps are the shape we want to reject here.
        if (reg == 4u || reg == 5u)
          return true;
      }
    }
    return false;
  };

  if (looks_like_prologue_at(0)) {
    if (has_early_unconditional_transfer(24))
      return false;
    return true;
  }

  for (unsigned i = 1; i + 3 < sizeof(bytes) && i < 48; ++i) {
    if (!looks_like_prologue_at(i))
      continue;
    bool saw_branch_or_ret = false;
    for (unsigned j = 0; j < i; ++j) {
      if (bytes[j] == 0xC3 || bytes[j] == 0xC2 || bytes[j] == 0xE9 ||
          bytes[j] == 0xEB || (bytes[j] >= 0x70 && bytes[j] <= 0x7F) ||
          (bytes[j] == 0x0F && j + 1 < i && bytes[j + 1] >= 0x80 &&
           bytes[j + 1] <= 0x8F)) {
        saw_branch_or_ret = true;
        break;
      }
    }
    if (saw_branch_or_ret)
      return true;
  }
  return false;
}

bool looksLikeVmEnterBoundary(uint64_t target_pc,
                              const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[32] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
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

bool looksLikeTerminalBoundarySnippet(uint64_t target_pc,
                                      const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[16] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return false;
  if (bytes[0] == 0xC3 || bytes[0] == 0xC2)
    return true;

  for (unsigned i = 0; i < sizeof(bytes); ++i) {
    if (bytes[i] == 0xC3 || bytes[i] == 0xC2)
      return i >= 4;
    if (bytes[i] == 0xE8 || bytes[i] == 0xE9 || bytes[i] == 0xEB)
      return false;
    if (bytes[i] == 0xFF && i + 1 < sizeof(bytes)) {
      const uint8_t reg = (bytes[i + 1] >> 3) & 0x7;
      if (reg == 2 || reg == 3 || reg == 4 || reg == 5)
        return false;
    }
  }
  return false;
}

bool looksLikeJunkExecutableSnippet(uint64_t target_pc,
                                    const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[16] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return false;
  if (looksLikeVmEnterBoundary(target_pc, callbacks) ||
      looksLikeNativeCallBoundary(target_pc, callbacks) ||
      looksLikeNativeFunctionEntry(target_pc, callbacks) ||
      looksLikeTerminalBoundarySnippet(target_pc, callbacks)) {
    return false;
  }

  auto is_suspicious = [](uint8_t byte) {
    switch (byte) {
      case 0x60:  // pusha (invalid in x64 long mode)
      case 0x61:  // popa (invalid in x64 long mode)
      case 0x62:  // legacy bound/EVEX lead, very unlikely entry here
      case 0xC8:  // enter
      case 0xCA:  // lret imm16
      case 0xCB:  // lret
      case 0xCE:  // into / invalid in x64
      case 0xCF:  // iret
      case 0xE4:
      case 0xE5:
      case 0xE6:
      case 0xE7:
      case 0xEC:
      case 0xED:
      case 0xEE:
      case 0xEF:  // in/out I/O instructions
      case 0xF4:  // hlt
      case 0xFA:  // cli
      case 0xFB:  // sti
        return true;
      default:
        return false;
    }
  };

  unsigned suspicious = 0;
  for (unsigned i = 0; i < sizeof(bytes); ++i) {
    if (bytes[i] == 0xE8 || bytes[i] == 0xE9 || bytes[i] == 0xEB ||
        bytes[i] == 0xC3 || bytes[i] == 0xC2) {
      break;
    }
    if (is_suspicious(bytes[i]))
      ++suspicious;
  }
  return suspicious >= 2;
}

bool looksLikeNonEntryExecutableSnippet(uint64_t target_pc,
                                        const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[32] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return false;
  if (looksLikeVmEnterBoundary(target_pc, callbacks) ||
      looksLikeNativeCallBoundary(target_pc, callbacks) ||
      looksLikeNativeFunctionEntry(target_pc, callbacks) ||
      looksLikeTerminalBoundarySnippet(target_pc, callbacks) ||
      looksLikeJunkExecutableSnippet(target_pc, callbacks)) {
    return false;
  }

  for (unsigned i = 1; i + 1 < sizeof(bytes) && i < 24; ++i) {
    if (bytes[i] == 0xE9 || bytes[i] == 0xEB)
      return true;
    if (bytes[i] == 0xFF) {
      const uint8_t reg = (bytes[i + 1] >> 3) & 0x7u;
      if (reg == 4u || reg == 5u)
        return true;
    }
  }
  return false;
}

bool isExactX86DirectCallFallthrough(uint64_t target_pc,
                                     const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes || target_pc < 5)
    return false;
  uint8_t bytes[5] = {};
  const uint64_t call_pc = target_pc - 5;
  if (!callbacks.read_target_bytes(call_pc, bytes, sizeof(bytes)))
    return false;
  return bytes[0] == 0xE8;
}

struct NativeBoundaryDecodeSummary {
  std::optional<uint64_t> direct_call_target_pc;
  bool has_direct_call_fallthrough = false;
  std::optional<uint64_t> continuation_pc;
};

NativeBoundaryDecodeSummary decodeNativeBoundarySummary(
    uint64_t target_pc, const FrontierCallbacks &callbacks) {
  NativeBoundaryDecodeSummary summary;
  if (!callbacks.read_target_bytes)
    return summary;
  uint8_t bytes[192] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return summary;
  for (unsigned i = 0; i + 4 < sizeof(bytes); ++i) {
    if (bytes[i] != 0xE8)
      continue;
    int32_t rel = 0;
    std::memcpy(&rel, &bytes[i + 1], sizeof(rel));
    summary.direct_call_target_pc =
        static_cast<uint64_t>(static_cast<int64_t>(target_pc) +
                              static_cast<int64_t>(i) + 5 +
                              static_cast<int64_t>(rel));
    summary.has_direct_call_fallthrough = true;
    summary.continuation_pc = target_pc + i + 5;
    break;
  }
  return summary;
}

llvm::Function *getOrCreateDirectNativeTargetDecl(llvm::Module &M,
                                                  llvm::FunctionType *fn_ty,
                                                  uint64_t boundary_pc,
                                                  uint64_t target_pc) {
  std::string name = "omill_native_target_";
  name += llvm::utohexstr(target_pc);
  auto *callee = M.getFunction(name);
  if (!callee) {
    callee = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    name, M);
    BoundaryFact fact;
    fact.boundary_pc = boundary_pc;
    fact.native_target_pc = target_pc;
    fact.kind = BoundaryKind::kNativeBoundary;
    writeBoundaryFact(*callee, fact);
    return callee;
  }

  // Native-target placeholder names are keyed by the direct native target PC,
  // so a child continuation slice may legitimately reference the same symbol
  // name as the parent module. Preserve any parent-owned boundary identity
  // that is already present on the existing declaration and only backfill
  // fields that are still missing.
  BoundaryFact fact = readBoundaryFact(*callee).value_or(BoundaryFact{});
  if (!fact.boundary_pc)
    fact.boundary_pc = boundary_pc;
  if (!fact.native_target_pc)
    fact.native_target_pc = target_pc;
  if (fact.kind == BoundaryKind::kUnknown)
    fact.kind = BoundaryKind::kNativeBoundary;
  writeBoundaryFact(*callee, fact);
  return callee;
}

bool materializeNativeBoundaryReenterStub(llvm::Function &function,
                                          const FrontierWorkItem &item,
                                          const FrontierCallbacks &callbacks,
                                          const NativeBoundaryDecodeSummary &summary,
                                          const DevirtualizationSession *session) {
  if (!item.target_pc || !summary.direct_call_target_pc ||
      !summary.continuation_pc || !summary.has_direct_call_fallthrough) {
    return false;
  }
  if (function.arg_size() < 3)
    return false;

  auto findImportedVmEnterRoot = [&](uint64_t target_pc) -> llvm::Function * {
    if (!session)
      return nullptr;
    if (auto imported_it = session->imported_vm_enter_child_roots.find(target_pc);
        imported_it != session->imported_vm_enter_child_roots.end()) {
      if (auto *imported = function.getParent()->getFunction(imported_it->second);
          imported && !imported->isDeclaration()) {
        return imported;
      }
    }
    return nullptr;
  };
  auto preferImportedVmEnterRoot =
      [&](llvm::Function *candidate,
          std::optional<uint64_t> candidate_pc = std::nullopt)
      -> llvm::Function * {
    if (!candidate)
      return nullptr;
    if (candidate_pc) {
      if (auto *imported = findImportedVmEnterRoot(*candidate_pc))
        return imported;
    }
    const uint64_t structural_pc = extractStructuralCodeTargetPC(*candidate);
    if (structural_pc != 0) {
      if (auto *imported = findImportedVmEnterRoot(structural_pc))
        return imported;
    }
    if (auto fact = readBoundaryFact(*candidate)) {
      if (fact->boundary_pc) {
        if (auto *imported = findImportedVmEnterRoot(*fact->boundary_pc))
          return imported;
      }
    }
    return candidate;
  };

  auto *continuation = findLiftedOrCoveredFunctionByPC(
      *function.getParent(), *summary.continuation_pc);
  if (!continuation) {
    continuation = preferImportedVmEnterRoot(
        findStructuralCodeTargetFunctionByPC(*function.getParent(),
                                             *summary.continuation_pc),
        *summary.continuation_pc);
  }
  if (!continuation) {
    if (auto nearby_pc = findNearestCoveredLiftedOrBlockPC(
            *function.getParent(), *summary.continuation_pc, 0x80)) {
      continuation =
          findLiftedOrCoveredFunctionByPC(*function.getParent(), *nearby_pc);
      if (!continuation) {
        continuation = preferImportedVmEnterRoot(
            findStructuralCodeTargetFunctionByPC(*function.getParent(),
                                                 *nearby_pc),
            *nearby_pc);
      }
    }
  }
  if (!continuation) {
    continuation = preferImportedVmEnterRoot(
        findNearestStructuralCodeTargetFunctionByPC(
            *function.getParent(), *summary.continuation_pc, 0x80));
  }
  if (!continuation)
    return false;
  const bool modeled_vm_enter_placeholder =
      continuation->isDeclaration() &&
      [&]() {
        if (auto fact = readBoundaryFact(*continuation)) {
          return fact->is_vm_enter || fact->is_nested_vm_enter ||
                 fact->kind == BoundaryKind::kVmEnterBoundary ||
                 fact->kind == BoundaryKind::kNestedVmEnterBoundary;
        }
        return false;
      }();
  if (continuation == &function ||
      (continuation->isDeclaration() && !modeled_vm_enter_placeholder))
    return false;
  if (continuation->arg_size() < 3)
    return false;
  if (continuation->getReturnType() != function.getReturnType())
    return false;

  auto *native_callee = getOrCreateDirectNativeTargetDecl(
      *function.getParent(), function.getFunctionType(), *item.target_pc,
      *summary.direct_call_target_pc);
  if (!native_callee)
    return false;

  if (!function.isDeclaration())
    function.deleteBody();

  auto *entry = llvm::BasicBlock::Create(function.getContext(), "entry", &function);
  llvm::IRBuilder<> ir(entry);
  auto arg_it = function.arg_begin();
  llvm::Value *state_arg = &*arg_it++;
  llvm::Value *pc_arg = &*arg_it++;
  (void)pc_arg;
  llvm::Value *memory_arg = &*arg_it++;

  llvm::SmallVector<llvm::Value *, 3> native_args;
  native_args.push_back(state_arg);
  native_args.push_back(
      llvm::ConstantInt::get(arg_it == function.arg_end()
                                 ? llvm::Type::getInt64Ty(function.getContext())
                                 : function.getFunctionType()->getParamType(1),
                             *summary.direct_call_target_pc));
  native_args.push_back(memory_arg);
  auto *native_call = ir.CreateCall(native_callee, native_args);

  llvm::SmallVector<llvm::Value *, 3> continuation_args;
  continuation_args.push_back(state_arg);
  continuation_args.push_back(llvm::ConstantInt::get(
      continuation->getFunctionType()->getParamType(1), *summary.continuation_pc));
  continuation_args.push_back(native_call);
  auto *continuation_call = ir.CreateCall(continuation, continuation_args);
  ir.CreateRet(continuation_call);
  return true;
}

llvm::FunctionType *inferFrontierFunctionType(llvm::Module &M,
                                              const FrontierWorkItem &item) {
  auto *owner = M.getFunction(item.owner_function);
  const auto boundary_native_target_pc =
      item.boundary ? item.boundary->native_target_pc : std::nullopt;
  if (owner && item.target_pc) {
    for (auto &BB : *owner) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        if (auto *callee = call->getCalledFunction()) {
          const uint64_t structural_target = extractStructuralCodeTargetPC(*callee);
          if (structural_target == *item.target_pc ||
              (boundary_native_target_pc &&
               structural_target == *boundary_native_target_pc)) {
            return call->getFunctionType();
          }
        }
        std::optional<uint64_t> call_target;
        if (auto *callee = call->getCalledFunction()) {
          if ((callee->getName() == "__remill_function_call" ||
               callee->getName() == "__remill_jump" ||
               isDispatchIntrinsicName(callee->getName())) &&
              call->arg_size() >= 2) {
            if (auto *pc =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              call_target = pc->getZExtValue();
            }
          }
        } else if (call->arg_size() >= 3) {
          if (auto *callee_fn = llvm::dyn_cast<llvm::Function>(
                  call->getCalledOperand()->stripPointerCasts());
              callee_fn && callee_fn->getName().contains("CALLI")) {
            if (auto *pc =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2))) {
              call_target = pc->getZExtValue();
            }
          }
        }
        if (call_target && *call_target == *item.target_pc)
          return call->getFunctionType();
      }
    }
  }

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (hasLiftedSignature(F))
      return F.getFunctionType();
  }
  return nullptr;
}

llvm::Function *getOrInsertNativeBoundaryDecl(llvm::Module &M,
                                              const FrontierWorkItem &item,
                                              const FrontierCallbacks &callbacks,
                                              const DevirtualizationSession *session) {
  if (!item.target_pc)
    return nullptr;
  const uint64_t decl_target_pc =
      item.boundary && item.boundary->native_target_pc
          ? *item.boundary->native_target_pc
          : *item.target_pc;
  auto native_summary = decodeNativeBoundarySummary(*item.target_pc, callbacks);
  if (item.boundary && item.boundary->continuation_pc)
    native_summary.continuation_pc = item.boundary->continuation_pc;
  if (auto *existing = M.getFunction(liftedFunctionName(decl_target_pc))) {
    if (!materializeNativeBoundaryReenterStub(*existing, item, callbacks,
                                              native_summary, session) &&
        !existing->isDeclaration()) {
      existing->deleteBody();
    }
    return existing;
  }
  if (auto *existing = findStructuralCodeTargetFunctionByPC(M, decl_target_pc)) {
    if (!materializeNativeBoundaryReenterStub(*existing, item, callbacks,
                                              native_summary, session) &&
        !existing->isDeclaration()) {
      existing->deleteBody();
    }
    return existing;
  }
  if (auto *existing = findLiftedOrBlockFunctionByPC(M, decl_target_pc)) {
    if (!materializeNativeBoundaryReenterStub(*existing, item, callbacks,
                                              native_summary, session) &&
        !existing->isDeclaration()) {
      existing->deleteBody();
    }
    return existing;
  }
  auto *fn_ty = inferFrontierFunctionType(M, item);
  if (!fn_ty)
    return nullptr;
  auto *decl = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                      liftedFunctionName(decl_target_pc), M);
  (void)materializeNativeBoundaryReenterStub(*decl, item, callbacks,
                                             native_summary, session);
  BoundaryFact fact = item.boundary.value_or(BoundaryFact{});
  fact.boundary_pc = item.target_pc;
  if (item.boundary && item.boundary->native_target_pc)
    fact.native_target_pc = item.boundary->native_target_pc;
  if (native_summary.direct_call_target_pc &&
      !(item.boundary && item.boundary->native_target_pc))
    fact.native_target_pc = *native_summary.direct_call_target_pc;
  if (native_summary.continuation_pc)
    fact.continuation_pc = *native_summary.continuation_pc;
  if (auto vip_pc = boundaryContinuationVipPc(item.boundary))
    fact.continuation_vip_pc = vip_pc;
  fact.is_partial_exit = native_summary.has_direct_call_fallthrough;
  fact.reenters_vm =
      boundaryDisposition(item.boundary) ==
      VirtualExitDisposition::kVmExitNativeCallReenter;
  fact.exit_disposition =
      fact.reenters_vm ? BoundaryDisposition::kVmExitNativeCallReenter
                       : BoundaryDisposition::kVmExitNativeExecUnknownReturn;
  fact.kind = BoundaryKind::kNativeBoundary;
  writeBoundaryFact(*decl, fact);
  return decl;
}

llvm::Function *getOrInsertVmEnterBoundaryFunction(
    llvm::Module &M, const FrontierWorkItem &item) {
  if (!item.target_pc)
    return nullptr;
  if (auto *existing =
          findStructuralCodeTargetFunctionByPC(M, *item.target_pc)) {
    return existing;
  }
  if (auto *existing = findLiftedOrBlockFunctionByPC(M, *item.target_pc)) {
    return existing;
  }
  auto *fn_ty = inferFrontierFunctionType(M, item);
  if (!fn_ty)
    return nullptr;
  return llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_" + llvm::utohexstr(*item.target_pc), M);
}

llvm::Function *getOrInsertExecutableTargetFunction(
    llvm::Module &M, const FrontierWorkItem &item) {
  if (!item.target_pc)
    return nullptr;
  if (auto *existing =
          findStructuralCodeTargetFunctionByPC(M, *item.target_pc)) {
    return existing;
  }
  auto *fn_ty = inferFrontierFunctionType(M, item);
  if (!fn_ty)
    return nullptr;
  auto *function = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage,
      "omill_executable_target_" + llvm::utohexstr(*item.target_pc), M);
  if (item.executable_target) {
    writeExecutableTargetFact(*function, *item.executable_target);
  } else {
    ExecutableTargetFact fact;
    fact.raw_target_pc = *item.target_pc;
    writeExecutableTargetFact(*function, fact);
  }
  if (item.site_pc) {
    function->addFnAttr("omill.virtual_exit_site_pc",
                        llvm::utohexstr(*item.site_pc));
  }
  if (item.vip_pc) {
    function->addFnAttr("omill.virtual_exit_vip",
                        llvm::utohexstr(*item.vip_pc));
  }
  if (item.boundary)
    writeBoundaryFact(*function, *item.boundary);
  return function;
}

void annotateNativeBoundaryFunction(llvm::Function &function,
                                    const FrontierWorkItem &item,
                                    const FrontierCallbacks &callbacks) {
  if (!item.target_pc)
    return;
  auto native_summary = decodeNativeBoundarySummary(*item.target_pc, callbacks);
  if (item.boundary && item.boundary->continuation_pc)
    native_summary.continuation_pc = item.boundary->continuation_pc;
  BoundaryFact fact = item.boundary.value_or(BoundaryFact{});
  fact.boundary_pc = item.target_pc;
  if (item.boundary && item.boundary->native_target_pc)
    fact.native_target_pc = item.boundary->native_target_pc;
  if (native_summary.direct_call_target_pc &&
      !(item.boundary && item.boundary->native_target_pc))
    fact.native_target_pc = *native_summary.direct_call_target_pc;
  if (native_summary.continuation_pc)
    fact.continuation_pc = *native_summary.continuation_pc;
  if (auto vip_pc = boundaryContinuationVipPc(item.boundary))
    fact.continuation_vip_pc = vip_pc;
  fact.is_partial_exit = native_summary.has_direct_call_fallthrough;
  fact.reenters_vm =
      boundaryDisposition(item.boundary) ==
      VirtualExitDisposition::kVmExitNativeCallReenter;
  fact.exit_disposition =
      fact.reenters_vm ? BoundaryDisposition::kVmExitNativeCallReenter
                       : BoundaryDisposition::kVmExitNativeExecUnknownReturn;
  fact.kind = BoundaryKind::kNativeBoundary;
  writeBoundaryFact(function, fact);
}

void annotateVmEnterBoundaryFunction(llvm::Function &function,
                                     const FrontierWorkItem &item) {
  if (!item.target_pc)
    return;
  BoundaryFact fact = item.boundary.value_or(BoundaryFact{});
  fact.boundary_pc = item.target_pc;
  fact.is_nested_vm_enter =
      boundaryDisposition(item.boundary) == VirtualExitDisposition::kNestedVmEnter;
  fact.is_vm_enter = !fact.is_nested_vm_enter;
  fact.exit_disposition =
      fact.is_nested_vm_enter ? BoundaryDisposition::kNestedVmEnter
                              : BoundaryDisposition::kVmEnter;
  fact.kind = fact.is_nested_vm_enter ? BoundaryKind::kNestedVmEnterBoundary
                                      : BoundaryKind::kVmEnterBoundary;
  if (auto vip_pc = boundaryContinuationVipPc(item.boundary))
    fact.continuation_vip_pc = vip_pc;
  writeBoundaryFact(function, fact);
}

FrontierWorkKind classifyFrontierWorkItem(const FrontierWorkItem &item,
                                          const FrontierCallbacks &callbacks) {
  if (!item.target_pc)
    return FrontierWorkKind::kUnknownExecutableTarget;
  if (item.from_boundary_continuation &&
      (item.kind == FrontierWorkKind::kIntraOwnerContinuation ||
       (item.boundary &&
        (item.boundary->covered_entry_pc.has_value() ||
         item.boundary->continuation_entry_transform.has_value())))) {
    return FrontierWorkKind::kIntraOwnerContinuation;
  }
  if (item.from_boundary_continuation)
    return FrontierWorkKind::kBoundaryContinuation;
  const uint64_t target_pc = *item.target_pc;
  const auto *fact = item.executable_target ? &*item.executable_target : nullptr;
  const VirtualExitDisposition exit_disposition =
      boundaryDisposition(item.boundary);
  const uint64_t effective_target_pc =
      fact && fact->effective_target_pc ? *fact->effective_target_pc : target_pc;
  if (exit_disposition == VirtualExitDisposition::kVmEnter ||
      exit_disposition == VirtualExitDisposition::kNestedVmEnter) {
    return FrontierWorkKind::kVmEnterBoundary;
  }
  if (exit_disposition == VirtualExitDisposition::kVmExitTerminal &&
      !(fact && fact->invalidated_executable_entry)) {
    return FrontierWorkKind::kTerminalBoundary;
  }
  if (exit_disposition == VirtualExitDisposition::kVmExitNativeCallReenter ||
      exit_disposition ==
          VirtualExitDisposition::kVmExitNativeExecUnknownReturn) {
    return FrontierWorkKind::kNativeCallBoundary;
  }
  if (callbacks.is_protected_boundary &&
      callbacks.is_protected_boundary(target_pc)) {
    return FrontierWorkKind::kVmEnterBoundary;
  }
  if (callbacks.has_defined_target && callbacks.has_defined_target(target_pc))
    return FrontierWorkKind::kLiftableBlock;
  if (effective_target_pc != target_pc && callbacks.has_defined_target &&
      callbacks.has_defined_target(effective_target_pc)) {
    return FrontierWorkKind::kLiftableBlock;
  }
  if (looksLikeVmEnterBoundary(target_pc, callbacks))
    return FrontierWorkKind::kVmEnterBoundary;
  if (!callbacks.is_executable_target ||
      !callbacks.is_executable_target(target_pc)) {
    return FrontierWorkKind::kTerminalBoundary;
  }
  if (((fact && fact->exact_fallthrough_target) ||
       (!(fact && fact->invalidated_executable_entry) &&
        callbacks.can_decode_target &&
        callbacks.can_decode_target(target_pc) &&
        isExactX86DirectCallFallthrough(target_pc, callbacks))) &&
      callbacks.can_decode_target &&
      callbacks.can_decode_target(effective_target_pc)) {
    return FrontierWorkKind::kLiftableBlock;
  }
  if (looksLikeTerminalBoundarySnippet(target_pc, callbacks))
    return FrontierWorkKind::kTerminalBoundary;
  if (looksLikeJunkExecutableSnippet(target_pc, callbacks))
    return FrontierWorkKind::kTerminalBoundary;
  if (looksLikeNativeCallBoundary(target_pc, callbacks))
    return FrontierWorkKind::kNativeCallBoundary;
  if (looksLikeNativeFunctionEntry(target_pc, callbacks))
    return FrontierWorkKind::kNativeCallBoundary;
  if (looksLikeNonEntryExecutableSnippet(target_pc, callbacks))
    return FrontierWorkKind::kUnknownExecutableTarget;
  if (fact && fact->invalidated_executable_entry)
    return FrontierWorkKind::kUnknownExecutableTarget;
  if (callbacks.can_decode_target &&
      callbacks.can_decode_target(effective_target_pc))
    return FrontierWorkKind::kLiftableBlock;
  return FrontierWorkKind::kUnknownExecutableTarget;
}

void mergeFrontierItems(
    DevirtualizationSession &session, llvm::ArrayRef<FrontierWorkItem> items,
    FrontierAdvanceSummary *summary = nullptr) {
  auto &edge_facts = session.graph.edge_facts_by_identity;
  for (const auto &item : items) {
    auto existing = edge_facts.find(item.identity);
    if (existing == edge_facts.end()) {
      SessionEdgeFact edge;
      edge.identity = item.identity;
      syncEdgeFactFromFrontierWorkItem(edge, item);
      edge.is_dirty = true;
      edge.from_output_root_closure = item.identity.find("closure:") == 0;
      edge.from_vm_continuation = item.owner_function == "__frontier__";
      edge.from_boundary_continuation = item.from_boundary_continuation;
      edge.from_unresolved_exit =
          !edge.from_output_root_closure && !edge.from_boundary_continuation;
      edge_facts.emplace(item.identity, std::move(edge));
      if (summary)
        ++summary->discovered;
      continue;
    }
    auto &edge = existing->second;
    const bool changed = edge.target_pc != item.target_pc ||
                         edge.executable_target != item.executable_target ||
                         edge.boundary != item.boundary ||
                         edge.vip_pc != item.vip_pc ||
                         edge.vip_symbolic != item.vip_symbolic;
    const auto preserved_kind = edge.kind;
    const auto preserved_status = edge.status;
    const auto preserved_retry_count = edge.retry_count;
    const auto preserved_failure_reason = edge.failure_reason;
    if (edge.status == FrontierWorkStatus::kInvalidated || changed) {
      edge.status = FrontierWorkStatus::kPending;
      edge.failure_reason.clear();
      edge.is_dirty = true;
    }
    syncEdgeFactFromFrontierWorkItem(edge, item);
    if (edge.status != FrontierWorkStatus::kInvalidated && !changed) {
      edge.kind = preserved_kind;
      edge.status = preserved_status;
      edge.retry_count = preserved_retry_count;
      edge.failure_reason = preserved_failure_reason;
    }
    edge.from_output_root_closure =
        edge.from_output_root_closure || item.identity.find("closure:") == 0;
    edge.from_vm_continuation =
        edge.from_vm_continuation || item.owner_function == "__frontier__";
    edge.from_boundary_continuation =
        edge.from_boundary_continuation || item.from_boundary_continuation;
    edge.from_unresolved_exit =
        edge.from_unresolved_exit ||
        (!item.from_boundary_continuation && item.identity.find("closure:") != 0);
  }
}

void refreshFrontierCompatibilityViews(DevirtualizationSession &session) {
  const bool debug_frontier =
      (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
  session.discovered_frontier_work_items.clear();
  session.late_frontier_work_items.clear();
  session.discovered_frontier_identities.clear();
  session.late_frontier_identities.clear();
  session.discovered_frontier_pcs.clear();
  session.late_frontier.clear();
  session.frontier_work_by_identity.clear();

  for (const auto &[identity, edge] : session.graph.edge_facts_by_identity) {
    (void)identity;
    auto item = frontierWorkItemFromEdgeFact(edge);
    session.frontier_work_by_identity.emplace(item.identity, item);
    session.discovered_frontier_work_items.push_back(item);
    session.discovered_frontier_identities.push_back(item.identity);
    if (item.target_pc)
      session.discovered_frontier_pcs.push_back(*item.target_pc);
    if (item.status == FrontierWorkStatus::kPending ||
        item.status == FrontierWorkStatus::kInvalidated) {
      session.late_frontier_work_items.push_back(item);
      session.late_frontier_identities.push_back(item.identity);
      if (item.target_pc)
        session.late_frontier.push_back(*item.target_pc);
    }
  }

  auto scheduling_rank = [](FrontierSchedulingClass scheduling_class) {
    switch (scheduling_class) {
      case FrontierSchedulingClass::kTrustedLive:
        return 0;
      case FrontierSchedulingClass::kWeakExecutable:
        return 1;
      case FrontierSchedulingClass::kNativeOrVmEnterBoundary:
        return 2;
      case FrontierSchedulingClass::kTerminalModeled:
        return 3;
      case FrontierSchedulingClass::kQuarantinedSelectorArm:
        return 4;
    }
    return 99;
  };
  std::stable_sort(
      session.late_frontier_work_items.begin(),
      session.late_frontier_work_items.end(),
      [&](const FrontierWorkItem &lhs, const FrontierWorkItem &rhs) {
        return scheduling_rank(lhs.scheduling_class) <
               scheduling_rank(rhs.scheduling_class);
      });
  session.late_frontier_identities.clear();
  session.late_frontier.clear();
  for (const auto &item : session.late_frontier_work_items) {
    session.late_frontier_identities.push_back(item.identity);
    if (item.target_pc)
      session.late_frontier.push_back(*item.target_pc);
  }

  if (debug_frontier) {
    for (const auto &[identity, item] : session.frontier_work_by_identity) {
      llvm::errs() << "[frontier-refresh] id=" << identity;
      if (item.target_pc)
        llvm::errs() << " target=0x" << llvm::utohexstr(*item.target_pc);
      llvm::errs() << " kind=" << toString(item.kind)
                   << " status=" << toString(item.status)
                   << " sched=" << static_cast<int>(item.scheduling_class);
      if (!item.failure_reason.empty())
        llvm::errs() << " reason=" << item.failure_reason;
      llvm::errs() << "\n";
    }
  }
}

bool isContinuationCandidate(const UnresolvedExitSite &site) {
  if (!site.target_pc || site.completeness != ExitCompleteness::kComplete)
    return false;
  return site.kind == UnresolvedExitKind::kDispatchCall ||
         site.kind == UnresolvedExitKind::kDispatchJump ||
         site.kind == UnresolvedExitKind::kUnknownContinuation;
}

std::vector<std::string> collectContinuationIdentities(
    llvm::ArrayRef<UnresolvedExitSite> unresolved_exits) {
  std::set<std::string> identities;
  for (const auto &site : unresolved_exits) {
    if (!isContinuationCandidate(site))
      continue;
    identities.insert(unresolvedExitIdentity(site));
  }
  return {identities.begin(), identities.end()};
}

std::map<std::string, UnresolvedExitSite> buildUnresolvedExitIndex(
    const std::vector<UnresolvedExitSite> &sites) {
  std::map<std::string, UnresolvedExitSite> index;
  for (const auto &site : sites)
    index.emplace(unresolvedExitStableSiteKey(site), site);
  return index;
}

std::vector<UnresolvedExitSite> collectUnresolvedExitSites(
    const llvm::Module &M, const std::vector<UnresolvedExitSite> &previous) {
  std::vector<UnresolvedExitSite> sites;
  const auto previous_index = buildUnresolvedExitIndex(previous);
  std::map<std::string, unsigned> next_site_index;

  auto applyPreviousState = [&](UnresolvedExitSite &site) {
    const auto key = unresolvedExitStableSiteKey(site);
    auto it = previous_index.find(key);
    if (it == previous_index.end())
      return;
    const auto &prior = it->second;
    if (prior.evidence.predecessor_count != site.evidence.predecessor_count) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "predecessor_count_changed";
    } else if (prior.target_pc != site.target_pc) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "target_changed";
    } else if (prior.vip_pc != site.vip_pc) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "vip_changed";
    } else if (prior.continuation_vip_pc != site.continuation_vip_pc) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "continuation_vip_changed";
    } else if (prior.continuation_slot_id != site.continuation_slot_id) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "continuation_slot_changed";
    } else if (prior.continuation_stack_cell_id !=
               site.continuation_stack_cell_id) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "continuation_stack_cell_changed";
    } else if (prior.vip_symbolic != site.vip_symbolic) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "vip_symbolic_changed";
    } else if (prior.exit_disposition != site.exit_disposition) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "exit_disposition_changed";
    } else if (prior.completeness == ExitCompleteness::kComplete &&
               site.completeness == ExitCompleteness::kIncomplete) {
      site.completeness = ExitCompleteness::kInvalidated;
      site.evidence.invalidation_reason = "resolved_target_missing";
    }
  };

  auto carryForwardDerivedBoundaryState = [&](UnresolvedExitSite &site,
                                              bool has_explicit_boundary_fact) {
    if (has_explicit_boundary_fact)
      return;
    const auto key = unresolvedExitStableSiteKey(site);
    auto it = previous_index.find(key);
    if (it == previous_index.end())
      return;
    const auto &prior = it->second;
    if (prior.target_pc != site.target_pc)
      return;
    if ((site.exit_disposition == VirtualExitDisposition::kUnknown ||
         site.exit_disposition == VirtualExitDisposition::kStayInVm) &&
        prior.exit_disposition != VirtualExitDisposition::kUnknown) {
      site.exit_disposition = prior.exit_disposition;
    }
    if (!site.continuation_vip_pc)
      site.continuation_vip_pc = prior.continuation_vip_pc;
    if (!site.continuation_slot_id)
      site.continuation_slot_id = prior.continuation_slot_id;
    if (!site.continuation_stack_cell_id)
      site.continuation_stack_cell_id = prior.continuation_stack_cell_id;
  };

  for (const auto &F : M) {
    const auto owner_site_pc = extractLiftUnitVA(F);
    for (const auto &BB : F) {
      for (const auto &I : BB) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        const auto *Callee = CB ? CB->getCalledFunction() : nullptr;
        if (!Callee || !isDispatchIntrinsicName(Callee->getName()))
          continue;

        UnresolvedExitSite site;
        site.kind = isDispatchJumpName(Callee->getName())
                        ? UnresolvedExitKind::kDispatchJump
                        : UnresolvedExitKind::kDispatchCall;
        site.owner_function = F.getName().str();
        site.site_index = next_site_index[site.owner_function]++;
        site.site_pc = owner_site_pc;
        site.evidence.predecessor_count = llvm::pred_size(&BB);
        site.evidence.last_epoch_touched =
            DevirtualizationEpoch::kDetectionSeedExtraction;
        if (CB->arg_size() >= 2) {
          if (const auto *PC =
                  llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(1))) {
            if (PC->getZExtValue() != 0) {
              site.target_pc = PC->getZExtValue();
              site.vip_pc = site.target_pc;
              site.evidence.resolved_targets.push_back(*site.target_pc);
            }
          } else {
            site.vip_symbolic = true;
          }
        }
        const auto boundary_fact = readBoundaryFact(*CB);
        if (boundary_fact) {
          site.exit_disposition =
              virtualExitDispositionFromBoundaryDisposition(
                  boundary_fact->exit_disposition);
          site.continuation_vip_pc = boundary_fact->continuation_vip_pc;
          site.continuation_slot_id = boundary_fact->continuation_slot_id;
          site.continuation_stack_cell_id =
              boundary_fact->continuation_stack_cell_id;
        } else {
          site.exit_disposition =
              site.kind == UnresolvedExitKind::kDispatchCall
                  ? VirtualExitDisposition::kVmExitNativeCallReenter
                  : VirtualExitDisposition::kStayInVm;
        }
        carryForwardDerivedBoundaryState(site, boundary_fact.has_value());
        site.completeness =
            site.target_pc && hasKnownMaterializedTarget(M, *site.target_pc)
                ? ExitCompleteness::kComplete
                : ExitCompleteness::kIncomplete;
        applyPreviousState(site);
        sites.push_back(std::move(site));
      }
    }

    if (!functionLooksLikeVmBoundary(F))
      continue;
    UnresolvedExitSite site;
    site.kind = UnresolvedExitKind::kProtectedBoundary;
    site.owner_function = F.getName().str();
    site.site_index = next_site_index[site.owner_function]++;
    site.site_pc = owner_site_pc;
    site.evidence.predecessor_count = llvm::pred_size(&F.getEntryBlock());
    site.evidence.last_epoch_touched =
        DevirtualizationEpoch::kDetectionSeedExtraction;
    site.exit_disposition = VirtualExitDisposition::kVmExitTerminal;
    site.completeness = ExitCompleteness::kIncomplete;
    applyPreviousState(site);
    sites.push_back(std::move(site));
  }

  return sites;
}

void addUnknownContinuationSites(const llvm::Module &M,
                                 std::vector<UnresolvedExitSite> &sites,
                                 llvm::ArrayRef<uint64_t> frontier_pcs) {
  std::set<uint64_t> known_targets;
  for (const auto &site : sites) {
    if (site.target_pc)
      known_targets.insert(*site.target_pc);
  }
  for (uint64_t frontier_pc : frontier_pcs) {
    if (known_targets.count(frontier_pc))
      continue;
    UnresolvedExitSite site;
    site.kind = UnresolvedExitKind::kUnknownContinuation;
    site.owner_function = "__frontier__";
    site.site_pc = frontier_pc;
    site.target_pc = frontier_pc;
    site.vip_pc = frontier_pc;
    site.evidence.resolved_targets.push_back(frontier_pc);
    site.evidence.last_epoch_touched =
        DevirtualizationEpoch::kFrontierScheduling;
    site.exit_disposition = VirtualExitDisposition::kStayInVm;
    site.completeness = hasKnownMaterializedTarget(M, frontier_pc)
                            ? ExitCompleteness::kComplete
                            : ExitCompleteness::kIncomplete;
    sites.push_back(std::move(site));
  }
}

std::map<NormalizedLiftUnitCacheKey, NormalizedLiftUnitCacheEntry>
collectNormalizedLiftUnitCache(
    const llvm::Module &M,
    const std::map<NormalizedLiftUnitCacheKey, NormalizedLiftUnitCacheEntry>
        &previous_cache,
    llvm::ArrayRef<UnresolvedExitSite> unresolved_exits,
    std::vector<std::string> &newly_lifted_functions,
    std::vector<std::string> &dirty_functions) {
  std::map<NormalizedLiftUnitCacheKey, NormalizedLiftUnitCacheEntry> cache;
  std::set<std::string> dirty_set;

  for (const auto &F : M) {
    if (!isTrackedLiftUnit(F))
      continue;
    auto va = extractLiftUnitVA(F);
    if (!va)
      continue;

    NormalizedLiftUnitCacheEntry entry;
    entry.key.va = *va;
    entry.key.block_lift = isBlockLiftName(F.getName());
    entry.function_name = F.getName().str();

    const auto snapshot = summarizeFunctionNormalization(F);
    entry.normalization_gate_passed = passesNormalizationGate(snapshot);
    entry.live_memory_intrinsics = snapshot.live_memory_intrinsics;
    entry.live_runtime_intrinsics = snapshot.live_runtime_intrinsics;
    entry.legacy_dispatch_intrinsics = snapshot.legacy_dispatch_intrinsics;
    entry.dirty_dependencies = snapshot.dirty_dependencies;
    entry.unresolved_exit_count = static_cast<unsigned>(std::count_if(
        unresolved_exits.begin(), unresolved_exits.end(),
        [&](const UnresolvedExitSite &site) {
          return site.owner_function == entry.function_name;
        }));
    auto [vip_status, vip_pc] =
        classifyVipTrackingForFunction(entry.function_name, unresolved_exits);
    entry.vip_status = vip_status;
    entry.vip_pc = vip_pc;
    entry.vip_context_fingerprint =
        buildVipContextFingerprint(entry.function_name, unresolved_exits);

    auto previous_it = previous_cache.find(entry.key);
    if (previous_it == previous_cache.end()) {
      entry.status = LiftUnitCacheStatus::kFresh;
      newly_lifted_functions.push_back(entry.function_name);
    } else {
      const auto &previous = previous_it->second;
      const bool unchanged =
          previous.function_name == entry.function_name &&
          previous.vip_status == entry.vip_status &&
          previous.vip_pc == entry.vip_pc &&
          previous.vip_context_fingerprint == entry.vip_context_fingerprint &&
          previous.normalization_gate_passed == entry.normalization_gate_passed &&
          previous.unresolved_exit_count == entry.unresolved_exit_count &&
          previous.live_memory_intrinsics == entry.live_memory_intrinsics &&
          previous.live_runtime_intrinsics == entry.live_runtime_intrinsics &&
          previous.legacy_dispatch_intrinsics ==
              entry.legacy_dispatch_intrinsics &&
          previous.dirty_dependencies == entry.dirty_dependencies;
      entry.status = unchanged ? LiftUnitCacheStatus::kReused
                               : LiftUnitCacheStatus::kInvalidated;
      if (!unchanged)
        dirty_set.insert(entry.function_name);
    }

    if (!entry.normalization_gate_passed)
      dirty_set.insert(entry.function_name);

    cache.emplace(entry.key, std::move(entry));
  }

  dirty_functions.assign(dirty_set.begin(), dirty_set.end());
  return cache;
}

DevirtualizationRoundTelemetry summarizeRoundTelemetry(
    llvm::ArrayRef<UnresolvedExitSite> unresolved_exits,
    const std::map<NormalizedLiftUnitCacheKey, NormalizedLiftUnitCacheEntry>
        &cache,
    const RemillNormalizationSummary &normalization_summary) {
  DevirtualizationRoundTelemetry telemetry;
  for (const auto &[key, entry] : cache) {
    (void)key;
    if (entry.status == LiftUnitCacheStatus::kFresh)
      ++telemetry.units_lifted;
    if (entry.status == LiftUnitCacheStatus::kReused)
      ++telemetry.units_reused;
    if (!entry.normalization_gate_passed)
      ++telemetry.normalization_failures;
  }
  for (const auto &site : unresolved_exits) {
    switch (site.completeness) {
      case ExitCompleteness::kComplete:
        ++telemetry.unresolved_exits_complete;
        if (site.kind == UnresolvedExitKind::kDispatchCall ||
            site.kind == UnresolvedExitKind::kDispatchJump) {
          ++telemetry.dispatches_materialized;
        }
        break;
      case ExitCompleteness::kIncomplete:
        ++telemetry.unresolved_exits_incomplete;
        break;
      case ExitCompleteness::kInvalidated:
        ++telemetry.unresolved_exits_invalidated;
        break;
    }
  }
  telemetry.leaked_runtime_artifacts =
      normalization_summary.live_memory_intrinsics +
      normalization_summary.live_runtime_intrinsics +
      normalization_summary.legacy_omill_dispatch_intrinsics;
  return telemetry;
}

void refreshSessionCoreState(DevirtualizationSession &session,
                             const llvm::Module &M) {
  std::vector<uint64_t> frontier_pcs;
  auto previous_unresolved_exits = session.unresolved_exits;
  (void)countUnresolvedDispatches(M, &frontier_pcs);
  session.unresolved_exits =
      collectUnresolvedExitSites(M, previous_unresolved_exits);
  addUnknownContinuationSites(M, session.unresolved_exits, frontier_pcs);
  std::set<std::string> known_site_keys;
  for (const auto &site : session.unresolved_exits)
    known_site_keys.insert(unresolvedExitStableSiteKey(site));
  for (const auto &site : previous_unresolved_exits) {
    if (site.kind != UnresolvedExitKind::kUnknownContinuation &&
        site.kind != UnresolvedExitKind::kProtectedBoundary) {
      continue;
    }
    if (known_site_keys.insert(unresolvedExitStableSiteKey(site)).second)
      session.unresolved_exits.push_back(site);
  }

  auto previous_cache = session.normalized_unit_cache;
  session.newly_lifted_functions.clear();
  session.dirty_functions.clear();
  session.normalized_unit_cache = collectNormalizedLiftUnitCache(
      M, previous_cache, session.unresolved_exits,
      session.newly_lifted_functions, session.dirty_functions);

  std::set<uint64_t> continuation_targets;
  for (const auto &site : session.unresolved_exits) {
    if (!isContinuationCandidate(site))
      continue;
    continuation_targets.insert(*site.target_pc);
  }
  session.discovered_continuations.assign(continuation_targets.begin(),
                                          continuation_targets.end());
  session.discovered_continuation_identities =
      collectContinuationIdentities(session.unresolved_exits);

  RemillNormalizationOrchestrator normalization;
  session.latest_round = summarizeRoundTelemetry(
      session.unresolved_exits, session.normalized_unit_cache,
      normalization.summarize(M));
  refreshSessionGraphState(session, M);
}

void linkFrontierItemToUnresolvedExit(DevirtualizationSession &session,
                                      const FrontierWorkItem &item) {
  auto matches = [&](const UnresolvedExitSite &site) {
    if (site.owner_function != item.owner_function)
      return false;
    if (site.site_index != item.site_index)
      return false;
    return site.target_pc == item.target_pc;
  };

  for (auto &site : session.unresolved_exits) {
    if (!matches(site))
      continue;
    site.exit_disposition = boundaryDisposition(item.boundary);
    site.continuation_vip_pc = boundaryContinuationVipPc(item.boundary);
    site.continuation_slot_id = boundaryContinuationSlotId(item.boundary);
    site.continuation_stack_cell_id =
        boundaryContinuationStackCellId(item.boundary);
    site.vip_pc = item.vip_pc;
    site.vip_symbolic = item.vip_symbolic;
    site.completeness = item.status == FrontierWorkStatus::kLifted ||
                                item.status == FrontierWorkStatus::kSkippedMaterialized
                            ? ExitCompleteness::kComplete
                            : ExitCompleteness::kIncomplete;
    site.evidence.invalidation_reason = item.failure_reason;
    return;
  }

  if (!item.target_pc)
    return;
  UnresolvedExitSite site;
  site.kind = UnresolvedExitKind::kUnknownContinuation;
  site.owner_function = item.owner_function;
  site.site_index = item.site_index;
  site.site_pc = item.site_pc;
  site.target_pc = item.target_pc;
  site.vip_pc = item.vip_pc;
  site.continuation_vip_pc = boundaryContinuationVipPc(item.boundary);
  site.continuation_slot_id = boundaryContinuationSlotId(item.boundary);
  site.continuation_stack_cell_id =
      boundaryContinuationStackCellId(item.boundary);
  site.vip_symbolic = item.vip_symbolic;
  site.exit_disposition = boundaryDisposition(item.boundary);
  site.completeness = item.status == FrontierWorkStatus::kLifted ||
                              item.status == FrontierWorkStatus::kSkippedMaterialized
                          ? ExitCompleteness::kComplete
                          : ExitCompleteness::kIncomplete;
  site.evidence.invalidation_reason = item.failure_reason;
  session.unresolved_exits.push_back(std::move(site));
}

unsigned countUnresolvedDispatches(const llvm::Module &M,
                                   std::vector<uint64_t> *frontier_pcs) {
  unsigned unresolved = 0;
  for (const auto &F : M) {
    for (const auto &BB : F) {
      for (const auto &I : BB) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        const auto *Callee = CB ? CB->getCalledFunction() : nullptr;
        if (!Callee || !isDispatchName(Callee->getName()))
          continue;
        ++unresolved;
        if (!frontier_pcs || CB->arg_size() < 2)
          continue;
        const auto *PC = llvm::dyn_cast<llvm::ConstantInt>(CB->getArgOperand(1));
        if (PC && PC->getZExtValue() != 0)
          frontier_pcs->push_back(PC->getZExtValue());
      }
    }
  }
  return unresolved;
}

unsigned countProtectedBoundaries(const llvm::Module &M,
                                  unsigned *vm_entry_boundaries) {
  unsigned boundaries = 0;
  unsigned vm_entries = 0;
  for (const auto &F : M) {
    if (!functionLooksLikeVmBoundary(F))
      continue;
    ++boundaries;
    if (F.getName().starts_with("vm_entry_"))
      ++vm_entries;
  }
  if (vm_entry_boundaries)
    *vm_entry_boundaries = vm_entries;
  return boundaries;
}

bool hasClosedSliceWrapperLadder(const llvm::Module &M) {
  const auto *ClosedFlag = M.getModuleFlag("omill.closed_root_slice_scope");
  if (!ClosedFlag)
    return false;

  for (const auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
      continue;
    for (const auto &BB : F) {
      for (const auto &I : BB) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        const auto *Callee = CB ? CB->getCalledFunction() : nullptr;
        if (!Callee)
          continue;
        if (Callee->getName().ends_with("_native") ||
            Callee->hasFnAttribute("omill.abi_wrapper"))
          return true;
      }
    }
  }
  return false;
}

}  // namespace

void publishSessionGraphProjection(const llvm::Module &M,
                                   const SessionGraphState &state) {
  publishSessionGraphProjectionImpl(M, state);
}

const SessionGraphState *findSessionGraphProjection(const llvm::Module &M) {
  return findSessionGraphProjectionImpl(M);
}

SessionGraphState *findMutableSessionGraphProjection(llvm::Module &M) {
  return findMutableSessionGraphProjectionImpl(M);
}

DevirtualizationOrchestrator::DevirtualizationOrchestrator(
    DevirtualizationPolicy policy,
    std::shared_ptr<IterativeLiftingSession> session)
    : policy_(std::move(policy)) {
  session_.iterative_session = std::move(session);
}

DevirtualizationDetectionResult DevirtualizationOrchestrator::detect(
    const llvm::Module &M, const DevirtualizationRequest &request,
    const DevirtualizationCompatInputs &compat_inputs) const {
  DevirtualizationDetectionResult result;
  result.forced = request.force_devirtualize;
  result.seed_roots = request.root_vas;
  result.unresolved_dispatches =
      countUnresolvedDispatches(M, &result.frontier_pcs);
  result.protected_boundaries =
      countProtectedBoundaries(M, &result.vm_entry_boundaries);

  const bool generic_candidates =
      moduleHasGenericStaticDevirtualizationCandidates(M);
  const bool root_local_candidates =
      moduleHasRootLocalGenericStaticDevirtualizationShape(M);
  const bool compatibility_requested = compatibilityRequested(compat_inputs);

  if (request.force_devirtualize) {
    result.should_devirtualize = true;
    result.confidence = DevirtualizationConfidence::kHigh;
    result.reasons.emplace_back("forced");
  }

  if (compatibility_requested) {
    result.should_devirtualize = true;
    result.confidence = DevirtualizationConfidence::kHigh;
    result.reasons.emplace_back("compatibility_flag");
  }

  if (policy_.auto_detect && request.auto_detect) {
    const bool has_vm_like_signal = result.protected_boundaries > 0 ||
                                    root_local_candidates ||
                                    generic_candidates;
    if (result.unresolved_dispatches > 0 && has_vm_like_signal) {
      result.should_devirtualize = true;
      result.confidence = DevirtualizationConfidence::kHigh;
      result.reasons.emplace_back("unresolved_dispatch_frontier");
    }
    if (result.protected_boundaries > 0) {
      result.should_devirtualize = true;
      if (result.confidence == DevirtualizationConfidence::kLow)
        result.confidence = DevirtualizationConfidence::kMedium;
      result.reasons.emplace_back("protected_boundary");
    }
    if (root_local_candidates) {
      result.should_devirtualize = true;
      result.confidence = DevirtualizationConfidence::kHigh;
      result.reasons.emplace_back("root_local_vm_shape");
    } else if (generic_candidates) {
      result.should_devirtualize = true;
      if (result.confidence == DevirtualizationConfidence::kLow)
        result.confidence = DevirtualizationConfidence::kMedium;
      result.reasons.emplace_back("generic_vm_candidates");
    }
  }

  return result;
}

DevirtualizationExecutionPlan DevirtualizationOrchestrator::buildExecutionPlan(
    const llvm::Module &M, const DevirtualizationRequest &request,
    const DevirtualizationCompatInputs &compat_inputs) {
  DevirtualizationExecutionPlan plan;
  plan.detection = detect(M, request, compat_inputs);
  plan.enable_devirtualization = plan.detection.should_devirtualize;
  plan.verify_rewrites = request.verify_rewrites;

  session_.root_slice = request.root_vas;
  session_.discovered_root_pcs = plan.detection.seed_roots;
  refreshSessionCoreState(session_, M);
  mergeFrontierItems(session_, collectFrontierWorkItems(session_.unresolved_exits));
  refreshSessionGraphState(session_, M);
  refreshFrontierCompatibilityViews(session_);

  if (!plan.enable_devirtualization)
    return plan;

  plan.use_block_lift = policy_.force_block_lift;
  plan.use_generic_static_devirtualization = policy_.force_generic_static;
  plan.disable_legacy_vm_path = policy_.disable_legacy_vm_path;
  return plan;
}

DevirtualizationDriverCompatPlan
DevirtualizationOrchestrator::buildDriverCompatPlan(
    const llvm::Module &M, const DevirtualizationRequest &request,
    const DevirtualizationCompatInputs &compat_inputs) {
  DevirtualizationDriverCompatPlan compat_plan;
  compat_plan.execution = buildExecutionPlan(M, request, compat_inputs);
  compat_plan.use_block_lift =
      requestedCompatBlockLiftMode(request, compat_inputs) ||
      compat_plan.execution.use_block_lift;
  compat_plan.generic_static_requested =
      requestedCompatGenericStatic(request, compat_inputs) ||
      compat_plan.execution.use_generic_static_devirtualization;
  compat_plan.use_generic_static = compat_plan.generic_static_requested;
  compat_plan.verify_generic_static =
      compat_inputs.env_verify_generic_static || request.verify_rewrites ||
      compat_plan.execution.verify_rewrites;
  compat_plan.enable_legacy_vm_mode = false;
  if (compat_inputs.requested_vm_entry_mode) {
    compat_plan.suppress_legacy_vm_mode = true;
    compat_plan.legacy_vm_mode_reason =
        DevirtualizationCompatReason::kLegacyVmPathSuppressed;
  }

  compat_plan.root_local_generic_static_devirtualization_shape =
      moduleHasRootLocalGenericStaticDevirtualizationShape(M);

  const bool known_unstable_large_default_export_root =
      compat_inputs.requested_root_is_export &&
      compat_inputs.largest_executable_section_size >= (1ull << 20) &&
      (compat_inputs.requested_root_rva == 0x2400 ||
       compat_inputs.requested_root_rva == 0x23F0);

  if (compat_plan.use_generic_static &&
      shouldUseFastPlainExportRootFallback(
          compat_plan.enable_legacy_vm_mode,
          compat_inputs.requested_root_is_export, compat_plan.use_block_lift,
          compat_plan.generic_static_requested,
          compat_inputs.env_force_generic_static,
          compat_inputs.largest_executable_section_size,
          compat_inputs.executable_section_count) &&
      !compat_inputs.export_root_has_hidden_entry_seed_exprs) {
    compat_plan.use_generic_static = false;
    compat_plan.verify_generic_static = false;
    compat_plan.export_root_fallback_mode =
        DevirtualizationExportRootFallbackMode::kFastPlain;
    compat_plan.generic_static_reason =
        DevirtualizationCompatReason::kFastPlainExportRootFallback;
  } else if (compat_plan.use_generic_static &&
             shouldUseStableNoGsdExportRootFallback(
                 compat_plan.enable_legacy_vm_mode,
                 compat_inputs.requested_root_is_export,
                 compat_plan.use_block_lift,
                 compat_plan.generic_static_requested,
                 compat_inputs.env_force_generic_static,
                 compat_inputs.largest_executable_section_size) &&
             known_unstable_large_default_export_root) {
    compat_plan.use_generic_static = false;
    compat_plan.verify_generic_static = false;
    compat_plan.export_root_fallback_mode =
        DevirtualizationExportRootFallbackMode::kStableLarge;
    compat_plan.generic_static_reason =
        DevirtualizationCompatReason::kStableLargeExportRootFallback;
  } else if (
      compat_plan.use_generic_static &&
      shouldAutoSkipGenericStaticDevirtualizationForRoot(
          M, compat_plan.enable_legacy_vm_mode,
          compat_inputs.requested_root_is_export,
          compat_inputs.env_force_generic_static,
          compat_plan.root_local_generic_static_devirtualization_shape)) {
    compat_plan.use_generic_static = false;
    compat_plan.verify_generic_static = false;
    compat_plan.generic_static_reason =
        DevirtualizationCompatReason::kNoVmLikeCandidates;
  }

  compat_plan.auto_skip_always_inline =
      shouldAutoSkipAlwaysInlineForRoot(
          compat_plan.enable_legacy_vm_mode,
          compat_inputs.requested_root_is_export,
          compat_plan.generic_static_requested, compat_plan.use_generic_static,
          compat_plan.root_local_generic_static_devirtualization_shape) ||
      compat_plan.export_root_fallback_mode ==
          DevirtualizationExportRootFallbackMode::kStableLarge;
  if (compat_plan.auto_skip_always_inline) {
    compat_plan.always_inline_reason =
        compat_plan.export_root_fallback_mode ==
                DevirtualizationExportRootFallbackMode::kStableLarge
            ? DevirtualizationCompatReason::kStableLargeExportRootFallback
            : DevirtualizationCompatReason::kNoRootLocalDevirtShape;
  }

  compat_plan.use_pre_abi_noabi_cleanup =
      !compat_inputs.no_abi && compat_plan.use_generic_static;
  if (compat_plan.use_pre_abi_noabi_cleanup) {
    compat_plan.pre_abi_cleanup_reason =
        DevirtualizationCompatReason::kPreAbiNoAbiCleanup;
  }
  compat_plan.no_abi_mode =
      compat_inputs.no_abi || compat_plan.use_pre_abi_noabi_cleanup;

  return compat_plan;
}

void DevirtualizationOrchestrator::refreshSessionState(const llvm::Module &M) {
  refreshSessionCoreState(session_, M);
  mergeFrontierItems(session_, collectFrontierWorkItems(session_.unresolved_exits));
  refreshSessionGraphState(session_, M);
  refreshFrontierCompatibilityViews(session_);
}

void DevirtualizationOrchestrator::applyExecutionPlan(
    const DevirtualizationExecutionPlan &plan, PipelineOptions &opts) const {
  if (!plan.enable_devirtualization)
    return;
  opts.use_block_lifting = opts.use_block_lifting || plan.use_block_lift;
  opts.generic_static_devirtualize =
      opts.generic_static_devirtualize ||
      plan.use_generic_static_devirtualization;
  opts.verify_generic_static_devirtualization =
      opts.verify_generic_static_devirtualization || plan.verify_rewrites;
  opts.require_remill_normalization =
      opts.require_remill_normalization || plan.enable_devirtualization;
  if (plan.disable_legacy_vm_path)
    opts.vm_devirtualize = false;
}

void DevirtualizationOrchestrator::applyDriverCompatPlan(
    const DevirtualizationDriverCompatPlan &plan, PipelineOptions &opts) const {
  applyExecutionPlan(plan.execution, opts);
  opts.use_block_lifting = opts.use_block_lifting || plan.use_block_lift;
  opts.generic_static_devirtualize = plan.use_generic_static;
  opts.verify_generic_static_devirtualization = plan.verify_generic_static;
  opts.vm_devirtualize = plan.enable_legacy_vm_mode;
  opts.no_abi_mode = plan.no_abi_mode;
}

FrontierAdvanceSummary DevirtualizationOrchestrator::discoverFrontierWork(
    const llvm::Module &M, const FrontierCallbacks &callbacks,
    FrontierDiscoveryPhase phase) {
  FrontierAdvanceSummary summary;
  if (phase == FrontierDiscoveryPhase::kUnresolvedOnly) {
    const bool has_pending_boundary_continuation =
        llvm::any_of(session_.late_frontier_work_items, [](const FrontierWorkItem &item) {
          return item.from_boundary_continuation &&
                 item.status == FrontierWorkStatus::kPending;
        });
    if (has_pending_boundary_continuation) {
      refreshFrontierCompatibilityViews(session_);
      summary.pending =
          static_cast<unsigned>(session_.late_frontier_work_items.size());
      return summary;
    }
  }
  refreshSessionCoreState(session_, M);

  if (phase == FrontierDiscoveryPhase::kUnresolvedOnly ||
      phase == FrontierDiscoveryPhase::kCombined) {
    mergeFrontierItems(session_, collectFrontierWorkItems(session_.unresolved_exits),
                       &summary);
  }

  if ((phase == FrontierDiscoveryPhase::kVmUnresolvedContinuations ||
       phase == FrontierDiscoveryPhase::kCombined) &&
      callbacks.is_code_address && callbacks.has_defined_target &&
      callbacks.normalize_target_pc) {
    auto continuation_items = collectVmUnresolvedContinuationWorkItems(
        M, callbacks.is_code_address, callbacks.has_defined_target,
        callbacks.normalize_target_pc);
    std::vector<FrontierWorkItem> frontier_items;
    frontier_items.reserve(continuation_items.size());
    for (const auto &item : continuation_items)
      frontier_items.push_back(makeClosureFrontierWorkItem(item));
    mergeFrontierItems(session_, frontier_items, &summary);
  }

  if ((phase == FrontierDiscoveryPhase::kOutputRootClosure ||
       phase == FrontierDiscoveryPhase::kCombined) &&
      callbacks.is_code_address && callbacks.has_defined_target &&
      callbacks.normalize_target_pc) {
    auto closure_items = collectOutputRootClosureWorkItems(
        M, callbacks.is_code_address, callbacks.has_defined_target,
        callbacks.normalize_target_pc,
        /*include_defined_targets=*/false);
    std::vector<FrontierWorkItem> frontier_items;
    frontier_items.reserve(closure_items.size());
    for (const auto &item : closure_items)
      frontier_items.push_back(makeClosureFrontierWorkItem(item));
    mergeFrontierItems(session_, frontier_items, &summary);
  }

  refreshDerivedViewsAndLoweringInputs(session_, M);
  session_.protector_model = buildProtectorModelFromSession(session_);
  applyProtectorModelToSession(session_, session_.protector_model);
  refreshFrontierCompatibilityViews(session_);
  summary.pending =
      static_cast<unsigned>(session_.late_frontier_work_items.size());
  return summary;
}

bool DevirtualizationOrchestrator::enqueueBoundaryContinuationWork(
    const llvm::Module &M, const BoundaryFact &boundary,
    llvm::StringRef source_name, std::optional<uint64_t> source_pc) {
  if (!boundary.continuation_pc)
    return false;
  FrontierWorkItem item =
      makeBoundaryContinuationWorkItem(boundary, source_name, source_pc);
  if (!item.target_pc || item.identity.empty())
    return false;

  const auto findNearbyTrackedSeed = [&](uint64_t continuation_pc)
      -> std::optional<uint64_t> {
    constexpr uint64_t kNearbySeedWindow = 0x40;
    std::optional<uint64_t> best_target;
    uint64_t best_distance = std::numeric_limits<uint64_t>::max();
    auto consider_target = [&](std::optional<uint64_t> maybe_target,
                               bool from_boundary_continuation) {
      if (!maybe_target || from_boundary_continuation)
        return;
      const uint64_t candidate_pc = *maybe_target;
      if (candidate_pc > continuation_pc)
        return;
      const uint64_t distance = continuation_pc - candidate_pc;
      if (distance > kNearbySeedWindow)
        return;
      if (!best_target || distance < best_distance) {
        best_target = candidate_pc;
        best_distance = distance;
      }
    };

    for (const auto &existing : session_.late_frontier_work_items)
      consider_target(existing.target_pc, existing.from_boundary_continuation);
    for (const auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
      (void)identity;
      consider_target(edge.target_pc, edge.from_boundary_continuation);
    }
    return best_target;
  };

  if (item.executable_target) {
    if (auto covered_pc =
            recoverCoveredTargetEntryPc(const_cast<llvm::Module &>(M),
                                        *item.target_pc)) {
      item.target_pc = *covered_pc;
      item.site_index = boundary.boundary_pc
                            ? boundaryContinuationSiteIndex(*boundary.boundary_pc,
                                                             *covered_pc)
                            : boundaryContinuationSiteIndex(*covered_pc,
                                                             *covered_pc);
      item.identity = makeBoundaryContinuationIdentity(boundary, *covered_pc);
      item.boundary->continuation_pc = *covered_pc;
      item.boundary->covered_entry_pc = *covered_pc;
      item.executable_target->effective_target_pc = *covered_pc;
      item.continuation_rationale = "boundary_reentry_intra_owner_seed";
      item.kind = FrontierWorkKind::kIntraOwnerContinuation;
      promoteBoundaryReentrySeed(session_, *covered_pc);
    } else if (auto nearby_seed = findNearbyTrackedSeed(*item.target_pc)) {
      item.target_pc = *nearby_seed;
      item.site_index = boundary.boundary_pc
                            ? boundaryContinuationSiteIndex(*boundary.boundary_pc,
                                                             *nearby_seed)
                            : boundaryContinuationSiteIndex(*nearby_seed,
                                                             *nearby_seed);
      item.identity =
          makeBoundaryContinuationIdentity(boundary, *nearby_seed);
      item.boundary->continuation_pc = *nearby_seed;
      item.boundary->covered_entry_pc = *nearby_seed;
      item.executable_target->effective_target_pc = *nearby_seed;
      item.continuation_rationale = "boundary_reentry_intra_owner_nearby_seed";
      item.kind = FrontierWorkKind::kIntraOwnerContinuation;
      promoteBoundaryReentrySeed(session_, *nearby_seed);
    }
  }

  if (auto existing = session_.graph.edge_facts_by_identity.find(item.identity);
      existing != session_.graph.edge_facts_by_identity.end()) {
    existing->second.status = FrontierWorkStatus::kInvalidated;
    existing->second.is_dirty = true;
    existing->second.failure_reason.clear();
  }
  mergeFrontierItems(session_, {item});
  refreshDerivedViewsAndLoweringInputs(session_, M);
  session_.protector_model = buildProtectorModelFromSession(session_);
  applyProtectorModelToSession(session_, session_.protector_model);
  refreshFrontierCompatibilityViews(session_);
  return true;
}

bool DevirtualizationOrchestrator::requeueBoundaryEdgesForTarget(
    const llvm::Module &M, uint64_t target_pc, llvm::StringRef reason) {
  bool changed = false;
  for (auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
    (void)identity;
    if (edge.from_boundary_continuation || !edge.boundary)
      continue;
    const bool matches_target =
        (edge.target_pc && *edge.target_pc == target_pc) ||
        (edge.boundary->native_target_pc &&
         *edge.boundary->native_target_pc == target_pc) ||
        (edge.boundary->boundary_pc &&
         *edge.boundary->boundary_pc == target_pc);
    if (!matches_target)
      continue;

    const auto disposition = boundaryDisposition(edge.boundary);
    if (edge.kind != FrontierWorkKind::kNativeCallBoundary &&
        disposition != VirtualExitDisposition::kVmExitNativeCallReenter &&
        disposition != VirtualExitDisposition::kVmExitNativeExecUnknownReturn) {
      continue;
    }

    if (edge.status != FrontierWorkStatus::kPending &&
        edge.status != FrontierWorkStatus::kInvalidated) {
      changed = true;
    }
    edge.status = FrontierWorkStatus::kInvalidated;
    edge.is_dirty = true;
    edge.retry_count = 0;
    edge.failure_reason = reason.str();
    auto handler_it = session_.graph.handler_nodes.find(edge.owner_function);
    if (handler_it != session_.graph.handler_nodes.end() &&
        handler_it->second.entry_va) {
      session_.graph.dirty_root_vas.insert(*handler_it->second.entry_va);
    }
  }

  if (!changed)
    return false;

  refreshDerivedViewsAndLoweringInputs(session_, M);
  session_.protector_model = buildProtectorModelFromSession(session_);
  applyProtectorModelToSession(session_, session_.protector_model);
  refreshFrontierCompatibilityViews(session_);
  return true;
}

FrontierAdvanceSummary DevirtualizationOrchestrator::advanceFrontierWork(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &callbacks) {
  FrontierAdvanceSummary summary;
  const bool debug_frontier =
      (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
  const bool recovery_mode = isTerminalBoundaryRecoveryModeEnabled();
  const bool enable_quarantined_frontier_exploration =
      envFlagEnabled("OMILL_ENABLE_QUARANTINED_FRONTIER_EXPLORATION");
  session_.protector_model = buildProtectorModelFromSession(session_);
  applyProtectorModelToSession(session_, session_.protector_model);
  std::vector<std::string> identities;
  identities.reserve(session_.late_frontier_work_items.size());
  for (const auto &item : session_.late_frontier_work_items)
    identities.push_back(item.identity);
  auto scheduling_rank = [&](const std::string &identity) {
    auto it = session_.graph.edge_facts_by_identity.find(identity);
    if (it == session_.graph.edge_facts_by_identity.end())
      return 99;
    switch (it->second.scheduling_class) {
      case FrontierSchedulingClass::kTrustedLive:
        return 0;
      case FrontierSchedulingClass::kWeakExecutable:
        return 1;
      case FrontierSchedulingClass::kNativeOrVmEnterBoundary:
        return 2;
      case FrontierSchedulingClass::kTerminalModeled:
        return 3;
      case FrontierSchedulingClass::kQuarantinedSelectorArm:
        return 4;
    }
    return 99;
  };
  auto hasTrackedNonBoundaryContinuationSeed = [&](uint64_t target_pc) {
    auto matches_target = [&](std::optional<uint64_t> maybe_target,
                              bool from_boundary_continuation) {
      return maybe_target && *maybe_target == target_pc &&
             !from_boundary_continuation;
    };
    for (const auto &existing : session_.late_frontier_work_items) {
      if (matches_target(existing.target_pc, existing.from_boundary_continuation))
        return true;
    }
    for (const auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
      (void)identity;
      if (matches_target(edge.target_pc, edge.from_boundary_continuation))
        return true;
    }
    return false;
  };
  std::stable_sort(identities.begin(), identities.end(),
                   [&](const std::string &lhs, const std::string &rhs) {
                     return scheduling_rank(lhs) < scheduling_rank(rhs);
                   });
  const bool has_non_quarantined_pending =
      llvm::any_of(identities, [&](const std::string &identity) {
        auto it = session_.graph.edge_facts_by_identity.find(identity);
        if (it == session_.graph.edge_facts_by_identity.end())
          return false;
        return it->second.scheduling_class !=
                   FrontierSchedulingClass::kQuarantinedSelectorArm &&
               (it->second.status == FrontierWorkStatus::kPending ||
                it->second.status == FrontierWorkStatus::kInvalidated);
      });

  for (const auto &identity : identities) {
    auto edge_it = session_.graph.edge_facts_by_identity.find(identity);
    if (edge_it == session_.graph.edge_facts_by_identity.end())
      continue;
    auto item = frontierWorkItemFromEdgeFact(edge_it->second);
    if (!edge_it->second.continuation_proof)
      classifyContinuationCandidate(item);
    if (!item.target_pc)
      continue;
    if (!enable_quarantined_frontier_exploration &&
        has_non_quarantined_pending &&
        item.scheduling_class ==
            FrontierSchedulingClass::kQuarantinedSelectorArm) {
      item.failure_reason = "quarantined_selector_arm_deferred";
      item.continuation_rationale = "deferred_until_trusted_progress_stalls";
      syncEdgeFactFromFrontierWorkItem(edge_it->second, item);
      summary.notes.push_back("deferred_quarantined:" + item.identity);
      continue;
    }
    const uint64_t target_pc = *item.target_pc;
    if (debug_frontier) {
      llvm::errs() << "[frontier-advance] begin id=" << item.identity
                   << " target=0x" << llvm::utohexstr(target_pc)
                   << " kind=" << toString(item.kind)
                   << " status=" << toString(item.status) << "\n";
    }
    bool item_crashed = false;
    bool item_handled = false;
    __try {
      auto process_item = [&]() -> bool {
        item.kind = classifyFrontierWorkItem(item, callbacks);
        if (debug_frontier) {
          llvm::errs() << "[frontier-advance] classified id=" << item.identity
                       << " target=0x" << llvm::utohexstr(target_pc)
                       << " kind=" << toString(item.kind) << "\n";
        }
        if (item.kind == FrontierWorkKind::kLiftableBlock &&
            canMaterializeFrontierTarget(M, target_pc, callbacks)) {
          item.status = FrontierWorkStatus::kSkippedMaterialized;
          item.failure_reason.clear();
          ++summary.skipped_materialized;
          summary.changed = true;
          linkFrontierItemToUnresolvedExit(session_, item);
          return true;
        }
        switch (item.kind) {
          case FrontierWorkKind::kIntraOwnerContinuation:
          case FrontierWorkKind::kBoundaryContinuation: {
            if (!item.boundary || !item.boundary->boundary_pc) {
              item.status = FrontierWorkStatus::kFailedDecode;
              item.failure_reason = "boundary_continuation_missing_boundary";
              ++summary.failed_decode;
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            const bool intra_owner =
                item.kind == FrontierWorkKind::kIntraOwnerContinuation;
            const uint64_t continuation_pc = target_pc;
            uint64_t preferred_target_pc =
                item.executable_target && item.executable_target->effective_target_pc
                    ? *item.executable_target->effective_target_pc
                    : continuation_pc;
            uint64_t lift_target_pc =
                safeNormalizeTargetPc(preferred_target_pc, callbacks);
            if (debug_frontier) {
              llvm::errs()
                  << "[frontier-advance] boundary-continuation-normalized id="
                  << item.identity << " continuation=0x"
                  << llvm::utohexstr(continuation_pc) << " preferred=0x"
                  << llvm::utohexstr(preferred_target_pc) << " lift=0x"
                  << llvm::utohexstr(lift_target_pc) << "\n";
            }
            __try {
              if (auto recovered_target = recoverBoundaryContinuationLiftTarget(
                      M, preferred_target_pc, callbacks)) {
                lift_target_pc = *recovered_target;
              } else if (preferred_target_pc != continuation_pc) {
                if (auto recovered_target = recoverBoundaryContinuationLiftTarget(
                        M, continuation_pc, callbacks)) {
                  lift_target_pc = *recovered_target;
                }
              }
            } __except (1) {
              item.status = FrontierWorkStatus::kFailedDecode;
              item.failure_reason =
                  "boundary_continuation_target_resolution_crashed";
              ++summary.failed_decode;
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            if (intra_owner) {
              if (auto transform =
                      detectPushImmediateJumpTransform(lift_target_pc, callbacks)) {
                item.boundary->covered_entry_pc =
                    transform->entry_pc ? transform->entry_pc : lift_target_pc;
                item.boundary->continuation_entry_transform = transform;
                if (transform->jump_target_pc) {
                  preferred_target_pc = *transform->jump_target_pc;
                  lift_target_pc = *transform->jump_target_pc;
                  item.target_pc = *transform->jump_target_pc;
                  item.boundary->continuation_pc = *transform->jump_target_pc;
                  item.executable_target->effective_target_pc =
                      *transform->jump_target_pc;
                }
                item.continuation_rationale =
                    "boundary_reentry_intra_owner_transform";
              } else if (!item.boundary->covered_entry_pc &&
                         recoverCoveredTargetEntryPc(M, preferred_target_pc)) {
                item.boundary->covered_entry_pc =
                    recoverCoveredTargetEntryPc(M, preferred_target_pc);
              }
            }
            if (debug_frontier) {
              llvm::errs()
                  << "[frontier-advance] boundary-continuation-recovered id="
                  << item.identity << " continuation=0x"
                  << llvm::utohexstr(continuation_pc) << " preferred=0x"
                  << llvm::utohexstr(preferred_target_pc) << " lift=0x"
                  << llvm::utohexstr(lift_target_pc) << "\n";
            }
            if (hasTrackedNonBoundaryContinuationSeed(preferred_target_pc)) {
              promoteBoundaryReentrySeed(session_, preferred_target_pc);
              if (debug_frontier) {
                llvm::errs()
                    << "[frontier-advance] boundary-continuation-redirected id="
                    << item.identity << " continuation=0x"
                    << llvm::utohexstr(continuation_pc) << " preferred=0x"
                    << llvm::utohexstr(preferred_target_pc) << "\n";
              }
              item.status = FrontierWorkStatus::kSkippedMaterialized;
              item.failure_reason =
                  "boundary_continuation_redirected_to_nearby_seed";
              ++summary.skipped_materialized;
              summary.changed = true;
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            if (intra_owner && item.boundary->covered_entry_pc &&
                hasTrackedNonBoundaryContinuationSeed(
                    *item.boundary->covered_entry_pc)) {
              promoteBoundaryReentrySeed(session_,
                                         *item.boundary->covered_entry_pc);
              if (debug_frontier) {
                llvm::errs()
                    << "[frontier-advance] boundary-continuation-redirected "
                       "covered-entry id="
                    << item.identity << " continuation=0x"
                    << llvm::utohexstr(continuation_pc) << " covered=0x"
                    << llvm::utohexstr(*item.boundary->covered_entry_pc)
                    << "\n";
              }
              item.status = FrontierWorkStatus::kSkippedMaterialized;
              item.failure_reason =
                  "boundary_continuation_redirected_to_covered_entry_seed";
              ++summary.skipped_materialized;
              summary.changed = true;
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            const uint64_t boundary_pc = *item.boundary->boundary_pc;
            const bool continuation_materialized =
                intra_owner ? hasExactMaterializedTarget(M, continuation_pc)
                            : canMaterializeFrontierTarget(M, continuation_pc,
                                                           callbacks);
            const bool lift_target_materialized =
                lift_target_pc != continuation_pc &&
                (intra_owner ? hasExactMaterializedTarget(M, lift_target_pc)
                             : canMaterializeFrontierTarget(M, lift_target_pc,
                                                            callbacks));
            if (continuation_materialized || lift_target_materialized) {
              if (debug_frontier) {
                llvm::errs()
                    << "[frontier-advance] boundary-continuation-materialize id="
                    << item.identity << " boundary=0x"
                    << llvm::utohexstr(boundary_pc) << "\n";
              }
              FrontierWorkItem boundary_item = item;
              boundary_item.target_pc = boundary_pc;
              boundary_item.kind = FrontierWorkKind::kNativeCallBoundary;
              boundary_item.from_boundary_continuation = false;
              if (auto *decl = getOrInsertNativeBoundaryDecl(
                      M, boundary_item, callbacks, &session_)) {
                annotateNativeBoundaryFunction(*decl, boundary_item, callbacks);
                item.status = FrontierWorkStatus::kSkippedMaterialized;
                item.failure_reason = "boundary_continuation_materialized";
                ++summary.skipped_materialized;
                summary.changed = true;
              } else {
                item.status = FrontierWorkStatus::kFailedDecode;
                item.failure_reason = "boundary_continuation_bridge_missing";
                ++summary.failed_decode;
              }
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            if (!safeCanDecodeTarget(lift_target_pc, callbacks)) {
              item.status = FrontierWorkStatus::kFailedDecode;
              item.failure_reason = "boundary_continuation_not_decodable";
              ++summary.failed_decode;
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            if (debug_frontier) {
              llvm::errs()
                  << "[frontier-advance] boundary-continuation-ready-to-lift id="
                  << item.identity << " lift=0x"
                  << llvm::utohexstr(lift_target_pc) << "\n";
            }
            break;
          }
          case FrontierWorkKind::kTerminalBoundary:
            item.status = FrontierWorkStatus::kClassifiedTerminal;
            if (!item.boundary)
              item.boundary = BoundaryFact{};
            item.boundary->exit_disposition = BoundaryDisposition::kVmExitTerminal;
            item.boundary->kind = BoundaryKind::kTerminalBoundary;
            item.failure_reason = "non_liftable_terminal_boundary";
            ++summary.classified_terminal;
            summary.changed = true;
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          case FrontierWorkKind::kVmEnterBoundary:
            item.status = FrontierWorkStatus::kClassifiedVmEnter;
            if (!item.boundary)
              item.boundary = BoundaryFact{};
            if (boundaryDisposition(item.boundary) == VirtualExitDisposition::kUnknown)
              item.boundary->exit_disposition = BoundaryDisposition::kVmEnter;
            item.boundary->is_vm_enter = true;
            item.boundary->kind = BoundaryKind::kVmEnterBoundary;
            if (auto *function = getOrInsertVmEnterBoundaryFunction(M, item))
              annotateVmEnterBoundaryFunction(*function, item);
            item.failure_reason = "vm_entry_boundary";
            ++summary.classified_vm_enter;
            summary.changed = true;
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          case FrontierWorkKind::kNativeCallBoundary:
            if (!item.boundary)
              item.boundary = BoundaryFact{};
            if (boundaryDisposition(item.boundary) == VirtualExitDisposition::kUnknown ||
                boundaryDisposition(item.boundary) == VirtualExitDisposition::kStayInVm) {
              item.boundary->exit_disposition =
                  boundaryContinuationVipPc(item.boundary)
                      ? BoundaryDisposition::kVmExitNativeCallReenter
                      : BoundaryDisposition::kVmExitNativeExecUnknownReturn;
            }
            item.boundary->kind = BoundaryKind::kNativeBoundary;
            if (debug_frontier) {
              llvm::errs() << "[frontier-advance] native-boundary-decl id="
                           << item.identity << " target=0x"
                           << llvm::utohexstr(target_pc) << "\n";
            }
            if (auto *decl =
                    getOrInsertNativeBoundaryDecl(M, item, callbacks, &session_)) {
              annotateNativeBoundaryFunction(*decl, item, callbacks);
              if (debug_frontier) {
                llvm::errs()
                    << "[frontier-advance] native-boundary-decl-ready id="
                    << item.identity << " fn=" << decl->getName() << "\n";
              }
              item.status = FrontierWorkStatus::kSkippedMaterialized;
              item.failure_reason = "native_call_boundary_declared";
              ++summary.skipped_materialized;
            } else {
              if (debug_frontier) {
                llvm::errs() << "[frontier-advance] native-boundary-no-decl id="
                             << item.identity << "\n";
              }
              item.status = FrontierWorkStatus::kClassifiedNativeExit;
              item.failure_reason = "native_call_boundary";
            }
            ++summary.classified_native_exit;
            summary.changed = true;
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          case FrontierWorkKind::kUnknownExecutableTarget:
            if (getOrInsertExecutableTargetFunction(M, item)) {
              item.status = FrontierWorkStatus::kSkippedMaterialized;
              item.failure_reason = "executable_target_declared";
              ++summary.skipped_materialized;
              summary.changed = true;
            } else {
              item.status = FrontierWorkStatus::kFailedDecode;
              item.failure_reason = "executable_target_not_decodable";
              ++summary.failed_decode;
            }
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          case FrontierWorkKind::kLiftableBlock:
            if (recovery_mode) {
              item.status = FrontierWorkStatus::kFailedLift;
              item.failure_reason = "recovery_mode_deferred_liftable_block";
              ++item.retry_count;
              ++summary.failed_lift;
              summary.changed = true;
              linkFrontierItemToUnresolvedExit(session_, item);
              return true;
            }
            break;
        }

        llvm::SmallVector<uint64_t, 4> discovered_targets;
        if (debug_frontier) {
          llvm::errs() << "[frontier-advance] lifting id=" << item.identity
                       << " target=0x" << llvm::utohexstr(target_pc) << "\n";
        }
        uint64_t lift_target_pc = target_pc;
        if (item.kind == FrontierWorkKind::kBoundaryContinuation ||
            item.kind == FrontierWorkKind::kIntraOwnerContinuation) {
          const bool intra_owner =
              item.kind == FrontierWorkKind::kIntraOwnerContinuation;
          const uint64_t preferred_target_pc =
              item.executable_target && item.executable_target->effective_target_pc
                  ? *item.executable_target->effective_target_pc
                  : target_pc;
          lift_target_pc = safeNormalizeTargetPc(preferred_target_pc, callbacks);
          if (debug_frontier) {
            llvm::errs()
                << "[frontier-advance] boundary-continuation-lift-normalized id="
                << item.identity << " target=0x"
                << llvm::utohexstr(target_pc) << " preferred=0x"
                << llvm::utohexstr(preferred_target_pc) << " lift=0x"
                << llvm::utohexstr(lift_target_pc) << "\n";
          }
          __try {
            if (auto recovered_target = recoverBoundaryContinuationLiftTarget(
                    M, preferred_target_pc, callbacks)) {
              lift_target_pc = *recovered_target;
            } else if (preferred_target_pc != target_pc) {
              if (auto recovered_target = recoverBoundaryContinuationLiftTarget(
                      M, target_pc, callbacks)) {
                lift_target_pc = *recovered_target;
              }
            }
          } __except (1) {
            item.status = FrontierWorkStatus::kFailedDecode;
            item.failure_reason =
                "boundary_continuation_target_resolution_crashed";
            ++summary.failed_decode;
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          }
          if (intra_owner) {
            if (auto transform =
                    detectPushImmediateJumpTransform(lift_target_pc, callbacks)) {
              item.boundary->covered_entry_pc =
                  transform->entry_pc ? transform->entry_pc : lift_target_pc;
              item.boundary->continuation_entry_transform = transform;
              if (transform->jump_target_pc) {
                lift_target_pc = *transform->jump_target_pc;
                item.target_pc = *transform->jump_target_pc;
                item.boundary->continuation_pc = *transform->jump_target_pc;
                item.executable_target->effective_target_pc =
                    *transform->jump_target_pc;
              }
            }
          }
          if (debug_frontier) {
            llvm::errs()
                << "[frontier-advance] boundary-continuation-lift-recovered id="
                << item.identity << " target=0x"
                << llvm::utohexstr(target_pc) << " preferred=0x"
                << llvm::utohexstr(preferred_target_pc) << " lift=0x"
                << llvm::utohexstr(lift_target_pc) << "\n";
          }
        }
        bool lift_crashed = false;
        llvm::Function *lifted = nullptr;
        __try {
          lifted = block_lifter.LiftBlock(lift_target_pc, discovered_targets);
        } __except (1) {
          lift_crashed = true;
        }
        if (lift_crashed) {
          if (debug_frontier) {
            llvm::errs() << "[frontier-advance] lift-crashed id="
                         << item.identity << " target=0x"
                         << llvm::utohexstr(target_pc) << "\n";
          }
          item.status = FrontierWorkStatus::kFailedLift;
          item.failure_reason = "block_lift_crashed";
          ++item.retry_count;
          ++summary.failed_lift;
          linkFrontierItemToUnresolvedExit(session_, item);
          return true;
        }
        if (debug_frontier) {
          llvm::errs() << "[frontier-advance] lift-return id=" << item.identity
                       << " target=0x" << llvm::utohexstr(lift_target_pc)
                       << " lifted=" << (lifted ? 1 : 0)
                       << " discovered=" << discovered_targets.size() << "\n";
        }
        if (lifted) {
          if (debug_frontier) {
            llvm::errs() << "[frontier-advance] note-lifted-target id="
                         << item.identity << " target=0x"
                         << llvm::utohexstr(target_pc) << "\n";
          }
          iterative_session.noteLiftedTarget(target_pc);
          if (lift_target_pc != target_pc)
            iterative_session.noteLiftedTarget(lift_target_pc);
          if (debug_frontier) {
            llvm::errs() << "[frontier-advance] noted-lifted-target id="
                         << item.identity << " target=0x"
                         << llvm::utohexstr(target_pc) << "\n";
          }
          item.status = FrontierWorkStatus::kLifted;
          item.failure_reason.clear();
          if ((item.kind == FrontierWorkKind::kBoundaryContinuation ||
               item.kind == FrontierWorkKind::kIntraOwnerContinuation) &&
              item.boundary && item.boundary->boundary_pc) {
            FrontierWorkItem boundary_item = item;
            boundary_item.target_pc = item.boundary->boundary_pc;
            boundary_item.kind = FrontierWorkKind::kNativeCallBoundary;
            boundary_item.from_boundary_continuation = false;
            if (auto *decl =
                    getOrInsertNativeBoundaryDecl(M, boundary_item, callbacks,
                                                  &session_)) {
              annotateNativeBoundaryFunction(*decl, boundary_item, callbacks);
            }
          }
          ++item.retry_count;
          ++summary.lifted;
          summary.changed = true;
          linkFrontierItemToUnresolvedExit(session_, item);
          return true;
        }

        item.status = FrontierWorkStatus::kFailedLift;
        item.failure_reason = "block_lift_returned_null";
        ++item.retry_count;
        ++summary.failed_lift;
        linkFrontierItemToUnresolvedExit(session_, item);
        return true;
      };
      item_handled = process_item();
    } __except (1) {
      item_crashed = true;
    }
    if (item_crashed) {
      if (debug_frontier) {
        llvm::errs() << "[frontier-advance] item-crashed id=" << item.identity
                     << " target=0x" << llvm::utohexstr(target_pc) << "\n";
      }
      item.status = FrontierWorkStatus::kFailedLift;
      item.failure_reason = "frontier_processing_crashed";
      ++item.retry_count;
      ++summary.failed_lift;
      summary.changed = true;
      summary.notes.push_back("crashed:" + item.identity);
      linkFrontierItemToUnresolvedExit(session_, item);
      syncEdgeFactFromFrontierWorkItem(edge_it->second, item);
      continue;
    }
    if (item_handled)
      syncEdgeFactFromFrontierWorkItem(edge_it->second, item);
  }

  if (debug_frontier)
    llvm::errs() << "[frontier-advance] refresh-session-core-state\n";
  refreshSessionCoreState(session_, M);
  if (debug_frontier)
    llvm::errs() << "[frontier-advance] refresh-frontier-compatibility\n";
  refreshFrontierCompatibilityViews(session_);
  summary.pending =
      static_cast<unsigned>(session_.late_frontier_work_items.size());
  return summary;
}

FrontierRoundSummary DevirtualizationOrchestrator::runFrontierRound(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &callbacks, FrontierDiscoveryPhase phase) {
  FrontierRoundSummary summary;
  __try {
    summary.discover = discoverFrontierWork(M, callbacks, phase);
    summary.advance =
        advanceFrontierWork(M, block_lifter, iterative_session, callbacks);
  } __except (1) {
    summary.crashed = true;
    return summary;
  }
  summary.changed = summary.advance.changed;
  return summary;
}

FrontierIterationSummary DevirtualizationOrchestrator::runFrontierIterations(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &frontier_callbacks, FrontierDiscoveryPhase phase,
    unsigned max_rounds, const FrontierIterationCallbacks &iteration_callbacks,
    const VmEnterChildImportCallbacks *vm_enter_import_callbacks) {
  FrontierIterationSummary summary;
  for (unsigned round = 0; round < max_rounds; ++round) {
    if (iteration_callbacks.before_frontier_round &&
        !iteration_callbacks.before_frontier_round(round)) {
      break;
    }

    auto round_summary =
        runFrontierRound(M, block_lifter, iterative_session, frontier_callbacks,
                         phase);
    summary.round_summaries.push_back(round_summary);
    if (round_summary.crashed) {
      summary.crashed = true;
      break;
    }

    VmEnterChildImportSummary import_summary;
    if (vm_enter_import_callbacks && vm_enter_import_callbacks->enabled) {
      import_summary =
          importNestedVmEnterChildren(M, *vm_enter_import_callbacks);
      summary.vm_enter_children_imported += import_summary.imported;
    }
    summary.import_summaries.push_back(import_summary);

    bool callback_changed = false;
    if (iteration_callbacks.after_frontier_round) {
      callback_changed = iteration_callbacks.after_frontier_round(
          round, round_summary, import_summary);
    }

    ++summary.rounds_run;
    const bool round_changed =
        round_summary.changed || import_summary.changed || callback_changed;
    summary.changed = summary.changed || round_changed;
    if (!round_changed)
      break;
  }
  return summary;
}

VmEnterChildImportSummary DevirtualizationOrchestrator::importNestedVmEnterChildren(
    llvm::Module &M, const VmEnterChildImportCallbacks &callbacks) {
  VmEnterChildImportSummary summary;
  if (!callbacks.enabled || !callbacks.try_import_target)
    return summary;

  auto isModeledBoundaryPlaceholder = [](llvm::Function *F) {
    if (!F)
      return false;
    auto fact = readBoundaryFact(*F);
    if (!fact)
      return false;
    switch (fact->kind) {
      case BoundaryKind::kNativeBoundary:
      case BoundaryKind::kTerminalBoundary:
      case BoundaryKind::kVmEnterBoundary:
      case BoundaryKind::kNestedVmEnterBoundary:
        return true;
    }
    return false;
  };

  auto isVmEnterBoundaryFact = [](const std::optional<BoundaryFact> &fact) {
    if (!fact)
      return false;
    return fact->is_vm_enter || fact->is_nested_vm_enter ||
           fact->kind == BoundaryKind::kVmEnterBoundary ||
           fact->kind == BoundaryKind::kNestedVmEnterBoundary ||
           boundaryDisposition(fact) == VirtualExitDisposition::kVmEnter ||
           boundaryDisposition(fact) == VirtualExitDisposition::kNestedVmEnter;
  };

  auto isVmEnterCandidate = [&](const FrontierWorkItem &item) {
    if (!item.target_pc || item.from_boundary_continuation)
      return false;
    return item.kind == FrontierWorkKind::kVmEnterBoundary ||
           isVmEnterBoundaryFact(item.boundary);
  };

  llvm::SmallVector<FrontierWorkItem, 8> import_candidates;
  llvm::SmallDenseMap<uint64_t, unsigned, 8> candidate_index_by_target;
  auto mergeCandidate = [&](FrontierWorkItem item) {
    if (!isVmEnterCandidate(item))
      return;
    if (item.kind != FrontierWorkKind::kVmEnterBoundary)
      item.kind = FrontierWorkKind::kVmEnterBoundary;
    if (!item.boundary)
      item.boundary = BoundaryFact{};
    if (boundaryDisposition(item.boundary) == VirtualExitDisposition::kUnknown)
      item.boundary->exit_disposition = BoundaryDisposition::kVmEnter;
    item.boundary->is_nested_vm_enter =
        boundaryDisposition(item.boundary) ==
        VirtualExitDisposition::kNestedVmEnter;
    item.boundary->is_vm_enter = !item.boundary->is_nested_vm_enter;
    item.boundary->kind = item.boundary->is_nested_vm_enter
                              ? BoundaryKind::kNestedVmEnterBoundary
                              : BoundaryKind::kVmEnterBoundary;
    if (item.status == FrontierWorkStatus::kPending ||
        item.status == FrontierWorkStatus::kInvalidated) {
      item.status = FrontierWorkStatus::kClassifiedVmEnter;
      item.failure_reason = "vm_entry_boundary";
    }

    const uint64_t target_pc = *item.target_pc;
    auto found = candidate_index_by_target.find(target_pc);
    if (found == candidate_index_by_target.end()) {
      candidate_index_by_target[target_pc] = import_candidates.size();
      import_candidates.push_back(std::move(item));
      return;
    }

    auto &existing = import_candidates[found->second];
    if (existing.identity.empty() && !item.identity.empty())
      existing.identity = item.identity;
    if (existing.owner_function.empty() && !item.owner_function.empty())
      existing.owner_function = item.owner_function;
    if (!existing.site_pc && item.site_pc)
      existing.site_pc = item.site_pc;
    if (!existing.boundary && item.boundary)
      existing.boundary = item.boundary;
    if (existing.kind != FrontierWorkKind::kVmEnterBoundary &&
        item.kind == FrontierWorkKind::kVmEnterBoundary)
      existing.kind = item.kind;
    if (existing.status != FrontierWorkStatus::kClassifiedVmEnter &&
        item.status == FrontierWorkStatus::kClassifiedVmEnter) {
      existing.status = item.status;
      existing.failure_reason = item.failure_reason;
    }
  };

  for (const auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc)
      continue;
    FrontierWorkItem item = frontierWorkItemFromEdgeFact(edge);
    mergeCandidate(std::move(item));
  }
  for (const auto &item : session_.late_frontier_work_items)
    mergeCandidate(item);

  unsigned imported = 0;
  auto updateVmEnterFailureReason = [&](uint64_t target_pc,
                                        llvm::StringRef failure_reason) {
    for (auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
      (void)identity;
      if (!edge.target_pc || *edge.target_pc != target_pc)
        continue;
      const bool is_vm_enter_edge =
          edge.kind == FrontierWorkKind::kVmEnterBoundary ||
          (edge.boundary &&
           (edge.boundary->is_vm_enter || edge.boundary->is_nested_vm_enter ||
            edge.boundary->kind == BoundaryKind::kVmEnterBoundary ||
            edge.boundary->kind == BoundaryKind::kNestedVmEnterBoundary));
      if (!is_vm_enter_edge)
        continue;
      edge.failure_reason = failure_reason.str();
    }
    for (auto &item : session_.late_frontier_work_items) {
      if (!item.target_pc || *item.target_pc != target_pc)
        continue;
      const bool is_vm_enter_item =
          item.kind == FrontierWorkKind::kVmEnterBoundary ||
          (item.boundary &&
           (item.boundary->is_vm_enter || item.boundary->is_nested_vm_enter ||
            item.boundary->kind == BoundaryKind::kVmEnterBoundary ||
            item.boundary->kind == BoundaryKind::kNestedVmEnterBoundary));
      if (!is_vm_enter_item)
        continue;
      item.failure_reason = failure_reason.str();
    }
  };
  for (const auto &candidate : import_candidates) {
    if (!candidate.target_pc)
      continue;
    const uint64_t target_pc = *candidate.target_pc;
    if (!candidate.identity.empty()) {
      auto &edge = session_.graph.edge_facts_by_identity[candidate.identity];
      edge.identity = candidate.identity;
      syncEdgeFactFromFrontierWorkItem(edge, candidate);
      if (candidate.identity.find("closure:") == 0)
        edge.from_output_root_closure = true;
    }

    auto *existing = findLiftedOrCoveredFunctionByPC(M, target_pc);
    auto *placeholder = findStructuralCodeTargetFunctionByPC(M, target_pc);
    if (!placeholder)
      placeholder = existing;
    if (!placeholder) {
      FrontierWorkItem item = candidate;
      placeholder = getOrInsertVmEnterBoundaryFunction(M, item);
      if (placeholder)
        annotateVmEnterBoundaryFunction(*placeholder, item);
    }

    const auto placeholder_fact =
        placeholder ? readBoundaryFact(*placeholder) : std::nullopt;
    const bool modeled_placeholder =
        placeholder && isModeledBoundaryPlaceholder(placeholder);
    if (existing && !existing->isDeclaration() && !modeled_placeholder) {
      continue;
    }

    if (!placeholder || !placeholder_fact) {
      continue;
    }
    const bool retry_modeled_placeholder =
        modeled_placeholder &&
        session_.imported_vm_enter_child_roots.count(target_pc) == 0;
    if (session_.attempted_vm_enter_child_import_pcs.count(target_pc) != 0 &&
        !retry_modeled_placeholder) {
      continue;
    }
    session_.attempted_vm_enter_child_import_pcs.insert(target_pc);
    if (imported >= callbacks.max_imports)
      break;

    ++summary.attempted;
    std::string failure_reason;
    llvm::Function *imported_root = nullptr;
      if (!callbacks.try_import_target(target_pc, *placeholder, failure_reason,
                                     imported_root) ||
        !imported_root) {
      if (failure_reason.empty())
        failure_reason = "child_import_failed";
      updateVmEnterFailureReason(target_pc, failure_reason);
      summary.notes.push_back(std::string("target=0x") +
                              llvm::utohexstr(target_pc) + ":" +
                              failure_reason);
      continue;
    }
    if (imported_root->getFunctionType() != placeholder->getFunctionType()) {
      updateVmEnterFailureReason(target_pc, "type_mismatch");
      summary.notes.push_back(std::string("target=0x") +
                              llvm::utohexstr(target_pc) + ":type_mismatch:" +
                              imported_root->getName().str());
      continue;
    }

    placeholder->replaceAllUsesWith(imported_root);
    if (placeholder->use_empty())
      placeholder->eraseFromParent();
    if (callbacks.on_imported_target)
      callbacks.on_imported_target(target_pc);
    updateVmEnterFailureReason(target_pc, "");
    session_.imported_vm_enter_child_roots[target_pc] =
        imported_root->getName().str();
    summary.notes.push_back(std::string("imported target=0x") +
                            llvm::utohexstr(target_pc) + " as " +
                            imported_root->getName().str());
    ++imported;
    ++summary.imported;
    summary.changed = true;
  }

  if (summary.changed) {
    refreshSessionCoreState(session_, M);
    for (const auto &[target_pc, imported_name] :
         session_.imported_vm_enter_child_roots) {
      auto &region = session_.graph.region_nodes_by_entry_pc[target_pc];
      region.entry_pc = target_pc;
      region.kind = SessionRegionKind::kNestedVmEnter;
      region.status = SessionRegionStatus::kImported;
      region.imported_root_function = imported_name;
    }
    refreshFrontierCompatibilityViews(session_);
  }
  return summary;
}

bool DevirtualizationOrchestrator::hasUnstableFrontierState() const {
  for (const auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
    (void)identity;
    switch (edge.status) {
      case FrontierWorkStatus::kPending:
      case FrontierWorkStatus::kFailedDecode:
      case FrontierWorkStatus::kFailedLift:
      case FrontierWorkStatus::kInvalidated:
        return true;
      case FrontierWorkStatus::kLifted:
      case FrontierWorkStatus::kClassifiedNativeExit:
      case FrontierWorkStatus::kClassifiedTerminal:
      case FrontierWorkStatus::kClassifiedVmEnter:
      case FrontierWorkStatus::kSkippedMaterialized:
        break;
    }
  }
  return false;
}

bool DevirtualizationOrchestrator::hasBlockingUnstableFrontierState(
    const llvm::Module &M) const {
  auto &mutable_module = const_cast<llvm::Module &>(M);
  for (const auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
    (void)identity;
    switch (edge.status) {
      case FrontierWorkStatus::kLifted:
      case FrontierWorkStatus::kClassifiedNativeExit:
      case FrontierWorkStatus::kClassifiedTerminal:
      case FrontierWorkStatus::kClassifiedVmEnter:
      case FrontierWorkStatus::kSkippedMaterialized:
        continue;
      case FrontierWorkStatus::kPending:
      case FrontierWorkStatus::kFailedDecode:
      case FrontierWorkStatus::kFailedLift:
      case FrontierWorkStatus::kInvalidated:
        break;
    }

    if (!edge.target_pc)
      return true;

    if (findStructuralCodeTargetFunctionByPC(mutable_module, *edge.target_pc) ||
        findLiftedOrBlockFunctionByPC(mutable_module, *edge.target_pc)) {
      continue;
    }

    auto boundary_it = session_.graph.boundary_facts_by_target.find(*edge.target_pc);
    if (boundary_it != session_.graph.boundary_facts_by_target.end() &&
        boundary_it->second.declaration_name.has_value() &&
        mutable_module.getFunction(*boundary_it->second.declaration_name)) {
      continue;
    }

    return true;
  }
  return false;
}

std::string DevirtualizationOrchestrator::summarizeFrontierAdvance(
    const FrontierAdvanceSummary &summary) const {
  return (llvm::Twine("discovered=") + llvm::Twine(summary.discovered) +
          ",pending=" + llvm::Twine(summary.pending) +
          ",lifted=" + llvm::Twine(summary.lifted) +
          ",native=" + llvm::Twine(summary.classified_native_exit) +
          ",terminal=" + llvm::Twine(summary.classified_terminal) +
          ",vmenter=" + llvm::Twine(summary.classified_vm_enter) +
          ",failed_decode=" + llvm::Twine(summary.failed_decode) +
          ",failed_lift=" + llvm::Twine(summary.failed_lift) +
          ",skipped=" + llvm::Twine(summary.skipped_materialized))
      .str();
}

ProtectorModel DevirtualizationOrchestrator::buildProtectorModel() const {
  return buildProtectorModelFromSession(session_);
}

ProtectorValidationReport DevirtualizationOrchestrator::buildProtectorValidationReport(
    const llvm::Module &M) const {
  ProtectorValidationReport report;
  report.model = buildProtectorModel();
  auto bump = [&](ProtectorValidationIssueClass klass) {
    ++report.counts_by_class[toString(klass)];
  };

  for (const auto &candidate : report.model.continuation_candidates) {
    if (candidate.liveness == ContinuationLiveness::kQuarantined) {
      ProtectorValidationIssue issue;
      issue.issue_class =
          ProtectorValidationIssueClass::kQuarantinedSelectorArm;
      issue.edge_identity = candidate.edge_identity;
      issue.caller_name = candidate.source_handler_name;
      issue.message = candidate.rationale;
      report.issues.push_back(std::move(issue));
      bump(ProtectorValidationIssueClass::kQuarantinedSelectorArm);
      continue;
    }
    if (candidate.provenance == ContinuationProvenance::kTerminalBoundary) {
      ProtectorValidationIssue issue;
      issue.issue_class = ProtectorValidationIssueClass::kTerminalEdge;
      issue.edge_identity = candidate.edge_identity;
      issue.caller_name = candidate.source_handler_name;
      issue.message = candidate.rationale;
      report.issues.push_back(std::move(issue));
      bump(ProtectorValidationIssueClass::kTerminalEdge);
      continue;
    }
    if (candidate.provenance == ContinuationProvenance::kNativeBoundary ||
        candidate.provenance == ContinuationProvenance::kVmEnterBoundary) {
      ProtectorValidationIssue issue;
      issue.issue_class =
          ProtectorValidationIssueClass::kNativeOrVmEnterBoundary;
      issue.edge_identity = candidate.edge_identity;
      issue.caller_name = candidate.source_handler_name;
      issue.message = candidate.rationale;
      report.issues.push_back(std::move(issue));
      bump(ProtectorValidationIssueClass::kNativeOrVmEnterBoundary);
    }
  }

  for (const auto &F : M) {
    if (F.isDeclaration() && F.getName().starts_with("__remill_")) {
      ProtectorValidationIssue issue;
      issue.issue_class = ProtectorValidationIssueClass::kRemillRuntimeLeak;
      issue.callee_name = F.getName().str();
      issue.message = "reachable runtime decl requires caller-path validation";
      report.issues.push_back(std::move(issue));
      bump(ProtectorValidationIssueClass::kRemillRuntimeLeak);
    }
  }

  return report;
}

std::vector<std::string> DevirtualizationOrchestrator::collectInvariantViolations(
    const llvm::Module &M, DevirtualizationOutputMode mode) const {
  std::vector<std::string> violations;
  RemillNormalizationOrchestrator normalization;
  const auto summary = normalization.summarize(M);

  if (summary.unresolved_dispatch_intrinsics > 0)
    violations.emplace_back("unresolved_dispatch_intrinsics");

  if (summary.legacy_omill_dispatch_intrinsics > 0)
    violations.emplace_back("legacy_omill_dispatch_intrinsics");

  if (mode == DevirtualizationOutputMode::kNoABI &&
      summary.live_memory_intrinsics > 0)
    violations.emplace_back("live_remill_memory_intrinsics");

  if (mode == DevirtualizationOutputMode::kABI &&
      hasClosedSliceWrapperLadder(M)) {
    violations.emplace_back("closed_slice_wrapper_ladder");
  }

  if (mode == DevirtualizationOutputMode::kABI &&
      summary.native_wrapper_functions > 0) {
    violations.emplace_back("native_wrapper_functions_present");
  }

  return violations;
}

DevirtualizationEpochSummary DevirtualizationOrchestrator::summarizeEpoch(
    DevirtualizationEpoch epoch, const llvm::Module &M,
    DevirtualizationOutputMode mode, bool changed, std::string note) const {
  RemillNormalizationOrchestrator normalization;
  const auto normalization_summary = normalization.summarize(M);

  DevirtualizationEpochSummary summary;
  summary.epoch = epoch;
  summary.changed = changed;
  summary.note = std::move(note);
  summary.units_lifted = session_.latest_round.units_lifted;
  summary.units_reused = session_.latest_round.units_reused;
  summary.unresolved_exits_complete =
      session_.latest_round.unresolved_exits_complete;
  summary.unresolved_exits_incomplete =
      session_.latest_round.unresolved_exits_incomplete;
  summary.unresolved_exits_invalidated =
      session_.latest_round.unresolved_exits_invalidated;
  summary.normalization_failures = session_.latest_round.normalization_failures;
  summary.dispatches_materialized =
      session_.latest_round.dispatches_materialized;
  summary.leaked_runtime_artifacts =
      session_.latest_round.leaked_runtime_artifacts;
  summary.normalization_verifier_clean = normalization_summary.verifier_clean;
  summary.normalization_diagnostics = normalization_summary.diagnostics;
  summary.invariant_violations = collectInvariantViolations(M, mode);
  summary.clean = summary.invariant_violations.empty();
  return summary;
}

void DevirtualizationOrchestrator::recordEpoch(DevirtualizationEpoch epoch,
                                               const llvm::Module &M,
                                               DevirtualizationOutputMode mode,
                                               bool changed,
                                               std::string note) {
  if (!policy_.emit_epoch_summaries)
    return;
  session_.epochs.push_back(
      summarizeEpoch(epoch, M, mode, changed, std::move(note)));
}

const char *toString(DevirtualizationConfidence confidence) {
  switch (confidence) {
    case DevirtualizationConfidence::kLow:
      return "low";
    case DevirtualizationConfidence::kMedium:
      return "medium";
    case DevirtualizationConfidence::kHigh:
      return "high";
  }
  return "low";
}

const char *toString(DevirtualizationEpoch epoch) {
  switch (epoch) {
    case DevirtualizationEpoch::kInitialLiftNormalization:
      return "initial_lift_normalization";
    case DevirtualizationEpoch::kDetectionSeedExtraction:
      return "detection_seed_extraction";
    case DevirtualizationEpoch::kFrontierScheduling:
      return "frontier_scheduling";
    case DevirtualizationEpoch::kIncrementalBlockLift:
      return "incremental_block_lift";
    case DevirtualizationEpoch::kNormalizationCacheAdmission:
      return "normalization_cache_admission";
    case DevirtualizationEpoch::kCfgMaterialization:
      return "cfg_materialization";
    case DevirtualizationEpoch::kContinuationClosure:
      return "continuation_closure";
    case DevirtualizationEpoch::kAbiOrNoAbiFinalization:
      return "abi_or_noabi_finalization";
    case DevirtualizationEpoch::kFinalInvariantVerification:
      return "final_invariant_verification";
  }
  return "initial_lift_normalization";
}

const char *toString(DevirtualizationCompatReason reason) {
  switch (reason) {
    case DevirtualizationCompatReason::kNone:
      return "none";
    case DevirtualizationCompatReason::kCompatibilityFlag:
      return "compatibility_flag";
    case DevirtualizationCompatReason::kFastPlainExportRootFallback:
      return "fast_plain_export_root_fallback";
    case DevirtualizationCompatReason::kStableLargeExportRootFallback:
      return "stable_large_export_root_fallback";
    case DevirtualizationCompatReason::kNoVmLikeCandidates:
      return "no_vm_like_candidates";
    case DevirtualizationCompatReason::kNoRootLocalDevirtShape:
      return "no_root_local_devirt_shape";
    case DevirtualizationCompatReason::kLegacyVmPathSuppressed:
      return "legacy_vm_path_suppressed";
    case DevirtualizationCompatReason::kPreAbiNoAbiCleanup:
      return "pre_abi_noabi_cleanup";
  }
  return "none";
}

const char *toString(DevirtualizationExportRootFallbackMode mode) {
  switch (mode) {
    case DevirtualizationExportRootFallbackMode::kNone:
      return "none";
    case DevirtualizationExportRootFallbackMode::kFastPlain:
      return "fast_plain";
    case DevirtualizationExportRootFallbackMode::kStableLarge:
      return "stable_large";
  }
  return "none";
}

const char *toString(UnresolvedExitKind kind) {
  switch (kind) {
    case UnresolvedExitKind::kDispatchJump:
      return "dispatch_jump";
    case UnresolvedExitKind::kDispatchCall:
      return "dispatch_call";
    case UnresolvedExitKind::kProtectedBoundary:
      return "protected_boundary";
    case UnresolvedExitKind::kUnknownContinuation:
      return "unknown_continuation";
  }
  return "unknown_continuation";
}

const char *toString(ExitCompleteness completeness) {
  switch (completeness) {
    case ExitCompleteness::kComplete:
      return "complete";
    case ExitCompleteness::kIncomplete:
      return "incomplete";
    case ExitCompleteness::kInvalidated:
      return "invalidated";
  }
  return "incomplete";
}

const char *toString(LiftUnitCacheStatus status) {
  switch (status) {
    case LiftUnitCacheStatus::kFresh:
      return "fresh";
    case LiftUnitCacheStatus::kReused:
      return "reused";
    case LiftUnitCacheStatus::kInvalidated:
      return "invalidated";
  }
  return "fresh";
}

const char *toString(VipTrackingStatus status) {
  switch (status) {
    case VipTrackingStatus::kUnknown:
      return "unknown";
    case VipTrackingStatus::kResolved:
      return "resolved";
    case VipTrackingStatus::kSymbolic:
      return "symbolic";
  }
  return "unknown";
}

const char *toString(FrontierDiscoveryPhase phase) {
  switch (phase) {
    case FrontierDiscoveryPhase::kUnresolvedOnly:
      return "unresolved_only";
    case FrontierDiscoveryPhase::kVmUnresolvedContinuations:
      return "vm_unresolved_continuations";
    case FrontierDiscoveryPhase::kOutputRootClosure:
      return "output_root_closure";
    case FrontierDiscoveryPhase::kCombined:
      return "combined";
  }
  return "combined";
}

const char *toString(FrontierWorkKind kind) {
  switch (kind) {
    case FrontierWorkKind::kLiftableBlock:
      return "liftable_block";
    case FrontierWorkKind::kIntraOwnerContinuation:
      return "intra_owner_continuation";
    case FrontierWorkKind::kBoundaryContinuation:
      return "boundary_continuation";
    case FrontierWorkKind::kNativeCallBoundary:
      return "native_call_boundary";
    case FrontierWorkKind::kTerminalBoundary:
      return "terminal_boundary";
    case FrontierWorkKind::kVmEnterBoundary:
      return "vm_enter_boundary";
    case FrontierWorkKind::kUnknownExecutableTarget:
      return "unknown_executable_target";
  }
  return "unknown_executable_target";
}

const char *toString(FrontierWorkStatus status) {
  switch (status) {
    case FrontierWorkStatus::kPending:
      return "pending";
    case FrontierWorkStatus::kLifted:
      return "lifted";
    case FrontierWorkStatus::kClassifiedTerminal:
      return "classified_terminal";
    case FrontierWorkStatus::kClassifiedNativeExit:
      return "classified_native_exit";
    case FrontierWorkStatus::kClassifiedVmEnter:
      return "classified_vm_enter";
    case FrontierWorkStatus::kFailedDecode:
      return "failed_decode";
    case FrontierWorkStatus::kFailedLift:
      return "failed_lift";
    case FrontierWorkStatus::kSkippedMaterialized:
      return "skipped_materialized";
    case FrontierWorkStatus::kInvalidated:
      return "invalidated";
  }
  return "pending";
}

}  // namespace omill

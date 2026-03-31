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
#include <map>
#include <optional>
#include <set>

#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/BC/BlockLifter.h"
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
  SessionGraphState state;
};

std::map<const llvm::Module *, SessionGraphProjectionCacheEntry> &
sessionGraphProjectionCache() {
  static auto *cache =
      new std::map<const llvm::Module *, SessionGraphProjectionCacheEntry>();
  return *cache;
}

std::optional<uint64_t> parseOptionalHexAttr(llvm::Attribute attr) {
  if (!attr.isValid())
    return std::nullopt;
  auto text = attr.getValueAsString();
  if (text.empty())
    return std::nullopt;
  if (text.consume_front("0x") || text.consume_front("0X")) {
  }
  uint64_t value = 0;
  if (text.getAsInteger(16, value))
    return std::nullopt;
  return value;
}

std::optional<VirtualExitDisposition> parseVirtualExitDisposition(
    const llvm::CallBase &call) {
  auto attr = call.getFnAttr("omill.virtual_exit_disposition");
  if (!attr.isValid())
    return std::nullopt;
  auto text = attr.getValueAsString();
  if (text == "stay_in_vm")
    return VirtualExitDisposition::kStayInVm;
  if (text == "vm_exit_terminal")
    return VirtualExitDisposition::kVmExitTerminal;
  if (text == "vm_exit_native_call_reenter")
    return VirtualExitDisposition::kVmExitNativeCallReenter;
  if (text == "vm_exit_native_exec_unknown_return")
    return VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
  if (text == "vm_enter")
    return VirtualExitDisposition::kVmEnter;
  if (text == "nested_vm_enter")
    return VirtualExitDisposition::kNestedVmEnter;
  return VirtualExitDisposition::kUnknown;
}

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

bool hasKnownMaterializedTarget(const llvm::Module &M, uint64_t pc) {
  if (M.getFunction(liftedFunctionName(pc)))
    return true;
  auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (M.getFunction(block_name))
    return true;
  auto trace_name = (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  return M.getFunction(trace_name) != nullptr;
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
  item.continuation_vip_pc = site.continuation_vip_pc;
  item.vip_symbolic = site.vip_symbolic;
  item.exit_disposition = site.exit_disposition;
  item.identity = unresolvedExitIdentity(site);
  item.status = site.completeness == ExitCompleteness::kInvalidated
                    ? FrontierWorkStatus::kInvalidated
                    : FrontierWorkStatus::kPending;
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
  item.continuation_vip_pc = closure_item.continuation_vip_pc;
  item.vip_symbolic = closure_item.vip_symbolic;
  item.exit_disposition = closure_item.exit_disposition;
  item.identity = "closure:" + closure_item.identity;
  item.status = FrontierWorkStatus::kPending;
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
  item.continuation_vip_pc = edge.continuation_vip_pc;
  item.vip_symbolic = edge.vip_symbolic;
  item.exit_disposition = edge.exit_disposition;
  item.kind = edge.kind;
  item.status = edge.status;
  item.retry_count = edge.retry_count;
  item.failure_reason = edge.failure_reason;
  item.identity = edge.identity;
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
  edge.continuation_vip_pc = item.continuation_vip_pc;
  edge.vip_symbolic = item.vip_symbolic;
  edge.exit_disposition = item.exit_disposition;
  edge.kind = item.kind;
  edge.status = item.status;
  edge.retry_count = item.retry_count;
  edge.failure_reason = item.failure_reason;
  edge.is_dirty = false;
}

llvm::stable_hash handlerFingerprint(const llvm::Function &F) {
  return llvm::StructuralHash(F, /*DetailedHash=*/true);
}

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
  std::set<std::string> live_names;
  for (const auto &F : M) {
    if (!isTrackedLiftUnit(F) && !F.hasFnAttribute("omill.output_root") &&
        !F.hasFnAttribute("omill.closed_root_slice_root")) {
      continue;
    }
    const std::string name = F.getName().str();
    live_names.insert(name);
    auto *node = &graph.handler_nodes[name];
    node->function_name = name;
    node->entry_va = extractLiftUnitVA(F);
    node->fingerprint = handlerFingerprint(F);
    node->is_defined = !F.isDeclaration();
    node->is_output_root = F.hasFnAttribute("omill.output_root");
    node->is_closed_root_slice_root =
        F.hasFnAttribute("omill.closed_root_slice_root");
    node->is_specialized = F.hasFnAttribute("omill.virtual_specialized");
    node->is_dirty = graph.dirty_function_names.count(name) != 0;
    if (node->entry_va)
      graph.dirty_root_vas.insert(*node->entry_va);
  }

  for (auto it = graph.handler_nodes.begin(); it != graph.handler_nodes.end();) {
    if (live_names.count(it->first) != 0) {
      ++it;
      continue;
    }
    it = graph.handler_nodes.erase(it);
  }
}

void refreshSessionEdgesAndFrontier(DevirtualizationSession &session) {
  auto &graph = session.graph;
  for (const auto &site : session.unresolved_exits) {
    if (!site.target_pc)
      continue;
    if (site.kind != UnresolvedExitKind::kDispatchJump &&
        site.kind != UnresolvedExitKind::kDispatchCall &&
        site.kind != UnresolvedExitKind::kUnknownContinuation) {
      continue;
    }
    FrontierWorkItem work_item = makeFrontierWorkItem(site);
    auto [it, inserted] =
        graph.edge_facts_by_identity.emplace(work_item.identity, SessionEdgeFact{});
    auto &edge = it->second;
    if (inserted) {
      edge.identity = work_item.identity;
      edge.is_dirty = true;
    } else if (edge.target_pc != work_item.target_pc ||
               edge.continuation_vip_pc != work_item.continuation_vip_pc ||
               edge.exit_disposition != work_item.exit_disposition ||
               edge.vip_pc != work_item.vip_pc ||
               edge.vip_symbolic != work_item.vip_symbolic) {
      edge.is_dirty = true;
    }
    syncEdgeFactFromFrontierWorkItem(edge, work_item);
    edge.is_dirty = edge.is_dirty || inserted ||
                    session.graph.dirty_function_names.count(edge.owner_function) !=
                        0;
    edge.from_unresolved_exit = true;
  }

  graph.boundary_facts_by_target.clear();
  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc)
      continue;
    if (edge.kind != FrontierWorkKind::kNativeCallBoundary &&
        edge.kind != FrontierWorkKind::kTerminalBoundary &&
        edge.kind != FrontierWorkKind::kVmEnterBoundary) {
      continue;
    }
    auto &boundary = graph.boundary_facts_by_target[*edge.target_pc];
    boundary.target_pc = *edge.target_pc;
    boundary.kind = edge.kind;
    boundary.exit_disposition = edge.exit_disposition;
    boundary.is_dirty = boundary.is_dirty || edge.is_dirty;
  }
}

void refreshDerivedViewsAndLoweringInputs(DevirtualizationSession &session,
                                          const llvm::Module &M) {
  auto &graph = session.graph;
  graph.root_slices_by_va.clear();
  graph.region_nodes_by_entry_pc.clear();

  for (const auto &[name, node] : graph.handler_nodes) {
    (void)name;
    if (!node.entry_va)
      continue;
    if (!node.is_output_root && !node.is_closed_root_slice_root &&
        llvm::find(session.root_slice, *node.entry_va) == session.root_slice.end()) {
      continue;
    }
    auto &slice = graph.root_slices_by_va[*node.entry_va];
    slice.root_va = *node.entry_va;
    slice.root_function = node.function_name;
    slice.is_dirty = node.is_dirty;
    slice.reachable_handler_names.clear();
    slice.frontier_edge_identities.clear();
    slice.reachable_handler_names.push_back(node.function_name);
  }

  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    auto handler_it = graph.handler_nodes.find(edge.owner_function);
    if (handler_it != graph.handler_nodes.end() && handler_it->second.entry_va) {
      auto root_it = graph.root_slices_by_va.find(*handler_it->second.entry_va);
      if (root_it != graph.root_slices_by_va.end()) {
        root_it->second.frontier_edge_identities.push_back(identity);
        if (!edge.owner_function.empty())
          root_it->second.reachable_handler_names.push_back(edge.owner_function);
      }
    }
    if (edge.kind == FrontierWorkKind::kVmEnterBoundary && edge.target_pc) {
      auto &region = graph.region_nodes_by_entry_pc[*edge.target_pc];
      region.entry_pc = *edge.target_pc;
      region.kind = SessionRegionKind::kNestedVmEnter;
      region.status = SessionRegionStatus::kPending;
      region.is_dirty = region.is_dirty || edge.is_dirty;
      region.frontier_edge_identities.push_back(identity);
      if (handler_it != graph.handler_nodes.end())
        region.parent_entry_pc = handler_it->second.entry_va;
      region.parent_target_pc = edge.target_pc;

      if (auto imported_it =
              session.imported_vm_enter_child_roots.find(*edge.target_pc);
          imported_it != session.imported_vm_enter_child_roots.end()) {
        region.status = SessionRegionStatus::kImported;
        region.imported_root_function = imported_it->second;
      } else {
        for (const auto &F : M) {
          if (!isImportedVmEnterChildFunction(F, *edge.target_pc))
            continue;
          region.status = SessionRegionStatus::kImported;
          region.imported_root_function = F.getName().str();
          break;
        }
      }
      if (region.status != SessionRegionStatus::kImported &&
          session.attempted_vm_enter_child_import_pcs.count(*edge.target_pc) != 0) {
        region.status = SessionRegionStatus::kBlocked;
        if (region.failure_reason.empty())
          region.failure_reason = "child_import_not_materialized";
      }
    }
  }

  for (auto &[target_pc, boundary] : graph.boundary_facts_by_target) {
    auto &mutable_module = const_cast<llvm::Module &>(M);
    if (auto *fn = findStructuralCodeTargetFunctionByPC(mutable_module, target_pc))
      boundary.declaration_name = fn->getName().str();
    else if (auto *fn = findLiftedOrBlockFunctionByPC(mutable_module, target_pc))
      boundary.declaration_name = fn->getName().str();
  }

  for (auto &[root_va, slice] : graph.root_slices_by_va) {
    (void)root_va;
    std::sort(slice.reachable_handler_names.begin(),
              slice.reachable_handler_names.end());
    slice.reachable_handler_names.erase(
        std::unique(slice.reachable_handler_names.begin(),
                    slice.reachable_handler_names.end()),
        slice.reachable_handler_names.end());
    slice.is_closed = llvm::all_of(
        slice.frontier_edge_identities, [&](const std::string &identity) {
          auto it = graph.edge_facts_by_identity.find(identity);
          if (it == graph.edge_facts_by_identity.end())
            return true;
          return it->second.status != FrontierWorkStatus::kPending &&
                 it->second.status != FrontierWorkStatus::kInvalidated;
        });
  }
}

void publishSessionGraphProjectionImpl(const llvm::Module &M,
                                       const SessionGraphState &state) {
  SessionGraphProjectionCacheEntry entry;
  entry.module_fingerprint = llvm::StructuralHash(M);
  entry.state = state;
  sessionGraphProjectionCache()[&M] = std::move(entry);
}

const SessionGraphState *findSessionGraphProjectionImpl(
    const llvm::Module &M) {
  auto &cache = sessionGraphProjectionCache();
  auto it = cache.find(&M);
  if (it == cache.end())
    return nullptr;
  if (it->second.module_fingerprint != llvm::StructuralHash(M)) {
    cache.erase(it);
    return nullptr;
  }
  return &it->second.state;
}

void refreshSessionGraphState(DevirtualizationSession &session,
                              const llvm::Module &M) {
  collectDirtyFunctionsAndSites(session, M);
  refreshHandlerLocalFacts(session, M);
  refreshSessionEdgesAndFrontier(session);
  refreshDerivedViewsAndLoweringInputs(session, M);
  publishSessionGraphProjectionImpl(M, session.graph);
}

bool looksLikeNativeCallBoundary(uint64_t target_pc,
                                 const FrontierCallbacks &callbacks) {
  if (!callbacks.read_target_bytes)
    return false;
  uint8_t bytes[32] = {};
  if (!callbacks.read_target_bytes(target_pc, bytes, sizeof(bytes)))
    return false;
  const bool looks_like_x64_prologue =
      (bytes[0] == 0x48 && bytes[1] == 0x83 && bytes[2] == 0xEC) ||
      (bytes[0] == 0x48 && bytes[1] == 0x89 && bytes[3] == 0x24) ||
      (bytes[0] == 0x40 && bytes[1] == 0x53) ||
      (bytes[0] == 0x55 && bytes[1] == 0x48 && bytes[2] == 0x8B);
  unsigned stack_setup_ops = 0;
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
        break;
      default:
        break;
    }
  }

  bool saw_early_direct_call = false;
  for (unsigned i = 0; i + 4 < sizeof(bytes) && i < 24; ++i) {
    if (bytes[i] == 0xE8) {
      saw_early_direct_call = true;
      break;
    }
  }
  if (!saw_early_direct_call)
    return false;
  return looks_like_x64_prologue || stack_setup_ops >= 4 ||
         bytes[0] == 0xE8;
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

  if (looks_like_prologue_at(0))
    return true;

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
      looksLikeTerminalBoundarySnippet(target_pc, callbacks)) {
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
  }
  callee->addFnAttr("omill.native_boundary_pc", llvm::utohexstr(boundary_pc));
  callee->addFnAttr("omill.native_direct_target_pc", llvm::utohexstr(target_pc));
  return callee;
}

bool materializeNativeBoundaryReenterStub(llvm::Function &function,
                                          const FrontierWorkItem &item,
                                          const FrontierCallbacks &callbacks,
                                          const NativeBoundaryDecodeSummary &summary) {
  if (!item.target_pc || !summary.direct_call_target_pc ||
      !summary.continuation_pc || !summary.has_direct_call_fallthrough) {
    return false;
  }
  if (function.arg_size() < 3)
    return false;

  auto *continuation =
      findLiftedOrBlockFunctionByPC(*function.getParent(), *summary.continuation_pc);
  if (!continuation || continuation->isDeclaration())
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
  if (owner && item.target_pc) {
    for (auto &BB : *owner) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
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
                                              const FrontierCallbacks &callbacks) {
  if (!item.target_pc)
    return nullptr;
  const auto native_summary =
      decodeNativeBoundarySummary(*item.target_pc, callbacks);
  if (auto *existing = M.getFunction(liftedFunctionName(*item.target_pc))) {
    if (!materializeNativeBoundaryReenterStub(*existing, item, callbacks,
                                              native_summary) &&
        !existing->isDeclaration()) {
      existing->deleteBody();
    }
    return existing;
  }
  if (auto *existing = findLiftedOrBlockFunctionByPC(M, *item.target_pc)) {
    if (!materializeNativeBoundaryReenterStub(*existing, item, callbacks,
                                              native_summary) &&
        !existing->isDeclaration()) {
      existing->deleteBody();
    }
    return existing;
  }
  auto *fn_ty = inferFrontierFunctionType(M, item);
  if (!fn_ty)
    return nullptr;
  auto *decl = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                      liftedFunctionName(*item.target_pc), M);
  (void)materializeNativeBoundaryReenterStub(*decl, item, callbacks,
                                             native_summary);
  decl->addFnAttr("omill.native_boundary_pc", llvm::utohexstr(*item.target_pc));
  decl->addFnAttr("omill.virtual_exit_disposition",
                  item.exit_disposition ==
                          VirtualExitDisposition::kVmExitNativeCallReenter
                      ? "vm_exit_native_call_reenter"
                      : "vm_exit_native_exec_unknown_return");
  if (native_summary.direct_call_target_pc) {
    decl->addFnAttr("omill.virtual_exit_native_target_pc",
                    llvm::utohexstr(*native_summary.direct_call_target_pc));
  }
  if (item.continuation_vip_pc) {
    decl->addFnAttr("omill.virtual_exit_continuation_vip",
                    llvm::utohexstr(*item.continuation_vip_pc));
  }
  if (native_summary.continuation_pc) {
    decl->addFnAttr("omill.virtual_exit_continuation_pc",
                    llvm::utohexstr(*native_summary.continuation_pc));
  }
  if (native_summary.has_direct_call_fallthrough)
    decl->addFnAttr("omill.virtual_exit_partial", "1");
  if (item.exit_disposition == VirtualExitDisposition::kVmExitNativeCallReenter)
    decl->addFnAttr("omill.virtual_exit_reenters_vm", "1");
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
  function->addFnAttr("omill.executable_target_pc",
                      llvm::utohexstr(*item.target_pc));
  if (item.site_pc) {
    function->addFnAttr("omill.virtual_exit_site_pc",
                        llvm::utohexstr(*item.site_pc));
  }
  if (item.vip_pc) {
    function->addFnAttr("omill.virtual_exit_vip",
                        llvm::utohexstr(*item.vip_pc));
  }
  if (item.continuation_vip_pc) {
    function->addFnAttr("omill.virtual_exit_continuation_vip",
                        llvm::utohexstr(*item.continuation_vip_pc));
  }
  return function;
}

void annotateNativeBoundaryFunction(llvm::Function &function,
                                    const FrontierWorkItem &item,
                                    const FrontierCallbacks &callbacks) {
  if (!item.target_pc)
    return;
  const auto native_summary =
      decodeNativeBoundarySummary(*item.target_pc, callbacks);
  function.addFnAttr("omill.native_boundary_pc",
                     llvm::utohexstr(*item.target_pc));
  function.addFnAttr("omill.virtual_exit_disposition",
                     item.exit_disposition ==
                             VirtualExitDisposition::kVmExitNativeCallReenter
                         ? "vm_exit_native_call_reenter"
                         : "vm_exit_native_exec_unknown_return");
  if (native_summary.direct_call_target_pc) {
    function.addFnAttr("omill.virtual_exit_native_target_pc",
                       llvm::utohexstr(*native_summary.direct_call_target_pc));
  }
  if (item.continuation_vip_pc) {
    function.addFnAttr("omill.virtual_exit_continuation_vip",
                       llvm::utohexstr(*item.continuation_vip_pc));
  }
  if (native_summary.continuation_pc) {
    function.addFnAttr("omill.virtual_exit_continuation_pc",
                       llvm::utohexstr(*native_summary.continuation_pc));
  }
  if (native_summary.has_direct_call_fallthrough)
    function.addFnAttr("omill.virtual_exit_partial", "1");
  if (item.exit_disposition == VirtualExitDisposition::kVmExitNativeCallReenter)
    function.addFnAttr("omill.virtual_exit_reenters_vm", "1");
}

void annotateVmEnterBoundaryFunction(llvm::Function &function,
                                     const FrontierWorkItem &item) {
  if (!item.target_pc)
    return;
  function.addFnAttr("omill.native_boundary_pc",
                     llvm::utohexstr(*item.target_pc));
  function.addFnAttr("omill.vm_enter_target_pc",
                     llvm::utohexstr(*item.target_pc));
  function.addFnAttr(
      "omill.virtual_exit_disposition",
      item.exit_disposition == VirtualExitDisposition::kNestedVmEnter
          ? "nested_vm_enter"
          : "vm_enter");
  if (item.continuation_vip_pc) {
    function.addFnAttr("omill.virtual_exit_continuation_vip",
                       llvm::utohexstr(*item.continuation_vip_pc));
  }
}

FrontierWorkKind classifyFrontierWorkItem(const FrontierWorkItem &item,
                                          const FrontierCallbacks &callbacks) {
  if (!item.target_pc)
    return FrontierWorkKind::kUnknownExecutableTarget;
  const uint64_t target_pc = *item.target_pc;
  if (item.exit_disposition == VirtualExitDisposition::kVmEnter ||
      item.exit_disposition == VirtualExitDisposition::kNestedVmEnter) {
    return FrontierWorkKind::kVmEnterBoundary;
  }
  if (item.exit_disposition == VirtualExitDisposition::kVmExitTerminal) {
    return FrontierWorkKind::kTerminalBoundary;
  }
  if (item.exit_disposition ==
          VirtualExitDisposition::kVmExitNativeCallReenter ||
      item.exit_disposition ==
          VirtualExitDisposition::kVmExitNativeExecUnknownReturn) {
    return FrontierWorkKind::kNativeCallBoundary;
  }
  if (callbacks.is_protected_boundary &&
      callbacks.is_protected_boundary(target_pc)) {
    return FrontierWorkKind::kVmEnterBoundary;
  }
  if (callbacks.has_defined_target && callbacks.has_defined_target(target_pc))
    return FrontierWorkKind::kLiftableBlock;
  if (looksLikeVmEnterBoundary(target_pc, callbacks))
    return FrontierWorkKind::kVmEnterBoundary;
  if (!callbacks.is_executable_target ||
      !callbacks.is_executable_target(target_pc)) {
    return FrontierWorkKind::kTerminalBoundary;
  }
  if (looksLikeTerminalBoundarySnippet(target_pc, callbacks))
    return FrontierWorkKind::kTerminalBoundary;
  if (looksLikeNativeCallBoundary(target_pc, callbacks))
    return FrontierWorkKind::kNativeCallBoundary;
  if (looksLikeNativeFunctionEntry(target_pc, callbacks))
    return FrontierWorkKind::kNativeCallBoundary;
  if (looksLikeNonEntryExecutableSnippet(target_pc, callbacks))
    return FrontierWorkKind::kUnknownExecutableTarget;
  if (callbacks.can_decode_target && callbacks.can_decode_target(target_pc))
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
      edge.from_unresolved_exit = !edge.from_output_root_closure;
      edge_facts.emplace(item.identity, std::move(edge));
      if (summary)
        ++summary->discovered;
      continue;
    }
    auto &edge = existing->second;
    const bool changed = edge.target_pc != item.target_pc ||
                         edge.exit_disposition != item.exit_disposition ||
                         edge.continuation_vip_pc != item.continuation_vip_pc ||
                         edge.vip_pc != item.vip_pc ||
                         edge.vip_symbolic != item.vip_symbolic;
    if (edge.status == FrontierWorkStatus::kInvalidated || changed) {
      edge.status = FrontierWorkStatus::kPending;
      edge.failure_reason.clear();
      edge.is_dirty = true;
    }
    syncEdgeFactFromFrontierWorkItem(edge, item);
    edge.from_output_root_closure =
        edge.from_output_root_closure || item.identity.find("closure:") == 0;
    edge.from_vm_continuation =
        edge.from_vm_continuation || item.owner_function == "__frontier__";
    edge.from_unresolved_exit =
        edge.from_unresolved_exit || item.identity.find("closure:") != 0;
  }
}

void refreshFrontierCompatibilityViews(DevirtualizationSession &session) {
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
        if (auto attr_disposition = parseVirtualExitDisposition(*CB)) {
          site.exit_disposition = *attr_disposition;
        } else {
          site.exit_disposition =
              site.kind == UnresolvedExitKind::kDispatchCall
                  ? VirtualExitDisposition::kVmExitNativeCallReenter
                  : VirtualExitDisposition::kStayInVm;
        }
        site.continuation_vip_pc = parseOptionalHexAttr(
            CB->getFnAttr("omill.virtual_exit_continuation_vip"));
        if (!site.continuation_vip_pc) {
          site.continuation_vip_pc = parseOptionalHexAttr(
              CB->getFnAttr("omill.virtual_exit_continuation_pc"));
        }
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
    site.exit_disposition = item.exit_disposition;
    site.continuation_vip_pc = item.continuation_vip_pc;
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
  site.continuation_vip_pc = item.continuation_vip_pc;
  site.vip_symbolic = item.vip_symbolic;
  site.exit_disposition = item.exit_disposition;
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

DevirtualizationOrchestrator::DevirtualizationOrchestrator(
    DevirtualizationPolicy policy,
    std::shared_ptr<IterativeLiftingSession> session)
    : policy_(std::move(policy)) {
  session_.iterative_session = std::move(session);
}

DevirtualizationDetectionResult DevirtualizationOrchestrator::detect(
    const llvm::Module &M, const DevirtualizationRequest &request) const {
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
  const bool compatibility_requested =
      request.deprecated_block_lift || request.deprecated_generic_static;

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
    const llvm::Module &M, const DevirtualizationRequest &request) {
  DevirtualizationExecutionPlan plan;
  plan.detection = detect(M, request);
  plan.enable_devirtualization = plan.detection.should_devirtualize;
  plan.verify_rewrites = request.verify_rewrites;

  session_.root_slice = request.root_vas;
  session_.discovered_root_pcs = plan.detection.seed_roots;
  refreshSessionCoreState(session_, M);
  mergeFrontierItems(session_, collectFrontierWorkItems(session_.unresolved_exits));
  refreshDerivedViewsAndLoweringInputs(session_, M);
  refreshFrontierCompatibilityViews(session_);

  if (!plan.enable_devirtualization)
    return plan;

  plan.use_block_lift = policy_.force_block_lift;
  plan.use_generic_static_devirtualization = policy_.force_generic_static;
  plan.disable_legacy_vm_path = policy_.disable_legacy_vm_path;
  return plan;
}

void DevirtualizationOrchestrator::refreshSessionState(const llvm::Module &M) {
  refreshSessionCoreState(session_, M);
  mergeFrontierItems(session_, collectFrontierWorkItems(session_.unresolved_exits));
  refreshDerivedViewsAndLoweringInputs(session_, M);
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

FrontierAdvanceSummary DevirtualizationOrchestrator::discoverFrontierWork(
    const llvm::Module &M, const FrontierCallbacks &callbacks,
    FrontierDiscoveryPhase phase) {
  FrontierAdvanceSummary summary;
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
  refreshFrontierCompatibilityViews(session_);
  summary.pending =
      static_cast<unsigned>(session_.late_frontier_work_items.size());
  return summary;
}

FrontierAdvanceSummary DevirtualizationOrchestrator::advanceFrontierWork(
    llvm::Module &M, BlockLifter &block_lifter,
    IterativeLiftingSession &iterative_session,
    const FrontierCallbacks &callbacks) {
  FrontierAdvanceSummary summary;
  const bool debug_frontier =
      (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
  const bool recovery_mode = isTerminalBoundaryRecoveryModeEnabled();
  std::vector<std::string> identities;
  identities.reserve(session_.late_frontier_work_items.size());
  for (const auto &item : session_.late_frontier_work_items)
    identities.push_back(item.identity);

  for (const auto &identity : identities) {
    auto edge_it = session_.graph.edge_facts_by_identity.find(identity);
    if (edge_it == session_.graph.edge_facts_by_identity.end())
      continue;
    auto item = frontierWorkItemFromEdgeFact(edge_it->second);
    if (!item.target_pc)
      continue;
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
            callbacks.has_defined_target &&
            callbacks.has_defined_target(target_pc)) {
          item.status = FrontierWorkStatus::kSkippedMaterialized;
          item.failure_reason.clear();
          ++summary.skipped_materialized;
          summary.changed = true;
          linkFrontierItemToUnresolvedExit(session_, item);
          return true;
        }
        switch (item.kind) {
          case FrontierWorkKind::kTerminalBoundary:
            item.status = FrontierWorkStatus::kClassifiedTerminal;
            item.exit_disposition = VirtualExitDisposition::kVmExitTerminal;
            item.failure_reason = "non_liftable_terminal_boundary";
            ++summary.classified_terminal;
            summary.changed = true;
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          case FrontierWorkKind::kVmEnterBoundary:
            item.status = FrontierWorkStatus::kClassifiedVmEnter;
            if (item.exit_disposition == VirtualExitDisposition::kUnknown)
              item.exit_disposition = VirtualExitDisposition::kVmEnter;
            if (auto *function = getOrInsertVmEnterBoundaryFunction(M, item))
              annotateVmEnterBoundaryFunction(*function, item);
            item.failure_reason = "vm_entry_boundary";
            ++summary.classified_vm_enter;
            summary.changed = true;
            linkFrontierItemToUnresolvedExit(session_, item);
            return true;
          case FrontierWorkKind::kNativeCallBoundary:
            if (item.exit_disposition == VirtualExitDisposition::kUnknown ||
                item.exit_disposition == VirtualExitDisposition::kStayInVm) {
              item.exit_disposition =
                  item.continuation_vip_pc
                      ? VirtualExitDisposition::kVmExitNativeCallReenter
                      : VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
            }
            if (debug_frontier) {
              llvm::errs() << "[frontier-advance] native-boundary-decl id="
                           << item.identity << " target=0x"
                           << llvm::utohexstr(target_pc) << "\n";
            }
            if (auto *decl = getOrInsertNativeBoundaryDecl(M, item, callbacks)) {
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
            if (auto *function = getOrInsertExecutableTargetFunction(M, item)) {
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
        bool lift_crashed = false;
        llvm::Function *lifted = nullptr;
        __try {
          lifted = block_lifter.LiftBlock(target_pc, discovered_targets);
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
                       << " target=0x" << llvm::utohexstr(target_pc)
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
          if (debug_frontier) {
            llvm::errs() << "[frontier-advance] noted-lifted-target id="
                         << item.identity << " target=0x"
                         << llvm::utohexstr(target_pc) << "\n";
          }
          item.status = FrontierWorkStatus::kLifted;
          item.failure_reason.clear();
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

  unsigned imported = 0;
  for (const auto &[identity, edge] : session_.graph.edge_facts_by_identity) {
    (void)identity;
    if (!edge.target_pc ||
        edge.status != FrontierWorkStatus::kClassifiedVmEnter) {
      continue;
    }
    const uint64_t target_pc = *edge.target_pc;
    if (!session_.attempted_vm_enter_child_import_pcs.insert(target_pc).second)
      continue;
    if (imported >= callbacks.max_imports)
      break;
    if (auto *existing = findLiftedOrCoveredFunctionByPC(M, target_pc);
        existing && !existing->isDeclaration()) {
      continue;
    }

    auto *placeholder = findStructuralCodeTargetFunctionByPC(M, target_pc);
    if (!placeholder || !placeholder->isDeclaration() ||
        !placeholder->hasFnAttribute("omill.vm_enter_target_pc")) {
      continue;
    }

    ++summary.attempted;
    std::string failure_reason;
    llvm::Function *imported_root = nullptr;
      if (!callbacks.try_import_target(target_pc, *placeholder, failure_reason,
                                     imported_root) ||
        !imported_root) {
      if (failure_reason.empty())
        failure_reason = "child_import_failed";
      summary.notes.push_back(std::string("target=0x") +
                              llvm::utohexstr(target_pc) + ":" +
                              failure_reason);
      continue;
    }
    if (imported_root->getFunctionType() != placeholder->getFunctionType()) {
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

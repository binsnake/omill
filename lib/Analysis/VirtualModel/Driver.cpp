#include "Analysis/VirtualModel/Internal.h"

#include <llvm/Support/raw_ostream.h>

#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/StructuralHash.h>

#include <chrono>
#include <cstdlib>
#include <limits>
#include <map>
#include <set>
#include <utility>

#include "omill/Utils/LiftedNames.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Devirtualization/Orchestrator.h"

namespace omill {

namespace {

static bool vmModelImportDebugEnabled() {
  const char *v = std::getenv("OMILL_DEBUG_VIRTUAL_MODEL_IMPORT");
  return v && v[0] != '\0';
}

static bool vmModelStageDebugEnabled() {
  const char *v = std::getenv("OMILL_DEBUG_VIRTUAL_MODEL_STAGES");
  return v && v[0] != '\0';
}

static void vmModelStageDebugLogImpl(llvm::StringRef message) {
  if (!vmModelStageDebugEnabled())
    return;
  llvm::errs() << "[omill.vm-model] " << message << "\n";
}

static uint64_t elapsedMillisecondsImpl(
    std::chrono::steady_clock::time_point begin,
    std::chrono::steady_clock::time_point end) {
  return static_cast<uint64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(end - begin)
          .count());
}

static void vmModelImportDebugLogImpl(llvm::StringRef message) {
  if (!vmModelImportDebugEnabled())
    return;
  llvm::errs() << "[omill.vm-model.import] " << message << "\n";
}

static bool vmModelLocalReplayDebugEnabledImpl() {
  const char *v = std::getenv("OMILL_DEBUG_VIRTUAL_MODEL_LOCAL_REPLAY");
  return v && v[0] != '\0';
}

static void vmModelLocalReplayDebugLogImpl(llvm::StringRef message) {
  if (!vmModelLocalReplayDebugEnabledImpl())
    return;
  llvm::errs() << "[omill.vm-model.local-replay] " << message << "\n";
}

static std::optional<uint64_t> terminalBoundaryRecoveryRootVA() {
  const char *v = std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA");
  if (!v || v[0] == '\0')
    return std::nullopt;
  llvm::StringRef text(v);
  if (text.consume_front("0x") || text.consume_front("0X")) {
  }
  uint64_t value = 0;
  if (text.getAsInteger(16, value) || value == 0)
    return std::nullopt;
  return value;
}

static unsigned terminalBoundaryRecoveryMaxSeedHandlers() {
  const char *v =
      std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE");
  if (!v || v[0] == '\0')
    return 128u;
  unsigned value = 0u;
  if (llvm::StringRef(v).getAsInteger(10, value) || value == 0u)
    return 128u;
  return value;
}

static unsigned terminalBoundaryRecoveryGuaranteedCodeBearingDepth() {
  const char *v =
      std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY_GUARANTEED_CODE_DEPTH");
  if (!v || v[0] == '\0')
    return 2u;
  unsigned value = 0u;
  if (llvm::StringRef(v).getAsInteger(10, value))
    return 2u;
  return value;
}

static bool hasPreferredVirtualModelSeedAttr(const llvm::Function &F) {
  return F.hasFnAttribute("omill.output_root") ||
         F.hasFnAttribute("omill.virtual_specialized") ||
         F.hasFnAttribute("omill.closed_root_slice_root") ||
         F.hasFnAttribute("omill.vm_wrapper") ||
         F.hasFnAttribute("omill.vm_newly_lifted") ||
         F.hasFnAttribute("omill.newly_lifted") ||
         F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
         F.getFnAttribute("omill.vm_outlined_virtual_call").isValid();
}

static bool hasExplicitDirtyVirtualModelSeedAttr(const llvm::Function &F) {
  return F.hasFnAttribute("omill.vm_newly_lifted") ||
         F.hasFnAttribute("omill.newly_lifted") ||
         F.hasFnAttribute("omill.terminal_boundary_recovery_seed");
}

static llvm::stable_hash rootSliceSummaryFingerprint(
    const VirtualMachineModel &model, bool explicit_dirty_scope) {
  llvm::stable_hash hash = llvm::stable_hash_combine(
      explicit_dirty_scope ? 1u : 0u, model.boundaries().size(),
      model.handlers().size());

  for (const auto &boundary : model.boundaries()) {
    hash = llvm::stable_hash_combine(
        hash, llvm::stable_hash_name(boundary.name),
        static_cast<unsigned>(boundary.kind));
    hash = llvm::stable_hash_combine(hash, boundary.entry_va.value_or(0),
                                     boundary.target_va.value_or(0));
  }

  for (const auto &handler : model.handlers()) {
    hash = llvm::stable_hash_combine(hash,
                                     llvm::stable_hash_name(handler.function_name),
                                     handler.entry_va.value_or(0));
    hash = llvm::stable_hash_combine(
        hash, handler.is_output_root ? 1u : 0u,
        handler.is_closed_root_slice_root ? 1u : 0u,
        handler.is_specialized ? 1u : 0u);
    hash = llvm::stable_hash_combine(
        hash, handler.is_candidate ? 1u : 0u, handler.is_dirty_seed ? 1u : 0u,
        handler.dispatch_call_count);
    hash = llvm::stable_hash_combine(hash, handler.dispatch_jump_count,
                                     handler.dispatches.size(),
                                     handler.callsites.size());
    hash = llvm::stable_hash_combine(hash, handler.called_boundaries.size(),
                                     handler.direct_callees.size());
  }

  return hash;
}

static std::string projectedRootFrontierReason(
    const SessionEdgeFact &edge) {
  switch (edge.kind) {
    case FrontierWorkKind::kVmEnterBoundary:
    case FrontierWorkKind::kTerminalBoundary:
      return "boundary_target_unlifted";
    case FrontierWorkKind::kNativeCallBoundary:
      return edge.root_frontier_kind == VirtualRootFrontierKind::kCall
                 ? "call_target_unlifted"
                 : "dispatch_target_unlifted";
    case FrontierWorkKind::kLiftableBlock:
    case FrontierWorkKind::kUnknownExecutableTarget:
      return edge.root_frontier_kind == VirtualRootFrontierKind::kCall
                 ? "call_target_unlifted"
                 : "dispatch_target_unlifted";
  }
  return "dispatch_target_unlifted";
}

static void projectRootSlicesFromSessionGraph(
    const SessionGraphState &graph, VirtualMachineModel &model) {
  auto &root_slices = model.mutableRootSlices();
  root_slices.clear();

  for (const auto &[root_va, projected_slice] : graph.root_slices_by_va) {
    VirtualRootSliceSummary slice;
    slice.root_va = root_va;
    slice.reachable_handler_names = projected_slice.reachable_handler_names;
    slice.is_closed = projected_slice.is_closed;
    slice.specialization_count = 0;
    for (const auto &edge_id : projected_slice.frontier_edge_identities) {
      auto edge_it = graph.edge_facts_by_identity.find(edge_id);
      if (edge_it == graph.edge_facts_by_identity.end())
        continue;
      const auto &edge = edge_it->second;
      VirtualRootSliceSummary::FrontierEdge frontier;
      frontier.kind = edge.root_frontier_kind;
      frontier.source_handler_name = edge.owner_function;
      frontier.dispatch_index =
          edge.root_frontier_kind == VirtualRootFrontierKind::kDispatch
              ? edge.site_index
              : 0u;
      frontier.callsite_index =
          edge.root_frontier_kind == VirtualRootFrontierKind::kCall
              ? edge.site_index
              : 0u;
      frontier.reason = projectedRootFrontierReason(edge);
      frontier.target_pc = edge.target_pc;
      frontier.vip_pc = edge.vip_pc;
      frontier.exit_disposition = edge.exit_disposition;
      auto boundary_it = edge.target_pc
                             ? graph.boundary_facts_by_target.find(*edge.target_pc)
                             : graph.boundary_facts_by_target.end();
      if (boundary_it != graph.boundary_facts_by_target.end() &&
          boundary_it->second.declaration_name.has_value()) {
        frontier.boundary_name = boundary_it->second.declaration_name;
      }
      slice.frontier_edges.push_back(std::move(frontier));
    }
    root_slices.push_back(std::move(slice));
  }
}

static VirtualBoundaryKind projectedBoundaryKind(FrontierWorkKind kind) {
  switch (kind) {
    case FrontierWorkKind::kVmEnterBoundary:
      return VirtualBoundaryKind::kProtectedEntryStub;
    case FrontierWorkKind::kNativeCallBoundary:
    case FrontierWorkKind::kTerminalBoundary:
      return VirtualBoundaryKind::kProtectedBoundary;
    case FrontierWorkKind::kLiftableBlock:
    case FrontierWorkKind::kUnknownExecutableTarget:
      return VirtualBoundaryKind::kUnknown;
  }
  return VirtualBoundaryKind::kUnknown;
}

static VirtualValueExpr constantPcExpr(std::optional<uint64_t> pc) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kConstant;
  expr.bit_width = 64;
  expr.complete = pc.has_value();
  expr.constant = pc;
  return expr;
}

static void applyProjectedExitSummary(VirtualExitSummary &exit,
                                      const SessionEdgeFact &edge) {
  exit.disposition = edge.exit_disposition;
  exit.continuation_vip.resolved_pc = edge.continuation_vip_pc;
  exit.continuation_vip.symbolic =
      !edge.continuation_vip_pc.has_value() && edge.vip_symbolic;
  exit.continuation_pc = edge.continuation_vip_pc;

  switch (edge.exit_disposition) {
    case VirtualExitDisposition::kVmExitTerminal:
      exit.is_full_exit = true;
      break;
    case VirtualExitDisposition::kVmExitNativeCallReenter:
      exit.is_partial_exit = true;
      exit.reenters_vm = true;
      break;
    case VirtualExitDisposition::kVmExitNativeExecUnknownReturn:
      exit.is_partial_exit = true;
      break;
    case VirtualExitDisposition::kVmEnter:
    case VirtualExitDisposition::kNestedVmEnter:
    case VirtualExitDisposition::kStayInVm:
    case VirtualExitDisposition::kUnknown:
      break;
  }
}

static std::optional<std::string> projectedTargetNameForEdge(
    const SessionGraphState &graph, const SessionEdgeFact &edge) {
  if (!edge.target_pc)
    return std::nullopt;

  if (auto boundary_it = graph.boundary_facts_by_target.find(*edge.target_pc);
      boundary_it != graph.boundary_facts_by_target.end() &&
      boundary_it->second.declaration_name.has_value()) {
    return boundary_it->second.declaration_name;
  }

  for (const auto &[name, node] : graph.handler_nodes) {
    if (node.entry_va && *node.entry_va == *edge.target_pc)
      return name;
  }

  return std::nullopt;
}

static bool projectBoundariesFromSessionGraph(const SessionGraphState &graph,
                                              VirtualMachineModel &model) {
  bool changed = false;
  std::set<std::string> existing_names;
  for (const auto &boundary : model.boundaries())
    existing_names.insert(boundary.name);

  for (const auto &[target_pc, boundary_fact] : graph.boundary_facts_by_target) {
    if (!boundary_fact.declaration_name.has_value())
      continue;
    if (!existing_names.insert(*boundary_fact.declaration_name).second)
      continue;

    VirtualBoundaryInfo info;
    info.name = *boundary_fact.declaration_name;
    info.kind = projectedBoundaryKind(boundary_fact.kind);
    info.entry_va = target_pc;
    info.target_va = target_pc;
    model.mutableBoundaries().push_back(std::move(info));
    changed = true;
  }

  return changed;
}

static bool projectFlowFactsFromSessionGraph(const SessionGraphState &graph,
                                             VirtualMachineModel &model) {
  bool changed = false;
  std::map<std::string, VirtualHandlerSummary *> handlers_by_name;
  for (auto &handler : model.mutableHandlers()) {
    handlers_by_name.emplace(handler.function_name, &handler);
    handler.dispatch_call_count = 0;
    handler.dispatch_jump_count = 0;
    handler.protected_boundary_call_count = 0;
    handler.called_boundaries.clear();
    handler.dispatches.clear();
    handler.callsites.clear();
  }

  for (const auto &[identity, edge] : graph.edge_facts_by_identity) {
    (void)identity;
    auto handler_it = handlers_by_name.find(edge.owner_function);
    if (handler_it == handlers_by_name.end())
      continue;
    auto &handler = *handler_it->second;
    auto target_name = projectedTargetNameForEdge(graph, edge);

    if (edge.root_frontier_kind == VirtualRootFrontierKind::kDispatch) {
      VirtualDispatchSummary dispatch;
      dispatch.is_jump = true;
      dispatch.target = constantPcExpr(edge.target_pc);
      dispatch.specialized_target = dispatch.target;
      dispatch.vip.resolved_pc = edge.vip_pc;
      dispatch.vip.symbolic = !edge.vip_pc.has_value() && edge.vip_symbolic;
      dispatch.unresolved_reason = edge.failure_reason;
      applyProjectedExitSummary(dispatch.exit, edge);

      if (edge.target_pc) {
        VirtualDispatchSuccessorSummary successor;
        successor.target_pc = *edge.target_pc;
        successor.target_function_name = target_name;
        if (target_name &&
            graph.boundary_facts_by_target.find(*edge.target_pc) !=
                graph.boundary_facts_by_target.end()) {
          successor.boundary_name = target_name;
        }
        switch (edge.kind) {
          case FrontierWorkKind::kLiftableBlock:
            successor.kind = VirtualSuccessorKind::kLiftedBlock;
            break;
          case FrontierWorkKind::kVmEnterBoundary:
          case FrontierWorkKind::kNativeCallBoundary:
          case FrontierWorkKind::kTerminalBoundary:
            successor.kind = VirtualSuccessorKind::kProtectedBoundary;
            break;
          case FrontierWorkKind::kUnknownExecutableTarget:
            successor.kind = VirtualSuccessorKind::kUnknown;
            break;
        }
        dispatch.successors.push_back(std::move(successor));
      }

      if (target_name &&
          (edge.kind == FrontierWorkKind::kVmEnterBoundary ||
           edge.kind == FrontierWorkKind::kNativeCallBoundary ||
           edge.kind == FrontierWorkKind::kTerminalBoundary)) {
        handler.called_boundaries.push_back(*target_name);
        ++handler.protected_boundary_call_count;
      }

      handler.dispatches.push_back(std::move(dispatch));
      ++handler.dispatch_jump_count;
      changed = true;
      continue;
    }

    VirtualCallSiteSummary callsite;
    callsite.is_call = true;
    callsite.target = constantPcExpr(edge.target_pc);
    callsite.specialized_target = callsite.target;
    callsite.resolved_target_pc = edge.target_pc;
    callsite.recovered_entry_pc = edge.target_pc;
    callsite.continuation_pc = edge.continuation_vip_pc;
    callsite.vip.resolved_pc = edge.vip_pc;
    callsite.vip.symbolic = !edge.vip_pc.has_value() && edge.vip_symbolic;
    callsite.is_executable_in_image = edge.target_pc.has_value();
    callsite.is_decodable_entry =
        edge.kind != FrontierWorkKind::kUnknownExecutableTarget;
    callsite.target_function_name = target_name;
    callsite.recovered_target_function_name = target_name;
    callsite.unresolved_reason = edge.failure_reason;
    applyProjectedExitSummary(callsite.exit, edge);

    if (target_name &&
        (edge.kind == FrontierWorkKind::kVmEnterBoundary ||
         edge.kind == FrontierWorkKind::kNativeCallBoundary ||
         edge.kind == FrontierWorkKind::kTerminalBoundary)) {
      handler.called_boundaries.push_back(*target_name);
      ++handler.protected_boundary_call_count;
    }

    handler.callsites.push_back(std::move(callsite));
    ++handler.dispatch_call_count;
    changed = true;
  }

  for (auto &handler : model.mutableHandlers()) {
    std::sort(handler.called_boundaries.begin(), handler.called_boundaries.end());
    handler.called_boundaries.erase(
        std::unique(handler.called_boundaries.begin(),
                    handler.called_boundaries.end()),
        handler.called_boundaries.end());
  }

  return changed;
}

static bool projectRegionsFromSessionGraph(const SessionGraphState &graph,
                                           VirtualMachineModel &model) {
  if (graph.region_nodes_by_entry_pc.empty())
    return false;

  auto &regions = model.mutableRegions();
  regions.clear();
  unsigned next_id = 1;
  for (const auto &[entry_pc, region_node] : graph.region_nodes_by_entry_pc) {
    VirtualRegionSummary region;
    region.id = next_id++;
    if (region_node.imported_root_function.has_value()) {
      region.handler_names.push_back(*region_node.imported_root_function);
      region.entry_handler_names.push_back(*region_node.imported_root_function);
    }
    if (region_node.parent_entry_pc.has_value()) {
      for (const auto &[name, node] : graph.handler_nodes) {
        if (node.entry_va && *node.entry_va == *region_node.parent_entry_pc) {
          region.exit_handler_names.push_back(name);
          break;
        }
      }
    }
    for (const auto &identity : region_node.frontier_edge_identities) {
      auto edge_it = graph.edge_facts_by_identity.find(identity);
      if (edge_it == graph.edge_facts_by_identity.end())
        continue;
      const auto &edge = edge_it->second;
      if (!edge.owner_function.empty() &&
          llvm::find(region.handler_names, edge.owner_function) ==
              region.handler_names.end()) {
        region.handler_names.push_back(edge.owner_function);
      }
    }
    (void)entry_pc;
    regions.push_back(std::move(region));
  }

  return true;
}

}  // namespace

using virtual_model::detail::CachedDirectCalleeEntry;
using virtual_model::detail::CachedHandlerSummaryEntry;
using virtual_model::detail::classifyBoundaryKind;
using virtual_model::detail::collectDirectCalleesForFunction;
using virtual_model::detail::elapsedMilliseconds;
using virtual_model::detail::extractHexAttr;
using virtual_model::detail::isBoundaryFunction;
using virtual_model::detail::isVirtualModelCodeBearingFunction;
using virtual_model::detail::isVirtualModelInitialSeedFunction;
using virtual_model::detail::summaryRelevantFunctionFingerprint;
using virtual_model::detail::summarizeFunction;
using virtual_model::detail::summarizeCallSites;
using virtual_model::detail::summarizeDispatchSuccessors;
using virtual_model::detail::summarizeVirtualExits;
using virtual_model::detail::summarizeVirtualInstructionPointers;
using virtual_model::detail::summarizeRootSlices;
using virtual_model::detail::summarizeVirtualRegions;
using virtual_model::detail::virtualModelSummaryCaches;
using virtual_model::detail::vmModelStageDebugLog;
using virtual_model::detail::canonicalizeVirtualState;
using virtual_model::detail::propagateVirtualStateFacts;

namespace virtual_model::detail {

void vmModelImportDebugLog(llvm::StringRef message) {
  vmModelImportDebugLogImpl(message);
}

void vmModelStageDebugLog(llvm::StringRef message) {
  vmModelStageDebugLogImpl(message);
}

bool vmModelLocalReplayDebugEnabled() {
  return vmModelLocalReplayDebugEnabledImpl();
}

void vmModelLocalReplayDebugLog(llvm::StringRef message) {
  vmModelLocalReplayDebugLogImpl(message);
}

uint64_t elapsedMilliseconds(
    std::chrono::steady_clock::time_point begin,
    std::chrono::steady_clock::time_point end) {
  return elapsedMillisecondsImpl(begin, end);
}

std::map<const llvm::Module *, CachedModuleHandlerSummaryState> &
virtualModelSummaryCaches() {
  static auto *caches =
      new std::map<const llvm::Module *, CachedModuleHandlerSummaryState>();
  return *caches;
}

}  // namespace virtual_model::detail

llvm::AnalysisKey VirtualMachineModelAnalysis::Key;

VirtualMachineModelAnalysis::Result VirtualMachineModelAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  VirtualMachineModel model;
  vmModelStageDebugLog("run: begin");
  const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);
  vmModelStageDebugLog("run: binary-memory-ready");
  const auto run_begin = std::chrono::steady_clock::now();
  auto &module_cache = virtualModelSummaryCaches()[&M];
  const llvm::stable_hash module_fingerprint =
      llvm::StructuralHash(M, /*DetailedHash=*/true);
  if (module_cache.module_fingerprint != module_fingerprint) {
    module_cache = CachedModuleHandlerSummaryState{};
    module_cache.module_fingerprint = module_fingerprint;
  }
  const auto *session_graph = findSessionGraphProjection(M);
  auto &telemetry = model.mutableTelemetry();

  for (auto &F : M) {
    if (!isBoundaryFunction(F))
      continue;

    VirtualBoundaryInfo info;
    info.name = F.getName().str();
    info.kind = classifyBoundaryKind(F);
    uint64_t entry_va = extractEntryVA(F.getName());
    if (entry_va != 0)
      info.entry_va = entry_va;
    if (auto attr_entry = extractHexAttr(F, "omill.boundary_entry_va"))
      info.entry_va = attr_entry;
    info.target_va = extractHexAttr(F, "omill.boundary_target_va");
    model.boundaries_.push_back(std::move(info));
  }
  if (session_graph) {
    telemetry.session_graph_boundary_projection_used =
        projectBoundariesFromSessionGraph(*session_graph, model);
  }

  auto get_direct_callees = [&](llvm::Function &F)
      -> const llvm::SmallVector<std::string, 8> & {
    llvm::stable_hash fingerprint =
        llvm::StructuralHash(F, /*DetailedHash=*/true);
    std::string function_name = F.getName().str();
    auto cache_it = module_cache.direct_callees.find(function_name);
    if (cache_it != module_cache.direct_callees.end() &&
        cache_it->second.fingerprint == fingerprint) {
      return cache_it->second.callees;
    }
    auto callees = collectDirectCalleesForFunction(F);
    auto inserted = module_cache.direct_callees.insert_or_assign(
        function_name,
        CachedDirectCalleeEntry{fingerprint, std::move(callees)});
    return inserted.first->second.callees;
  };

  std::set<std::string> interesting_handlers;
  struct InterestingWorkItem {
    std::string name;
    unsigned helper_depth = 0u;
    unsigned code_bearing_depth = 0u;
  };
  std::vector<InterestingWorkItem> worklist;
  std::map<std::string, std::pair<unsigned, unsigned>> worklist_depths;
  constexpr unsigned kMaxClosedSliceHelperClosureDepth = 2;
  const auto recovery_root_va = terminalBoundaryRecoveryRootVA();
  const bool terminal_boundary_recovery_mode = recovery_root_va.has_value();
  const unsigned recovery_max_seed_handlers =
      terminal_boundary_recovery_mode
          ? terminalBoundaryRecoveryMaxSeedHandlers()
          : 0u;
  const unsigned recovery_guaranteed_code_bearing_depth =
      terminal_boundary_recovery_mode
          ? terminalBoundaryRecoveryGuaranteedCodeBearingDepth()
          : 0u;
  const unsigned max_helper_closure_depth =
      terminal_boundary_recovery_mode ? 1u : kMaxClosedSliceHelperClosureDepth;
  const unsigned max_code_bearing_depth =
      terminal_boundary_recovery_mode
          ? std::max(1u, recovery_guaranteed_code_bearing_depth)
          : std::numeric_limits<unsigned>::max();
  auto is_guaranteed_recovery_seed = [&](unsigned helper_depth,
                                         unsigned code_bearing_depth) {
    if (!terminal_boundary_recovery_mode)
      return false;
    if (code_bearing_depth > recovery_guaranteed_code_bearing_depth)
      return false;
    return helper_depth <= max_helper_closure_depth;
  };
  auto enqueue_interesting = [&](llvm::StringRef name, unsigned helper_depth,
                                 unsigned code_bearing_depth) {
    std::string key = name.str();
    auto [it, inserted_depth] =
        worklist_depths.emplace(key,
                                std::make_pair(helper_depth, code_bearing_depth));
    if (!inserted_depth) {
      auto &existing = it->second;
      if (helper_depth >= existing.first &&
          code_bearing_depth >= existing.second) {
        return;
      }
      existing.first = std::min(existing.first, helper_depth);
      existing.second = std::min(existing.second, code_bearing_depth);
    }
    if (terminal_boundary_recovery_mode &&
        !is_guaranteed_recovery_seed(helper_depth, code_bearing_depth) &&
        !interesting_handlers.count(key) &&
        interesting_handlers.size() >= recovery_max_seed_handlers) {
      vmModelStageDebugLog(
          (llvm::Twine("run: recovery-seed-cap-reached skip=") + key).str());
      return;
    }
    bool inserted_handler = interesting_handlers.insert(key).second;
    if (!inserted_handler && !inserted_depth)
      worklist.push_back(
          InterestingWorkItem{std::move(key), helper_depth, code_bearing_depth});
    else if (inserted_handler)
      worklist.push_back(
          InterestingWorkItem{std::move(key), helper_depth, code_bearing_depth});
  };
  const bool closed_slice_scope = isClosedRootSliceScopedModule(M);
  bool explicit_dirty_scope = false;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (hasExplicitDirtyVirtualModelSeedAttr(F)) {
      explicit_dirty_scope = true;
      break;
    }
  }
  telemetry.dirty_scope_requested = explicit_dirty_scope;
  if (explicit_dirty_scope)
    telemetry.scope_reason = "explicit_dirty_seed_attr";
  bool session_graph_handler_scope_used = false;
  if (session_graph) {
    if (explicit_dirty_scope && !session_graph->dirty_function_names.empty()) {
      for (const auto &dirty_name : session_graph->dirty_function_names) {
        auto *dirty_fn = M.getFunction(dirty_name);
        if (!dirty_fn || dirty_fn->isDeclaration())
          continue;
        enqueue_interesting(dirty_fn->getName(), /*helper_depth=*/0,
                            /*code_bearing_depth=*/0);
      }
    }
    session_graph_handler_scope_used = !interesting_handlers.empty();
    if (session_graph_handler_scope_used) {
      telemetry.session_graph_handler_scope_used = true;
      if (!telemetry.scope_reason.empty())
        telemetry.scope_reason += "+";
      telemetry.scope_reason += "session_graph";
      vmModelStageDebugLog("run: session-graph-handler-scope count=" +
                           llvm::Twine(interesting_handlers.size()).str());
    }
  }
  if (recovery_root_va && !session_graph_handler_scope_used) {
    std::string root_name = liftedFunctionName(*recovery_root_va);
    if (auto *root = M.getFunction(root_name);
        root && !root->isDeclaration()) {
      enqueue_interesting(root->getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
      vmModelStageDebugLog(
          (llvm::Twine("run: recovery-root-seed ") + root->getName()).str());
    } else {
      std::string block_name =
          (llvm::Twine("blk_") + llvm::Twine::utohexstr(*recovery_root_va))
              .str();
      if (auto *root = M.getFunction(block_name);
          root && !root->isDeclaration()) {
        enqueue_interesting(root->getName(), /*helper_depth=*/0,
                            /*code_bearing_depth=*/0);
        vmModelStageDebugLog(
            (llvm::Twine("run: recovery-root-seed ") + root->getName()).str());
      }
    }
    for (auto &F : M) {
      if (F.isDeclaration() ||
          !F.hasFnAttribute("omill.terminal_boundary_recovery_seed")) {
        continue;
      }
      enqueue_interesting(F.getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
      vmModelStageDebugLog(
          (llvm::Twine("run: recovery-extra-seed ") + F.getName()).str());
    }
  }
  if (closed_slice_scope && !session_graph_handler_scope_used) {
    for (auto &F : M) {
      if (F.isDeclaration() || !isClosedRootSliceFunction(F) ||
          !isVirtualModelCodeBearingFunction(F)) {
        continue;
      }
      if (explicit_dirty_scope && !F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice_root") &&
          !F.hasFnAttribute("omill.virtual_specialized") &&
          !hasExplicitDirtyVirtualModelSeedAttr(F)) {
        continue;
      }
      enqueue_interesting(F.getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
    }
  }
  if (interesting_handlers.empty() && !session_graph_handler_scope_used) {
    for (auto &F : M) {
      if (F.isDeclaration() ||
          F.hasFnAttribute("omill.localized_continuation_shim") ||
          !hasPreferredVirtualModelSeedAttr(F)) {
        continue;
      }
      if (explicit_dirty_scope && !F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice_root") &&
          !hasExplicitDirtyVirtualModelSeedAttr(F)) {
        continue;
      }
      enqueue_interesting(F.getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
    }
  }
  if (interesting_handlers.empty() && !explicit_dirty_scope &&
      !session_graph_handler_scope_used) {
    for (auto &F : M) {
      if (!isVirtualModelInitialSeedFunction(F))
        continue;
      enqueue_interesting(F.getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
    }
  } else if (interesting_handlers.empty() && explicit_dirty_scope &&
             !session_graph_handler_scope_used) {
    vmModelStageDebugLog(
        "run: initial-seed fallback skipped due to explicit dirty scope");
  }

  if (!explicit_dirty_scope) {
    for (const auto &boundary : model.boundaries_) {
      if (!boundary.target_va.has_value())
        continue;

      if (auto *target = M.getFunction(liftedFunctionName(*boundary.target_va));
          target && !target->isDeclaration()) {
        enqueue_interesting(target->getName(), /*helper_depth=*/0,
                            /*code_bearing_depth=*/0);
        continue;
      }

      std::string block_name =
          (llvm::Twine("blk_") + llvm::Twine::utohexstr(*boundary.target_va))
              .str();
      if (auto *target = M.getFunction(block_name);
          target && !target->isDeclaration()) {
        enqueue_interesting(target->getName(), /*helper_depth=*/0,
                            /*code_bearing_depth=*/0);
        continue;
      }

      std::string trace_block_name =
          (llvm::Twine("block_") + llvm::Twine::utohexstr(*boundary.target_va))
              .str();
      if (auto *target = M.getFunction(trace_block_name);
          target && !target->isDeclaration()) {
        enqueue_interesting(target->getName(), /*helper_depth=*/0,
                            /*code_bearing_depth=*/0);
      }
    }
  } else {
    vmModelStageDebugLog("run: boundary-target-seeding skipped due to explicit "
                         "dirty scope");
  }

  telemetry.seed_handler_count =
      static_cast<unsigned>(interesting_handlers.size());
  vmModelStageDebugLog("run: seed-scope handlers=" +
                       llvm::Twine(telemetry.seed_handler_count).str() +
                       " dirty_scope=" +
                       (explicit_dirty_scope ? std::string("true")
                                             : std::string("false")));

  while (!worklist.empty()) {
    auto [current, helper_depth, code_bearing_depth] = worklist.back();
    worklist.pop_back();
    auto *current_fn = M.getFunction(current);
    if (!current_fn || current_fn->isDeclaration())
      continue;
    for (const auto &callee_name : get_direct_callees(*current_fn)) {
      auto *callee = M.getFunction(callee_name);
      const bool callee_code_bearing =
          callee && isVirtualModelCodeBearingFunction(*callee);
      const bool callee_vm_helper =
          callee && callee->hasFnAttribute("omill.vm_handler");
      if (!callee_code_bearing && !callee_vm_helper &&
          !(callee && virtual_model::detail::isCallSiteHelper(*callee))) {
        continue;
      }
      unsigned next_helper_depth =
          callee_code_bearing ? 0u : helper_depth + 1u;
      unsigned next_code_bearing_depth =
          callee_code_bearing ? code_bearing_depth + 1u : code_bearing_depth;
      if ((closed_slice_scope || terminal_boundary_recovery_mode) &&
          !callee_code_bearing && next_helper_depth > max_helper_closure_depth) {
        continue;
      }
      if (terminal_boundary_recovery_mode &&
          next_code_bearing_depth > max_code_bearing_depth) {
        continue;
      }
      enqueue_interesting(callee_name, next_helper_depth,
                          next_code_bearing_depth);
    }
  }

  vmModelStageDebugLog("run: summarize-handlers-begin");
  const auto summarize_begin = std::chrono::steady_clock::now();
  auto &summary_cache = module_cache;
  std::set<std::string> live_summary_names;
  unsigned summarized_handlers = 0;
  unsigned cached_summary_hits = 0;
  unsigned cached_summary_misses = 0;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (F.hasFnAttribute("omill.localized_continuation_shim"))
      continue;
    if (!interesting_handlers.empty() &&
        !interesting_handlers.count(F.getName().str())) {
      continue;
    }
    if ((summarized_handlers % 64u) == 0u) {
      vmModelStageDebugLog(
          (llvm::Twine("run: summarizing ") + F.getName()).str());
    }
    std::string function_name = F.getName().str();
    live_summary_names.insert(function_name);
    llvm::stable_hash fingerprint = summaryRelevantFunctionFingerprint(F);
    auto cache_it = summary_cache.summaries.find(function_name);
    if (cache_it != summary_cache.summaries.end() &&
        cache_it->second.fingerprint == fingerprint) {
      model.handlers_.push_back(cache_it->second.summary);
      ++cached_summary_hits;
    } else {
      auto summary = summarizeFunction(F);
      summary_cache.summaries[function_name] =
          CachedHandlerSummaryEntry{fingerprint, summary};
      model.handlers_.push_back(std::move(summary));
      ++cached_summary_misses;
    }
    ++summarized_handlers;
  }
  for (auto it = summary_cache.summaries.begin();
       it != summary_cache.summaries.end();) {
    if (live_summary_names.count(it->first) != 0)
      ++it;
    else
      it = summary_cache.summaries.erase(it);
  }
  for (auto it = summary_cache.propagation_entries.begin();
       it != summary_cache.propagation_entries.end();) {
    if (live_summary_names.count(it->first) != 0)
      ++it;
    else
      it = summary_cache.propagation_entries.erase(it);
  }
  vmModelStageDebugLog("run: summarize-handlers-done count=" +
                       llvm::Twine(summarized_handlers).str() + " ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           summarize_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: summarize-handlers-cache hits=" +
                       llvm::Twine(cached_summary_hits).str() + " misses=" +
                       llvm::Twine(cached_summary_misses).str());
  telemetry.summarized_handlers = summarized_handlers;
  telemetry.cached_summary_hits = cached_summary_hits;
  telemetry.cached_summary_misses = cached_summary_misses;
  const bool session_graph_flow_projection_used =
      session_graph && !session_graph->edge_facts_by_identity.empty() &&
      projectFlowFactsFromSessionGraph(*session_graph, model);

  vmModelStageDebugLog("run: canonicalize-begin");
  const auto canonicalize_begin = std::chrono::steady_clock::now();
  canonicalizeVirtualState(model);
  vmModelStageDebugLog("run: canonicalize-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           canonicalize_begin,
                           std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: propagate-begin");
  const auto propagate_begin = std::chrono::steady_clock::now();
  propagateVirtualStateFacts(M, model, binary_memory, &module_cache);
  vmModelStageDebugLog("run: propagate-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           propagate_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: regions-begin");
  const auto regions_begin = std::chrono::steady_clock::now();
  const bool session_graph_region_projection_used =
      session_graph && projectRegionsFromSessionGraph(*session_graph, model);
  if (!session_graph_region_projection_used) {
    summarizeVirtualRegions(model, binary_memory);
  } else {
    vmModelStageDebugLog("run: regions-session-graph projection");
  }
  vmModelStageDebugLog("run: regions-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           regions_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: vip-begin");
  const auto vip_begin = std::chrono::steady_clock::now();
  summarizeVirtualInstructionPointers(M, model, binary_memory);
  vmModelStageDebugLog("run: vip-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           vip_begin, std::chrono::steady_clock::now()))
                           .str());
  telemetry.dispatch_handler_count = static_cast<unsigned>(llvm::count_if(
      model.handlers(), [](const VirtualHandlerSummary &summary) {
        return !summary.dispatches.empty();
      }));
  vmModelStageDebugLog("run: dispatch-begin");
  const auto dispatch_begin = std::chrono::steady_clock::now();
  if (!session_graph_flow_projection_used) {
    summarizeDispatchSuccessors(M, model, binary_memory);
  } else {
    vmModelStageDebugLog("run: dispatch-session-graph projection");
  }
  vmModelStageDebugLog("run: dispatch-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           dispatch_begin, std::chrono::steady_clock::now()))
                           .str());
  telemetry.callsite_handler_count = static_cast<unsigned>(llvm::count_if(
      model.handlers(), [](const VirtualHandlerSummary &summary) {
        return !summary.callsites.empty();
      }));
  vmModelStageDebugLog("run: callsites-begin");
  const auto callsites_begin = std::chrono::steady_clock::now();
  if (!session_graph_flow_projection_used) {
    summarizeCallSites(M, model, binary_memory);
  } else {
    vmModelStageDebugLog("run: callsites-session-graph projection");
  }
  vmModelStageDebugLog("run: callsites-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           callsites_begin, std::chrono::steady_clock::now()))
                           .str());
  telemetry.exit_handler_count = static_cast<unsigned>(llvm::count_if(
      model.handlers(), [](const VirtualHandlerSummary &summary) {
        return !summary.dispatches.empty() || !summary.callsites.empty();
      }));
  vmModelStageDebugLog("run: exits-begin");
  const auto exits_begin = std::chrono::steady_clock::now();
  if (!session_graph_flow_projection_used) {
    const auto &trace_map = MAM.getResult<VMTraceMapAnalysis>(M);
    summarizeVirtualExits(M, model, binary_memory,
                          trace_map.empty() ? nullptr : &trace_map);
  } else {
    vmModelStageDebugLog("run: exits-session-graph projection");
  }
  vmModelStageDebugLog("run: exits-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           exits_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: root-slices-begin");
  const auto root_slices_begin = std::chrono::steady_clock::now();
  if (const auto *session_graph = findSessionGraphProjection(M);
      session_graph && !session_graph->root_slices_by_va.empty()) {
    projectRootSlicesFromSessionGraph(*session_graph, model);
    telemetry.session_graph_projection_used = true;
    telemetry.root_slice_cache_hits = 0u;
    telemetry.root_slice_cache_misses = 0u;
    vmModelStageDebugLog("run: root-slices-session-graph projection");
  } else {
    llvm::stable_hash root_slice_fingerprint =
        rootSliceSummaryFingerprint(model, explicit_dirty_scope);
    if (module_cache.root_slices.fingerprint == root_slice_fingerprint) {
      model.mutableRootSlices() = module_cache.root_slices.root_slices;
      telemetry.root_slice_cache_hits = 1u;
      telemetry.root_slice_cache_misses = 0u;
      vmModelStageDebugLog("run: root-slices-cache hit");
    } else {
      summarizeRootSlices(M, model, binary_memory);
      module_cache.root_slices.fingerprint = root_slice_fingerprint;
      module_cache.root_slices.root_slices = model.rootSlices();
      telemetry.root_slice_cache_hits = 0u;
      telemetry.root_slice_cache_misses = 1u;
      vmModelStageDebugLog("run: root-slices-cache miss");
    }
  }
  vmModelStageDebugLog("run: root-slices-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           root_slices_begin,
                           std::chrono::steady_clock::now()))
                           .str());
  telemetry.root_slice_count =
      static_cast<unsigned>(model.rootSlices().size());
  vmModelStageDebugLog("run: scope-summary handlers=" +
                       llvm::Twine(telemetry.summarized_handlers).str() +
                       " dispatch_handlers=" +
                       llvm::Twine(telemetry.dispatch_handler_count).str() +
                       " callsite_handlers=" +
                       llvm::Twine(telemetry.callsite_handler_count).str() +
                       " exit_handlers=" +
                       llvm::Twine(telemetry.exit_handler_count).str() +
                       " root_slices=" +
                       llvm::Twine(telemetry.root_slice_count).str());
  vmModelStageDebugLog("run: done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           run_begin, std::chrono::steady_clock::now()))
                           .str());

  return model;
}

}  // namespace omill

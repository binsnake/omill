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
  if (recovery_root_va) {
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
  if (closed_slice_scope) {
    for (auto &F : M) {
      if (F.isDeclaration() || !isClosedRootSliceFunction(F) ||
          !isVirtualModelCodeBearingFunction(F)) {
        continue;
      }
      enqueue_interesting(F.getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
    }
  }
  if (interesting_handlers.empty()) {
    for (auto &F : M) {
      if (!isVirtualModelInitialSeedFunction(F))
        continue;
      enqueue_interesting(F.getName(), /*helper_depth=*/0,
                          /*code_bearing_depth=*/0);
    }
  }

  while (!worklist.empty()) {
    auto [current, helper_depth, code_bearing_depth] = worklist.back();
    worklist.pop_back();
    auto *current_fn = M.getFunction(current);
    if (!current_fn || current_fn->isDeclaration())
      continue;
    for (const auto &callee_name : get_direct_callees(*current_fn)) {
      auto *callee = M.getFunction(callee_name);
      bool callee_code_bearing =
          callee && isVirtualModelCodeBearingFunction(*callee);
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
  summarizeVirtualRegions(model, binary_memory);
  vmModelStageDebugLog("run: regions-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           regions_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: dispatch-begin");
  const auto dispatch_begin = std::chrono::steady_clock::now();
  summarizeDispatchSuccessors(M, model, binary_memory);
  vmModelStageDebugLog("run: dispatch-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           dispatch_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: callsites-begin");
  const auto callsites_begin = std::chrono::steady_clock::now();
  summarizeCallSites(M, model, binary_memory);
  vmModelStageDebugLog("run: callsites-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           callsites_begin, std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: root-slices-begin");
  const auto root_slices_begin = std::chrono::steady_clock::now();
  summarizeRootSlices(M, model, binary_memory);
  vmModelStageDebugLog("run: root-slices-done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           root_slices_begin,
                           std::chrono::steady_clock::now()))
                           .str());
  vmModelStageDebugLog("run: done ms=" +
                       llvm::Twine(elapsedMilliseconds(
                           run_begin, std::chrono::steady_clock::now()))
                           .str());

  return model;
}

}  // namespace omill

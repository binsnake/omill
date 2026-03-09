#include "omill/Passes/VMDeadMergedHandlerElimination.h"

#include <cstdlib>

#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Extract handler VA from a function whose name starts with "sub_<hex>".
static std::optional<uint64_t> extractHandlerVA(llvm::StringRef name) {
  uint64_t va = extractEntryVA(name);
  if (va == 0)
    return std::nullopt;
  return va;
}

/// Check if a function is a merged (non-demerged, non-wrapper) VM handler.
static bool isMergedHandler(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (!F.hasFnAttribute("omill.vm_handler"))
    return false;
  if (F.getFnAttribute("omill.vm_demerged_clone").isValid())
    return false;
  if (F.getFnAttribute("omill.vm_outlined_virtual_call").isValid())
    return false;
  if (F.hasFnAttribute("omill.vm_wrapper"))
    return false;
  return true;
}

static bool isVerbose() {
  static bool v = (std::getenv("OMILL_VM_VERBOSE") != nullptr);
  return v;
}

}  // namespace

llvm::PreservedAnalyses VMDeadMergedHandlerEliminationPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &trace_map = MAM.getResult<VMTraceMapAnalysis>(M);
  if (trace_map.empty())
    return llvm::PreservedAnalyses::all();

  auto &virtual_callees = MAM.getResult<VirtualCalleeRegistryAnalysis>(M);

  // Phase 1: identify merged handler candidates and their coverage.
  struct HandlerInfo {
    llvm::Function *fn = nullptr;
    uint64_t handler_va = 0;
    unsigned total_hashes = 0;
    unsigned covered_hashes = 0;
    bool has_uses = false;
  };
  llvm::SmallVector<HandlerInfo, 32> candidates;

  for (auto &F : M) {
    if (!isMergedHandler(F))
      continue;

    auto va_opt = extractHandlerVA(F.getName());
    if (!va_opt)
      continue;
    uint64_t handler_va = *va_opt;

    // Get all trace records for this handler VA.
    auto trace_records = trace_map.getTraceRecords(handler_va);
    if (trace_records.empty())
      continue;  // No trace data — can't assess coverage.

    unsigned total = trace_records.size();
    unsigned covered = 0;

    for (const auto &record : trace_records) {
      uint64_t incoming_hash = record.incoming_hash;

      // Check 1: is there a demerged clone function in the module?
      std::string clone_name =
          demergedHandlerCloneName(handler_va, incoming_hash);
      if (M.getFunction(clone_name)) {
        ++covered;
        continue;
      }

      // Check 2: is there a virtual callee registry record for this trace key?
      if (virtual_callees.lookupByTraceKey(handler_va, incoming_hash)) {
        ++covered;
        continue;
      }
    }

    HandlerInfo info;
    info.fn = &F;
    info.handler_va = handler_va;
    info.total_hashes = total;
    info.covered_hashes = covered;
    info.has_uses = !F.use_empty();
    candidates.push_back(info);
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  // Phase 2: eliminate fully-covered, unused merged handlers.
  unsigned eliminated = 0;
  unsigned kept_has_uses = 0;
  unsigned kept_partial = 0;

  for (auto &info : candidates) {
    bool fully_covered = (info.covered_hashes == info.total_hashes);

    if (fully_covered && !info.has_uses) {
      if (isVerbose()) {
        llvm::errs() << "VMDeadMergedHandlerElimination: removing "
                     << info.fn->getName() << " (0x"
                     << llvm::utohexstr(info.handler_va) << ") — "
                     << info.total_hashes << "/" << info.total_hashes
                     << " hashes covered, no uses\n";
      }
      info.fn->eraseFromParent();
      ++eliminated;
    } else if (fully_covered && info.has_uses) {
      // Fully covered but still has users — can't remove yet.
      // Mark internal linkage so GlobalDCE can clean it up later
      // if the uses get eliminated by inlining.
      if (info.fn->hasExternalLinkage())
        info.fn->setLinkage(llvm::GlobalValue::InternalLinkage);
      ++kept_has_uses;
      if (isVerbose()) {
        llvm::errs() << "VMDeadMergedHandlerElimination: keeping "
                     << info.fn->getName() << " (0x"
                     << llvm::utohexstr(info.handler_va) << ") — fully covered ("
                     << info.total_hashes << " hashes) but still has "
                     << info.fn->getNumUses() << " use(s)\n";
      }
    } else {
      // Partially covered — keep as fallback.
      ++kept_partial;
      if (isVerbose()) {
        llvm::errs() << "VMDeadMergedHandlerElimination: keeping "
                     << info.fn->getName() << " (0x"
                     << llvm::utohexstr(info.handler_va) << ") — "
                     << info.covered_hashes << "/" << info.total_hashes
                     << " hashes covered (partial)\n";
      }
    }
  }

  llvm::errs() << "VMDeadMergedHandlerElimination: "
               << eliminated << " eliminated";
  if (kept_has_uses > 0)
    llvm::errs() << ", " << kept_has_uses << " kept (have uses)";
  if (kept_partial > 0)
    llvm::errs() << ", " << kept_partial << " kept (partial coverage)";
  llvm::errs() << "\n";

  if (eliminated == 0)
    return llvm::PreservedAnalyses::all();
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

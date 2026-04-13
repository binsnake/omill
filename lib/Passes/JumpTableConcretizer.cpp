#include "omill/Passes/JumpTableConcretizer.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Support/Format.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"
#include "JumpTableUtils.h"

namespace omill {

namespace {

bool debugJumpTables() {
  static const bool enabled =
      (std::getenv("OMILL_DEBUG_JUMP_TABLES") != nullptr);
  return enabled;
}

struct JumpTableCandidate {
  llvm::CallInst *dispatch_call;
  llvm::ReturnInst *ret;
  llvm::BranchInst *branch;
  llvm::LoadInst *table_load;
  jt::LinearAddress addr;
  uint64_t image_base;
  uint64_t num_entries;
};

/// Scan a function for unresolved jump-dispatch sites with jump table patterns.
llvm::SmallVector<JumpTableCandidate, 4>
findJumpTableCandidates(llvm::Function &F, const BinaryMemoryMap *map) {
  llvm::SmallVector<JumpTableCandidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isDispatchJumpName(callee->getName()))
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *target = call->getArgOperand(1);

      // Skip already-constant targets — those are handled by dispatch
      // resolution, not jump table concretization.
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      // Unwrap RVA conversion: target = add(zext/sext(load), image_base).
      auto [image_base, load_val] = jt::unwrapRVAConversion(target, &F);
      llvm::Value *dynamic_rva_base = nullptr;
      if (image_base == 0)
        jt::trySplitDynamicRVAConversion(target, dynamic_rva_base, load_val);
      if (debugJumpTables()) {
        llvm::errs() << "[jt-concretizer] inspect " << F.getName()
                     << " bb=" << BB.getName()
                     << " image_base=0x" << llvm::format_hex(image_base, 10)
                     << " dynamic_base=" << (dynamic_rva_base ? "yes" : "no")
                     << "\n";
      }

      auto *table_load = jt::extractUnderlyingLoad(load_val, &F);
      if (!table_load) {
        if (debugJumpTables())
          llvm::errs() << "[jt-concretizer] reject:no-table-load\n";
        continue;
      }

      // Decompose load pointer into base + idx * stride.
      auto addr_info =
          jt::decomposeTableAddress(table_load->getPointerOperand(), &F);
      if (!addr_info && dynamic_rva_base && map && map->imageBase() != 0) {
        addr_info = jt::decomposeTableAddressWithDynamicBase(
            table_load->getPointerOperand(), dynamic_rva_base,
            map->imageBase());
        if (addr_info && image_base == 0)
          image_base = map->imageBase();
      }
      if (!addr_info) {
        if (debugJumpTables())
          llvm::errs() << "[jt-concretizer] reject:no-addr-decompose\n";
        continue;
      }

      // Find bounds from dominating branch conditions.
      auto bound = jt::computeIndexRange(addr_info->index, call->getParent());
      if (!bound || *bound == 0 || *bound > 1024) {
        if (debugJumpTables())
          llvm::errs() << "[jt-concretizer] reject:bad-bound\n";
        continue;
      }

      // Dispatch call must be followed by either a direct ret or an
      // unconditional branch into a shared return/join block.
      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      auto *branch =
          ret ? nullptr : llvm::dyn_cast<llvm::BranchInst>(call->getNextNode());
      if (!ret) {
        if (!branch || branch->isConditional() || branch->getNumSuccessors() != 1) {
          if (debugJumpTables())
            llvm::errs() << "[jt-concretizer] reject:no-ret-or-join\n";
          continue;
        }
      }

      if (debugJumpTables()) {
        llvm::errs() << "[jt-concretizer] candidate base=0x"
                     << llvm::format_hex(addr_info->base, 10)
                     << " stride=" << addr_info->stride
                     << " bound=" << *bound
                     << " image_base=0x" << llvm::format_hex(image_base, 10)
                     << "\n";
      }

      candidates.push_back(
          {call, ret, branch, table_load, *addr_info, image_base, *bound});
    }
  }

  return candidates;
}

}  // namespace

llvm::PreservedAnalyses JumpTableConcretizerPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (debugJumpTables())
    llvm::errs() << "[jt-concretizer] run " << F.getName() << "\n";

  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());

  auto candidates = findJumpTableCandidates(F, map);
  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.addr;

    // Read the jump table entries from binary memory.
    auto raw_entries =
        jt::readTableEntries(*map, addr.base, addr.stride, cand.num_entries);
    if (!raw_entries)
      continue;

    // Apply RVA→VA conversion if the target expression included an
    // image_base addend.
    jt::applyRVAConversion(*raw_entries, cand.image_base, addr.stride);
    jt::trimTrailingInvalidEntries(*raw_entries, *map);
    if (raw_entries->empty())
      continue;

    // Validate: all entries should look like plausible code addresses.
    // If image_base is set and the map has executable regions, check that
    // each target falls within a mapped region.
    bool all_plausible = true;
    for (uint64_t entry : *raw_entries) {
      if (entry == 0) {
        all_plausible = false;
        break;
      }
      // If we have an image base, verify the entry is within the image.
      if (map->imageBase() != 0 && map->imageSize() != 0) {
        if (entry < map->imageBase() ||
            entry >= map->imageBase() + map->imageSize()) {
          all_plausible = false;
          break;
        }
      }
    }
    if (!all_plausible)
      continue;

    // Build the switch instruction.
    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.image_base, cand.dispatch_call,
        cand.ret, cand.branch, F, *map, lifted);

    if (result.changed)
      changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#include "omill/Passes/RecoverJumpTables.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PatternMatch.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

#include "JumpTableUtils.h"

namespace omill {

namespace {

struct JumpTableCandidate {
  llvm::CallInst *dispatch_call;
  llvm::ReturnInst *ret;
  llvm::LoadInst *table_load;
  jt::LinearAddress addr;
  uint64_t image_base;
  uint64_t num_entries;
};

}  // namespace

llvm::PreservedAnalyses RecoverJumpTablesPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  auto *lifted = MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  // Collect candidates.
  llvm::SmallVector<JumpTableCandidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->getName() != "__omill_dispatch_jump")
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *target = call->getArgOperand(1);

      // Skip already-constant targets (handled by ResolveDispatchTargets).
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      // Unwrap RVA conversion if present.
      auto [image_base, load_val] = jt::unwrapRVAConversion(target);

      // Strip zext/sext from load value.
      if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(load_val))
        load_val = zext->getOperand(0);
      else if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(load_val))
        load_val = sext->getOperand(0);

      auto *table_load = llvm::dyn_cast<llvm::LoadInst>(load_val);
      if (!table_load)
        continue;

      // Decompose load pointer into base + idx * stride.
      auto addr_info = jt::decomposeTableAddress(table_load->getPointerOperand());
      if (!addr_info)
        continue;

      // Find bounds.
      auto bound = jt::computeIndexRange(addr_info->index, call->getParent());
      if (!bound || *bound == 0 || *bound > 1024)
        continue;

      // Must be followed by ret.
      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      if (!ret)
        continue;

      candidates.push_back({call, ret, table_load, *addr_info,
                            image_base, *bound});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.addr;

    // Read table entries from binary memory.
    auto raw_entries = jt::readTableEntries(*map, addr.base, addr.stride,
                                            cand.num_entries);
    if (!raw_entries)
      continue;

    // Apply RVA conversion.
    jt::applyRVAConversion(*raw_entries, cand.image_base, addr.stride);

    // Build switch.
    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.image_base, cand.dispatch_call,
        cand.ret, F, *map, lifted);

    if (result.changed)
      changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

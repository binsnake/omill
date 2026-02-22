#include "omill/Passes/VMHandlerInliner.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/Cloning.h>

namespace omill {
namespace {

/// Count instructions in a function (excluding debug/lifetime intrinsics).
unsigned countMeaningfulInstructions(llvm::Function &F) {
  unsigned count = 0;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::DbgInfoIntrinsic>(&I))
        continue;
      if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(&I)) {
        if (II->isLifetimeStartOrEnd())
          continue;
      }
      ++count;
    }
  }
  return count;
}

/// Check if a function is a lifted function (has remill signature or is
/// named sub_*).
bool isLiftedFunction(const llvm::Function &F) {
  auto name = F.getName();
  return name.starts_with("sub_") || name.starts_with("__lifted_");
}

/// Collect all direct call targets from a function, counting callsites.
void collectCallTargets(
    llvm::Function &F,
    llvm::DenseMap<llvm::Function *, unsigned> &target_counts) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;

      auto *callee = CB->getCalledFunction();
      if (!callee || callee->isDeclaration())
        continue;

      // Skip intrinsics and known non-handler functions.
      if (callee->isIntrinsic())
        continue;
      auto name = callee->getName();
      if (name.starts_with("__remill_") || name.starts_with("__omill_"))
        continue;

      target_counts[callee]++;
    }
  }
}

/// Identify VM handler candidates: small functions called from multiple
/// sites within lifted functions.
llvm::SmallVector<llvm::Function *, 16> identifyHandlers(
    llvm::Module &M, unsigned max_instrs, unsigned min_callsites) {
  // Count callsites across all lifted functions.
  llvm::DenseMap<llvm::Function *, unsigned> global_callsite_counts;

  for (auto &F : M) {
    if (F.isDeclaration() || !isLiftedFunction(F))
      continue;
    collectCallTargets(F, global_callsite_counts);
  }

  // Also count from _native wrappers (post-ABI recovery).
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.getName().ends_with("_native"))
      continue;
    collectCallTargets(F, global_callsite_counts);
  }

  llvm::SmallVector<llvm::Function *, 16> handlers;
  for (auto &[func, count] : global_callsite_counts) {
    if (count < min_callsites)
      continue;

    // Skip if function is too large to be a handler.
    unsigned size = countMeaningfulInstructions(*func);
    if (size > max_instrs)
      continue;

    // Skip functions that themselves are lifted (sub_*) — those are
    // real functions, not VM handlers.
    if (isLiftedFunction(*func))
      continue;

    handlers.push_back(func);
  }

  return handlers;
}

}  // namespace

llvm::PreservedAnalyses VMHandlerInlinerPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  auto handlers =
      identifyHandlers(M, max_handler_instrs_, min_callsites_);

  if (handlers.empty())
    return llvm::PreservedAnalyses::all();

  // Mark all handler functions as alwaysinline.
  bool changed = false;
  for (auto *F : handlers) {
    if (!F->hasFnAttribute(llvm::Attribute::AlwaysInline)) {
      F->addFnAttr(llvm::Attribute::AlwaysInline);
      F->removeFnAttr(llvm::Attribute::NoInline);
      F->removeFnAttr(llvm::Attribute::OptimizeNone);
      changed = true;
    }
  }

  if (!changed)
    return llvm::PreservedAnalyses::all();

  // Inline the marked functions.
  // We perform the inlining ourselves for direct calls to avoid depending
  // on a separate AlwaysInliner pass invocation.
  llvm::SmallVector<llvm::CallBase *, 32> inline_sites;
  llvm::DenseSet<llvm::Function *> handler_set(handlers.begin(),
                                                handlers.end());

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;

    for (auto it = llvm::inst_begin(F), end = llvm::inst_end(F);
         it != end; ++it) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&*it);
      if (!CB)
        continue;

      auto *callee = CB->getCalledFunction();
      if (!callee || !handler_set.contains(callee))
        continue;

      inline_sites.push_back(CB);
    }
  }

  bool inlined = false;
  for (auto *CB : inline_sites) {
    llvm::InlineFunctionInfo IFI;
    auto result = llvm::InlineFunction(*CB, IFI);
    if (result.isSuccess())
      inlined = true;
  }

  // Clean up: remove handler functions that are now dead.
  for (auto *F : handlers) {
    if (F->use_empty() && !F->hasExternalLinkage()) {
      F->eraseFromParent();
    }
  }

  return inlined ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

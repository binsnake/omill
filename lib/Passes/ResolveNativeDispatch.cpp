#include "omill/Passes/ResolveNativeDispatch.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#define DEBUG_TYPE "resolve-native-dispatch"

namespace omill {

namespace {

/// A parsed entry from __omill_native_dispatch's switch table.
struct DispatchEntry {
  llvm::Function *target_fn;
  /// Indices into __omill_native_dispatch's parameters that are forwarded
  /// to target_fn.  E.g., {1, 2} means dispatch arg 1 (rcx) and arg 2 (rdx).
  llvm::SmallVector<unsigned, 8> arg_indices;
};

/// Parse __omill_native_dispatch's switch to build a VA → DispatchEntry map.
/// Returns false if the function doesn't have the expected structure.
static bool parseDispatchTable(
    llvm::Function *dispatch_fn,
    llvm::DenseMap<uint64_t, DispatchEntry> &table) {
  if (!dispatch_fn || dispatch_fn->isDeclaration())
    return false;

  auto &entry_bb = dispatch_fn->getEntryBlock();
  auto *sw = llvm::dyn_cast<llvm::SwitchInst>(entry_bb.getTerminator());
  if (!sw)
    return false;

  for (auto &case_it : sw->cases()) {
    uint64_t va = case_it.getCaseValue()->getZExtValue();
    auto *case_bb = case_it.getCaseSuccessor();

    // Each case block should have: call @sub_X_native(...), ret %result
    llvm::CallInst *call = nullptr;
    for (auto &I : *case_bb) {
      if (auto *ci = llvm::dyn_cast<llvm::CallInst>(&I)) {
        call = ci;
        break;
      }
    }
    if (!call || !call->getCalledFunction())
      continue;

    DispatchEntry entry;
    entry.target_fn = call->getCalledFunction();

    // Map each call argument back to a dispatch function parameter index.
    for (unsigned i = 0; i < call->arg_size(); ++i) {
      auto *arg = call->getArgOperand(i);
      bool found = false;
      for (unsigned j = 0; j < dispatch_fn->arg_size(); ++j) {
        if (arg == dispatch_fn->getArg(j)) {
          entry.arg_indices.push_back(j);
          found = true;
          break;
        }
      }
      if (!found)
        break;  // Unexpected arg source, skip this case.
    }

    if (entry.arg_indices.size() == call->arg_size()) {
      table[va] = std::move(entry);
    }
  }

  return !table.empty();
}

}  // namespace

llvm::PreservedAnalyses ResolveNativeDispatchPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto *M = F.getParent();
  auto *dispatch_fn = M->getFunction("__omill_native_dispatch");
  if (!dispatch_fn)
    return llvm::PreservedAnalyses::all();

  // Parse the dispatch table each time.  The table is small (one entry per
  // lifted function) and this pass typically runs once per pipeline.
  llvm::DenseMap<uint64_t, DispatchEntry> dispatch_table;
  if (!parseDispatchTable(dispatch_fn, dispatch_table))
    return llvm::PreservedAnalyses::all();

  bool changed = false;
  llvm::SmallVector<llvm::CallInst *, 4> to_resolve;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      if (call->getCalledFunction() != dispatch_fn)
        continue;

      auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(0));
      if (!pc_ci)
        continue;

      uint64_t va = pc_ci->getZExtValue();
      auto it = dispatch_table.find(va);
      if (it == dispatch_table.end())
        continue;

      to_resolve.push_back(call);
    }
  }

  for (auto *call : to_resolve) {
    auto *pc_ci = llvm::cast<llvm::ConstantInt>(call->getArgOperand(0));
    uint64_t va = pc_ci->getZExtValue();
    auto &entry = dispatch_table[va];

    llvm::IRBuilder<> Builder(call);

    llvm::SmallVector<llvm::Value *, 8> args;
    for (unsigned idx : entry.arg_indices) {
      args.push_back(call->getArgOperand(idx));
    }

    auto *direct_call = Builder.CreateCall(entry.target_fn, args);
    // Preserve tail call kind — if the dispatch call is in tail position,
    // the direct call should be too.
    direct_call->setTailCallKind(call->getTailCallKind());

    call->replaceAllUsesWith(direct_call);
    call->eraseFromParent();
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

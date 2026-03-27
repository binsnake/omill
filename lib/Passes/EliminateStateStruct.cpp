#include "omill/Passes/EliminateStateStruct.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

bool shouldProcessClosedRootSliceFunction(const llvm::Function &F) {
  if (!isClosedRootSliceScopedModule(*F.getParent()))
    return true;
  return isClosedRootSliceFunction(F);
}

bool shouldPreserveLiftedOutputRootBoundary(const llvm::Function &F) {
  if (!F.hasFnAttribute("omill.output_root"))
    return false;
  if (isClosedRootSliceRoot(F))
    return false;

  auto has_open_control_flow = [&]() {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          return true;

        auto name = callee->getName();
        if (name == "__omill_dispatch_call" || name == "__omill_dispatch_jump")
          return true;
        if (name.starts_with("blk_") && callee->isDeclaration())
          return true;
        if (name.starts_with("sub_") && !name.ends_with("_native") &&
            callee->isDeclaration())
          return true;
      }
    }
    return false;
  };

  if (has_open_control_flow())
    return true;

  return F.hasFnAttribute("omill.vm_wrapper") ||
         F.hasFnAttribute("omill.vm_handler") ||
         F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
         F.getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
         F.getFnAttribute("omill.trace_native_target").isValid();
}

bool shouldInternalizeLiftedHelperWithoutWrapper(const llvm::Function &F) {
  if (!isLiftedFunction(F))
    return false;
  if (F.hasFnAttribute("omill.output_root"))
    return false;
  return true;
}

/// For functions that have been fully recovered (have a _native wrapper),
/// internalize the original lifted function so it can be inlined and DCE'd.
void internalizeRecoveredFunctions(llvm::Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    std::string native_name = F.getName().str() + "_native";
    const bool has_native_wrapper = M.getFunction(native_name) != nullptr;
    const bool internalize_dead_lifted_helper =
        !has_native_wrapper && shouldInternalizeLiftedHelperWithoutWrapper(F);
    if (!internalize_dead_lifted_helper &&
        !shouldProcessClosedRootSliceFunction(F))
      continue;

    if (has_native_wrapper || internalize_dead_lifted_helper) {
      F.setLinkage(llvm::GlobalValue::InternalLinkage);
      if (!has_native_wrapper)
        continue;

      if (shouldPreserveLiftedOutputRootBoundary(F)) {
        // Keep VM-oriented output roots as a boundary when they are still not
        // on a closed recovered slice. Plain lifted roots should inline into
        // the native wrapper so ABI cleanup can collapse ordinary block-lifted
        // helper graphs too.
        F.removeFnAttr(llvm::Attribute::AlwaysInline);
        F.addFnAttr(llvm::Attribute::NoInline);
      } else {
        // optnone requires noinline and is incompatible with alwaysinline.
        // Block-lifted helper functions and closed recovered roots can still
        // carry optnone here.
        if (F.hasFnAttribute(llvm::Attribute::OptimizeNone))
          F.removeFnAttr(llvm::Attribute::OptimizeNone);
        F.removeFnAttr(llvm::Attribute::NoInline);
        F.addFnAttr(llvm::Attribute::AlwaysInline);
      }
    }
  }
}

}  // namespace

llvm::PreservedAnalyses EliminateStateStructPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  bool changed = false;

  // Step 1: Internalize original lifted functions that have native wrappers.
  internalizeRecoveredFunctions(M);

  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    if (F.getName().starts_with("__remill_")) continue;
    if (F.getName().starts_with("__omill_")) continue;
    if (F.getName().ends_with("_native")) continue;
    if (!shouldProcessClosedRootSliceFunction(F))
      continue;

    if (F.arg_size() >= 1) {
      std::string native_name = F.getName().str() + "_native";
      if (M.getFunction(native_name)) {
        changed = true;
      }
    }
  }

  // Step 2: Remove unused remill intrinsic declarations.
  llvm::SmallVector<llvm::Function *, 16> to_remove;
  for (auto &F : M) {
    if (!F.isDeclaration()) continue;
    if (F.getName().starts_with("__remill_") && F.use_empty()) {
      to_remove.push_back(&F);
    }
  }
  for (auto *F : to_remove) {
    F->eraseFromParent();
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

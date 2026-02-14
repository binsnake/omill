#include "omill/Passes/EliminateStateStruct.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/CallingConventionAnalysis.h"

namespace omill {

namespace {

/// For functions that have been fully recovered (have a _native wrapper),
/// internalize the original lifted function so it can be inlined and DCE'd.
void internalizeRecoveredFunctions(llvm::Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    std::string native_name = F.getName().str() + "_native";
    if (M.getFunction(native_name)) {
      F.setLinkage(llvm::GlobalValue::InternalLinkage);
      F.addFnAttr(llvm::Attribute::AlwaysInline);
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

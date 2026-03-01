#include "omill/Passes/StripCompilerUsed.h"

#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

namespace omill {

llvm::PreservedAnalyses StripCompilerUsedPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  bool Changed = false;

  // 1. Erase @llvm.compiler.used — drops refs, lets GlobalDCE collect stubs.
  if (auto *GV = M.getGlobalVariable("llvm.compiler.used")) {
    GV->eraseFromParent();
    llvm::errs() << "[StripCompilerUsed] Removed @llvm.compiler.used\n";
    Changed = true;
  }

  // 2. Delete __remill_intrinsics (dead stub that pins ~120 declarations).
  if (auto *F = M.getFunction("__remill_intrinsics")) {
    F->eraseFromParent();
    llvm::errs() << "[StripCompilerUsed] Removed @__remill_intrinsics\n";
    Changed = true;
  }

  // 3. Delete @__remill_state (only referenced by __remill_intrinsics).
  if (auto *GV = M.getGlobalVariable("__remill_state")) {
    if (GV->use_empty()) {
      GV->eraseFromParent();
      llvm::errs() << "[StripCompilerUsed] Removed @__remill_state\n";
      Changed = true;
    }
  }

  // 4. Delete @__remill_mark_as_used (only called by __remill_intrinsics).
  if (auto *F = M.getFunction("__remill_mark_as_used")) {
    if (F->use_empty()) {
      F->eraseFromParent();
      Changed = true;
    }
  }

  return Changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

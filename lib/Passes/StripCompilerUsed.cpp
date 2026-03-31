#include "omill/Passes/StripCompilerUsed.h"

#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

namespace omill {

llvm::PreservedAnalyses StripCompilerUsedPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  bool Changed = false;

  llvm::removeFromUsedLists(M, [&](llvm::Constant *C) {
    auto *GV = llvm::dyn_cast<llvm::GlobalValue>(C);
    if (!GV)
      return false;
    const auto name = GV->getName();
    return name == "__remill_intrinsics" || name == "__remill_mark_as_used" ||
           name == "__remill_state";
  });

  // Erase both `llvm.used` and `llvm.compiler.used` so dead remill/runtime
  // scaffolding stops being pinned in final standalone outputs.
  if (auto *GV = M.getGlobalVariable("llvm.used")) {
    GV->eraseFromParent();
    Changed = true;
  }
  if (auto *GV = M.getGlobalVariable("llvm.compiler.used")) {
    GV->eraseFromParent();
    Changed = true;
  }

  // 2. Delete __remill_intrinsics (dead stub that pins ~120 declarations).
  if (auto *F = M.getFunction("__remill_intrinsics")) {
    if (F->use_empty()) {
      F->eraseFromParent();
      Changed = true;
    }
  }

  // 3. Delete @__remill_state (only referenced by __remill_intrinsics).
  if (auto *GV = M.getGlobalVariable("__remill_state")) {
    if (GV->use_empty()) {
      GV->eraseFromParent();
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

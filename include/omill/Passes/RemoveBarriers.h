#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Removes remill's volatile barrier intrinsics and inline asm barriers.
///
/// Remill inserts empty inline asm with side effects between State struct
/// fields (the "volatile separators") to prevent LLVM from coalescing
/// loads/stores across flag boundaries. It also has barrier intrinsics
/// (__remill_barrier_*) and delay slot markers.
///
/// After this pass, LLVM is free to optimize across what were field boundaries.
class RemoveBarriersPass : public llvm::PassInfoMixin<RemoveBarriersPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "RemoveBarriersPass"; }
};

}  // namespace omill

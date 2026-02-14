#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers remill atomic intrinsics to native LLVM atomic operations.
///
/// __remill_atomic_begin/end -> fence or removed
/// __remill_compare_exchange_memory_* -> cmpxchg instruction
/// __remill_fetch_and_* -> atomicrmw instruction
class LowerAtomicIntrinsicsPass
    : public llvm::PassInfoMixin<LowerAtomicIntrinsicsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerAtomicIntrinsicsPass"; }
};

}  // namespace omill

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates the Memory* pointer argument after memory intrinsics are lowered.
///
/// After LowerMemoryIntrinsics converts all __remill_read/write_memory_*
/// calls to native load/store, the Memory* pointer (3rd argument to lifted
/// functions) becomes unused. This pass replaces it with poison and cleans
/// up any remaining phi nodes that thread it.
class MemoryPointerEliminationPass
    : public llvm::PassInfoMixin<MemoryPointerEliminationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "MemoryPointerEliminationPass"; }
};

}  // namespace omill

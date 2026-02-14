#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers remill memory read/write intrinsics to native LLVM load/store.
///
/// __remill_read_memory_N(mem, addr) -> inttoptr addr, load iN
/// __remill_write_memory_N(mem, addr, val) -> inttoptr addr, store iN val
///
/// The returned Memory* from write intrinsics is replaced with the input
/// Memory*, since in the flat memory model the pointer is just a token.
/// Float variants (f32/f64/f80/f128) are handled similarly.
class LowerMemoryIntrinsicsPass
    : public llvm::PassInfoMixin<LowerMemoryIntrinsicsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerMemoryIntrinsicsPass"; }
};

}  // namespace omill

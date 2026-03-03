#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Collapses remill SHR switch-based variable shifts back to simple lshr.
///
/// Remill's SHR semantic generates a 3-way switch (shift==0, shift==1,
/// shift>=2) to handle x86 flag differences.  After SROA decomposes the
/// State struct, the result is reconstructed byte-by-byte.  When only the
/// data result is consumed (flags are dead), the entire switch + byte
/// reconstruction can be replaced with a single variable lshr, eliminating
/// up to 5 basic blocks per instance.
class CollapseRemillSHRSwitchPass
    : public llvm::PassInfoMixin<CollapseRemillSHRSwitchPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "CollapseRemillSHRSwitchPass"; }
};

}  // namespace omill

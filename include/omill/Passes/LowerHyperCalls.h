#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Lowers remill hyper call intrinsics.
///
/// __remill_sync_hyper_call(state, mem, name) for CPUID/RDTSC/etc.
///   -> platform-specific intrinsics or external function calls
///
/// __remill_async_hyper_call(state, ret_addr, mem) for syscalls/interrupts
///   -> stub calls to runtime handler
///
/// I/O port intrinsics -> inline asm or stubs
class LowerHyperCallsPass
    : public llvm::PassInfoMixin<LowerHyperCallsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerHyperCallsPass"; }
};

}  // namespace omill

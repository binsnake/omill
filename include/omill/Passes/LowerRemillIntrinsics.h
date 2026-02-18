#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

namespace LowerCategories {
enum : uint32_t {
  Flags = 1 << 0,
  Barriers = 1 << 1,
  Memory = 1 << 2,
  Atomics = 1 << 3,
  HyperCalls = 1 << 4,
  ErrorMissing = 1 << 5,
  Return = 1 << 6,
  Call = 1 << 7,
  Jump = 1 << 8,
  Undefined = 1 << 9,
  ResolvedDispatch = 1 << 10,
  // Presets
  Phase1 = Flags | Barriers | Memory | Atomics | HyperCalls,
  Phase3 = ErrorMissing | Return | Call | Jump,
  All = 0xFFFFFFFF,
};
}  // namespace LowerCategories

/// Consolidated pass that lowers remill intrinsic calls to native LLVM IR.
///
/// Categories (controlled by bitmask):
///   Flags — replace flag computation/comparison intrinsics with arg0
///   Barriers — remove volatile inline asm separators and barrier intrinsics
///   Memory — lower __remill_read/write_memory_N to load/store
///   Atomics — lower atomic operations to LLVM cmpxchg/atomicrmw
///   HyperCalls — lower sync/async hyper calls (CPUID, RDTSC, etc.)
///   ErrorMissing — lower error/missing block handlers
///   Return — lower __remill_function_return to ret
///   Call — lower __remill_function_call to direct/dispatch calls
///   Jump — lower __remill_jump to branch/tail-call/dispatch
///   Undefined — replace __remill_undefined_* with freeze(poison)
///   ResolvedDispatch — lower __omill_dispatch_call(ptrtoint(@import))
///                      to native Win64 calls
///
/// Replaces: LowerFlagIntrinsicsPass, RemoveBarriersPass,
///   LowerMemoryIntrinsicsPass, LowerAtomicIntrinsicsPass,
///   LowerHyperCallsPass, LowerErrorAndMissingPass,
///   LowerFunctionReturnPass, LowerFunctionCallPass, LowerJumpPass,
///   LowerUndefinedIntrinsicsPass, LowerResolvedDispatchCallsPass.
class LowerRemillIntrinsicsPass
    : public llvm::PassInfoMixin<LowerRemillIntrinsicsPass> {
 public:
  explicit LowerRemillIntrinsicsPass(
      uint32_t categories = LowerCategories::All)
      : categories_(categories) {}

  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "LowerRemillIntrinsicsPass"; }

 private:
  uint32_t categories_;
};

}  // namespace omill

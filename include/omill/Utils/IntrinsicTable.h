#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/StringRef.h>

namespace llvm {
class Function;
class Module;
class CallInst;
}  // namespace llvm

namespace omill {

/// Classification of remill intrinsic functions.
enum class IntrinsicKind {
  kUnknown,

  // Memory reads
  kReadMemory8,
  kReadMemory16,
  kReadMemory32,
  kReadMemory64,
  kReadMemoryF32,
  kReadMemoryF64,
  kReadMemoryF80,
  kReadMemoryF128,

  // Memory writes
  kWriteMemory8,
  kWriteMemory16,
  kWriteMemory32,
  kWriteMemory64,
  kWriteMemoryF32,
  kWriteMemoryF64,
  kWriteMemoryF80,
  kWriteMemoryF128,

  // Undefined values
  kUndefined8,
  kUndefined16,
  kUndefined32,
  kUndefined64,
  kUndefinedF32,
  kUndefinedF64,
  kUndefinedF80,
  kUndefinedF128,

  // Flag computations
  kFlagComputationZero,
  kFlagComputationSign,
  kFlagComputationOverflow,
  kFlagComputationCarry,

  // Comparisons
  kCompareSle,
  kCompareSlt,
  kCompareSge,
  kCompareSgt,
  kCompareUle,
  kCompareUlt,
  kCompareUgt,
  kCompareUge,
  kCompareEq,
  kCompareNeq,

  // Control flow
  kFunctionCall,
  kFunctionReturn,
  kJump,
  kMissingBlock,
  kError,

  // Hyper calls
  kSyncHyperCall,
  kAsyncHyperCall,

  // Barriers
  kBarrierLoadLoad,
  kBarrierLoadStore,
  kBarrierStoreLoad,
  kBarrierStoreStore,

  // Atomics
  kAtomicBegin,
  kAtomicEnd,
  kCompareExchange8,
  kCompareExchange16,
  kCompareExchange32,
  kCompareExchange64,
  kCompareExchange128,

  // Fetch-and-op (add/sub/and/or/xor/nand, 8/16/32/64)
  kFetchAndAdd8,
  kFetchAndAdd16,
  kFetchAndAdd32,
  kFetchAndAdd64,
  kFetchAndSub8,
  kFetchAndSub16,
  kFetchAndSub32,
  kFetchAndSub64,
  kFetchAndAnd8,
  kFetchAndAnd16,
  kFetchAndAnd32,
  kFetchAndAnd64,
  kFetchAndOr8,
  kFetchAndOr16,
  kFetchAndOr32,
  kFetchAndOr64,
  kFetchAndXor8,
  kFetchAndXor16,
  kFetchAndXor32,
  kFetchAndXor64,
  kFetchAndNand8,
  kFetchAndNand16,
  kFetchAndNand32,
  kFetchAndNand64,

  // Delay slots (not used for x86_64, but we handle for completeness)
  kDelaySlotBegin,
  kDelaySlotEnd,

  // FPU
  kFPUExceptionTest,
  kFPUExceptionClear,
  kFPUExceptionRaise,
  kFPUSetRounding,
  kFPUGetRounding,

  // I/O ports
  kReadIOPort8,
  kReadIOPort16,
  kReadIOPort32,
  kWriteIOPort8,
  kWriteIOPort16,
  kWriteIOPort32,

  // x86-specific segment/control register setters
  kX86SetSegment,
  kX86SetDebugReg,
  kX86SetControlReg,
};

/// Broad categories for quick filtering.
enum class IntrinsicCategory {
  kUnknown,
  kMemoryRead,
  kMemoryWrite,
  kUndefined,
  kFlag,
  kComparison,
  kControlFlow,
  kHyperCall,
  kBarrier,
  kAtomic,
  kFetchAndOp,
  kDelaySlot,
  kFPU,
  kIOPort,
  kX86Specific,
};

/// Maps a module's __remill_* functions to typed accessors.
/// Constructed once per module, then queried by passes.
class IntrinsicTable {
 public:
  explicit IntrinsicTable(llvm::Module &M);

  /// Classify a function. Returns kUnknown if not a remill intrinsic.
  IntrinsicKind classify(const llvm::Function *F) const;

  /// Get the broad category of a function.
  IntrinsicCategory category(const llvm::Function *F) const;

  /// Quick check: is this a remill intrinsic?
  bool isRemillIntrinsic(const llvm::Function *F) const;

  /// Quick check on a call instruction.
  bool isRemillIntrinsicCall(const llvm::CallInst *CI) const;
  IntrinsicKind classifyCall(const llvm::CallInst *CI) const;

  /// Get the function pointer for a specific intrinsic kind.
  /// Returns nullptr if the intrinsic doesn't exist in this module.
  llvm::Function *get(IntrinsicKind kind) const;

  /// Get the broad category for a kind.
  static IntrinsicCategory categoryOf(IntrinsicKind kind);

 private:
  void populate(llvm::Module &M);

  llvm::DenseMap<const llvm::Function *, IntrinsicKind> func_to_kind_;
  llvm::DenseMap<IntrinsicKind, llvm::Function *> kind_to_func_;
};

}  // namespace omill

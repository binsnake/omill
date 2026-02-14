#include "omill/Utils/IntrinsicTable.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

namespace omill {

namespace {

struct IntrinsicEntry {
  const char *name;
  IntrinsicKind kind;
};

// clang-format off
static const IntrinsicEntry kIntrinsicEntries[] = {
    // Memory reads
    {"__remill_read_memory_8",    IntrinsicKind::kReadMemory8},
    {"__remill_read_memory_16",   IntrinsicKind::kReadMemory16},
    {"__remill_read_memory_32",   IntrinsicKind::kReadMemory32},
    {"__remill_read_memory_64",   IntrinsicKind::kReadMemory64},
    {"__remill_read_memory_f32",  IntrinsicKind::kReadMemoryF32},
    {"__remill_read_memory_f64",  IntrinsicKind::kReadMemoryF64},
    {"__remill_read_memory_f80",  IntrinsicKind::kReadMemoryF80},
    {"__remill_read_memory_f128", IntrinsicKind::kReadMemoryF128},

    // Memory writes
    {"__remill_write_memory_8",    IntrinsicKind::kWriteMemory8},
    {"__remill_write_memory_16",   IntrinsicKind::kWriteMemory16},
    {"__remill_write_memory_32",   IntrinsicKind::kWriteMemory32},
    {"__remill_write_memory_64",   IntrinsicKind::kWriteMemory64},
    {"__remill_write_memory_f32",  IntrinsicKind::kWriteMemoryF32},
    {"__remill_write_memory_f64",  IntrinsicKind::kWriteMemoryF64},
    {"__remill_write_memory_f80",  IntrinsicKind::kWriteMemoryF80},
    {"__remill_write_memory_f128", IntrinsicKind::kWriteMemoryF128},

    // Undefined values
    {"__remill_undefined_8",    IntrinsicKind::kUndefined8},
    {"__remill_undefined_16",   IntrinsicKind::kUndefined16},
    {"__remill_undefined_32",   IntrinsicKind::kUndefined32},
    {"__remill_undefined_64",   IntrinsicKind::kUndefined64},
    {"__remill_undefined_f32",  IntrinsicKind::kUndefinedF32},
    {"__remill_undefined_f64",  IntrinsicKind::kUndefinedF64},
    {"__remill_undefined_f80",  IntrinsicKind::kUndefinedF80},
    {"__remill_undefined_f128", IntrinsicKind::kUndefinedF128},

    // Flag computations
    {"__remill_flag_computation_zero",     IntrinsicKind::kFlagComputationZero},
    {"__remill_flag_computation_sign",     IntrinsicKind::kFlagComputationSign},
    {"__remill_flag_computation_overflow", IntrinsicKind::kFlagComputationOverflow},
    {"__remill_flag_computation_carry",    IntrinsicKind::kFlagComputationCarry},

    // Comparisons
    {"__remill_compare_sle", IntrinsicKind::kCompareSle},
    {"__remill_compare_slt", IntrinsicKind::kCompareSlt},
    {"__remill_compare_sge", IntrinsicKind::kCompareSge},
    {"__remill_compare_sgt", IntrinsicKind::kCompareSgt},
    {"__remill_compare_ule", IntrinsicKind::kCompareUle},
    {"__remill_compare_ult", IntrinsicKind::kCompareUlt},
    {"__remill_compare_ugt", IntrinsicKind::kCompareUgt},
    {"__remill_compare_uge", IntrinsicKind::kCompareUge},
    {"__remill_compare_eq",  IntrinsicKind::kCompareEq},
    {"__remill_compare_neq", IntrinsicKind::kCompareNeq},

    // Control flow
    {"__remill_function_call",   IntrinsicKind::kFunctionCall},
    {"__remill_function_return", IntrinsicKind::kFunctionReturn},
    {"__remill_jump",            IntrinsicKind::kJump},
    {"__remill_missing_block",   IntrinsicKind::kMissingBlock},
    {"__remill_error",           IntrinsicKind::kError},

    // Hyper calls
    {"__remill_sync_hyper_call",  IntrinsicKind::kSyncHyperCall},
    {"__remill_async_hyper_call", IntrinsicKind::kAsyncHyperCall},

    // Barriers
    {"__remill_barrier_load_load",   IntrinsicKind::kBarrierLoadLoad},
    {"__remill_barrier_load_store",  IntrinsicKind::kBarrierLoadStore},
    {"__remill_barrier_store_load",  IntrinsicKind::kBarrierStoreLoad},
    {"__remill_barrier_store_store", IntrinsicKind::kBarrierStoreStore},

    // Atomics
    {"__remill_atomic_begin", IntrinsicKind::kAtomicBegin},
    {"__remill_atomic_end",   IntrinsicKind::kAtomicEnd},
    {"__remill_compare_exchange_memory_8",   IntrinsicKind::kCompareExchange8},
    {"__remill_compare_exchange_memory_16",  IntrinsicKind::kCompareExchange16},
    {"__remill_compare_exchange_memory_32",  IntrinsicKind::kCompareExchange32},
    {"__remill_compare_exchange_memory_64",  IntrinsicKind::kCompareExchange64},
    {"__remill_compare_exchange_memory_128", IntrinsicKind::kCompareExchange128},

    // Fetch-and-add
    {"__remill_fetch_and_add_8",  IntrinsicKind::kFetchAndAdd8},
    {"__remill_fetch_and_add_16", IntrinsicKind::kFetchAndAdd16},
    {"__remill_fetch_and_add_32", IntrinsicKind::kFetchAndAdd32},
    {"__remill_fetch_and_add_64", IntrinsicKind::kFetchAndAdd64},

    // Fetch-and-sub
    {"__remill_fetch_and_sub_8",  IntrinsicKind::kFetchAndSub8},
    {"__remill_fetch_and_sub_16", IntrinsicKind::kFetchAndSub16},
    {"__remill_fetch_and_sub_32", IntrinsicKind::kFetchAndSub32},
    {"__remill_fetch_and_sub_64", IntrinsicKind::kFetchAndSub64},

    // Fetch-and-and
    {"__remill_fetch_and_and_8",  IntrinsicKind::kFetchAndAnd8},
    {"__remill_fetch_and_and_16", IntrinsicKind::kFetchAndAnd16},
    {"__remill_fetch_and_and_32", IntrinsicKind::kFetchAndAnd32},
    {"__remill_fetch_and_and_64", IntrinsicKind::kFetchAndAnd64},

    // Fetch-and-or
    {"__remill_fetch_and_or_8",  IntrinsicKind::kFetchAndOr8},
    {"__remill_fetch_and_or_16", IntrinsicKind::kFetchAndOr16},
    {"__remill_fetch_and_or_32", IntrinsicKind::kFetchAndOr32},
    {"__remill_fetch_and_or_64", IntrinsicKind::kFetchAndOr64},

    // Fetch-and-xor
    {"__remill_fetch_and_xor_8",  IntrinsicKind::kFetchAndXor8},
    {"__remill_fetch_and_xor_16", IntrinsicKind::kFetchAndXor16},
    {"__remill_fetch_and_xor_32", IntrinsicKind::kFetchAndXor32},
    {"__remill_fetch_and_xor_64", IntrinsicKind::kFetchAndXor64},

    // Fetch-and-nand
    {"__remill_fetch_and_nand_8",  IntrinsicKind::kFetchAndNand8},
    {"__remill_fetch_and_nand_16", IntrinsicKind::kFetchAndNand16},
    {"__remill_fetch_and_nand_32", IntrinsicKind::kFetchAndNand32},
    {"__remill_fetch_and_nand_64", IntrinsicKind::kFetchAndNand64},

    // Delay slots
    {"__remill_delay_slot_begin", IntrinsicKind::kDelaySlotBegin},
    {"__remill_delay_slot_end",   IntrinsicKind::kDelaySlotEnd},

    // FPU
    {"__remill_fpu_exception_test",  IntrinsicKind::kFPUExceptionTest},
    {"__remill_fpu_exception_clear", IntrinsicKind::kFPUExceptionClear},
    {"__remill_fpu_exception_raise", IntrinsicKind::kFPUExceptionRaise},
    {"__remill_fpu_set_rounding",    IntrinsicKind::kFPUSetRounding},
    {"__remill_fpu_get_rounding",    IntrinsicKind::kFPUGetRounding},

    // I/O ports
    {"__remill_read_io_port_8",   IntrinsicKind::kReadIOPort8},
    {"__remill_read_io_port_16",  IntrinsicKind::kReadIOPort16},
    {"__remill_read_io_port_32",  IntrinsicKind::kReadIOPort32},
    {"__remill_write_io_port_8",  IntrinsicKind::kWriteIOPort8},
    {"__remill_write_io_port_16", IntrinsicKind::kWriteIOPort16},
    {"__remill_write_io_port_32", IntrinsicKind::kWriteIOPort32},
};
// clang-format on

// x86-specific intrinsic prefixes that all map to segment/debug/control set
static const IntrinsicEntry kX86SegmentEntries[] = {
    {"__remill_x86_set_segment_es",       IntrinsicKind::kX86SetSegment},
    {"__remill_x86_set_segment_ss",       IntrinsicKind::kX86SetSegment},
    {"__remill_x86_set_segment_ds",       IntrinsicKind::kX86SetSegment},
    {"__remill_x86_set_segment_fs",       IntrinsicKind::kX86SetSegment},
    {"__remill_x86_set_segment_gs",       IntrinsicKind::kX86SetSegment},
    {"__remill_x86_set_debug_reg",        IntrinsicKind::kX86SetDebugReg},
    {"__remill_amd64_set_debug_reg",      IntrinsicKind::kX86SetDebugReg},
    {"__remill_x86_set_control_reg_0",    IntrinsicKind::kX86SetControlReg},
    {"__remill_x86_set_control_reg_1",    IntrinsicKind::kX86SetControlReg},
    {"__remill_x86_set_control_reg_2",    IntrinsicKind::kX86SetControlReg},
    {"__remill_x86_set_control_reg_3",    IntrinsicKind::kX86SetControlReg},
    {"__remill_x86_set_control_reg_4",    IntrinsicKind::kX86SetControlReg},
    {"__remill_amd64_set_control_reg_0",  IntrinsicKind::kX86SetControlReg},
    {"__remill_amd64_set_control_reg_1",  IntrinsicKind::kX86SetControlReg},
    {"__remill_amd64_set_control_reg_2",  IntrinsicKind::kX86SetControlReg},
    {"__remill_amd64_set_control_reg_3",  IntrinsicKind::kX86SetControlReg},
    {"__remill_amd64_set_control_reg_4",  IntrinsicKind::kX86SetControlReg},
    {"__remill_amd64_set_control_reg_8",  IntrinsicKind::kX86SetControlReg},
};

}  // namespace

IntrinsicTable::IntrinsicTable(llvm::Module &M) { populate(M); }

void IntrinsicTable::populate(llvm::Module &M) {
  // Register standard intrinsics
  for (const auto &entry : kIntrinsicEntries) {
    if (auto *F = M.getFunction(entry.name)) {
      func_to_kind_[F] = entry.kind;
      kind_to_func_[entry.kind] = F;
    }
  }

  // Register x86-specific intrinsics
  for (const auto &entry : kX86SegmentEntries) {
    if (auto *F = M.getFunction(entry.name)) {
      func_to_kind_[F] = entry.kind;
      // Don't overwrite kind_to_func_ — these many-to-one mappings
      // mean we can't reverse-lookup a unique function from a kind.
    }
  }
}

IntrinsicKind IntrinsicTable::classify(const llvm::Function *F) const {
  auto it = func_to_kind_.find(F);
  if (it != func_to_kind_.end()) {
    return it->second;
  }
  return IntrinsicKind::kUnknown;
}

IntrinsicCategory IntrinsicTable::category(const llvm::Function *F) const {
  return categoryOf(classify(F));
}

bool IntrinsicTable::isRemillIntrinsic(const llvm::Function *F) const {
  return func_to_kind_.count(F) != 0;
}

bool IntrinsicTable::isRemillIntrinsicCall(const llvm::CallInst *CI) const {
  if (auto *F = CI->getCalledFunction()) {
    return isRemillIntrinsic(F);
  }
  return false;
}

IntrinsicKind IntrinsicTable::classifyCall(const llvm::CallInst *CI) const {
  if (auto *F = CI->getCalledFunction()) {
    return classify(F);
  }
  return IntrinsicKind::kUnknown;
}

llvm::Function *IntrinsicTable::get(IntrinsicKind kind) const {
  auto it = kind_to_func_.find(kind);
  if (it != kind_to_func_.end()) {
    return it->second;
  }
  return nullptr;
}

IntrinsicCategory IntrinsicTable::categoryOf(IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kUnknown:
      return IntrinsicCategory::kUnknown;

    case IntrinsicKind::kReadMemory8:
    case IntrinsicKind::kReadMemory16:
    case IntrinsicKind::kReadMemory32:
    case IntrinsicKind::kReadMemory64:
    case IntrinsicKind::kReadMemoryF32:
    case IntrinsicKind::kReadMemoryF64:
    case IntrinsicKind::kReadMemoryF80:
    case IntrinsicKind::kReadMemoryF128:
      return IntrinsicCategory::kMemoryRead;

    case IntrinsicKind::kWriteMemory8:
    case IntrinsicKind::kWriteMemory16:
    case IntrinsicKind::kWriteMemory32:
    case IntrinsicKind::kWriteMemory64:
    case IntrinsicKind::kWriteMemoryF32:
    case IntrinsicKind::kWriteMemoryF64:
    case IntrinsicKind::kWriteMemoryF80:
    case IntrinsicKind::kWriteMemoryF128:
      return IntrinsicCategory::kMemoryWrite;

    case IntrinsicKind::kUndefined8:
    case IntrinsicKind::kUndefined16:
    case IntrinsicKind::kUndefined32:
    case IntrinsicKind::kUndefined64:
    case IntrinsicKind::kUndefinedF32:
    case IntrinsicKind::kUndefinedF64:
    case IntrinsicKind::kUndefinedF80:
    case IntrinsicKind::kUndefinedF128:
      return IntrinsicCategory::kUndefined;

    case IntrinsicKind::kFlagComputationZero:
    case IntrinsicKind::kFlagComputationSign:
    case IntrinsicKind::kFlagComputationOverflow:
    case IntrinsicKind::kFlagComputationCarry:
      return IntrinsicCategory::kFlag;

    case IntrinsicKind::kCompareSle:
    case IntrinsicKind::kCompareSlt:
    case IntrinsicKind::kCompareSge:
    case IntrinsicKind::kCompareSgt:
    case IntrinsicKind::kCompareUle:
    case IntrinsicKind::kCompareUlt:
    case IntrinsicKind::kCompareUgt:
    case IntrinsicKind::kCompareUge:
    case IntrinsicKind::kCompareEq:
    case IntrinsicKind::kCompareNeq:
      return IntrinsicCategory::kComparison;

    case IntrinsicKind::kFunctionCall:
    case IntrinsicKind::kFunctionReturn:
    case IntrinsicKind::kJump:
    case IntrinsicKind::kMissingBlock:
    case IntrinsicKind::kError:
      return IntrinsicCategory::kControlFlow;

    case IntrinsicKind::kSyncHyperCall:
    case IntrinsicKind::kAsyncHyperCall:
      return IntrinsicCategory::kHyperCall;

    case IntrinsicKind::kBarrierLoadLoad:
    case IntrinsicKind::kBarrierLoadStore:
    case IntrinsicKind::kBarrierStoreLoad:
    case IntrinsicKind::kBarrierStoreStore:
      return IntrinsicCategory::kBarrier;

    case IntrinsicKind::kAtomicBegin:
    case IntrinsicKind::kAtomicEnd:
    case IntrinsicKind::kCompareExchange8:
    case IntrinsicKind::kCompareExchange16:
    case IntrinsicKind::kCompareExchange32:
    case IntrinsicKind::kCompareExchange64:
    case IntrinsicKind::kCompareExchange128:
      return IntrinsicCategory::kAtomic;

    case IntrinsicKind::kFetchAndAdd8:
    case IntrinsicKind::kFetchAndAdd16:
    case IntrinsicKind::kFetchAndAdd32:
    case IntrinsicKind::kFetchAndAdd64:
    case IntrinsicKind::kFetchAndSub8:
    case IntrinsicKind::kFetchAndSub16:
    case IntrinsicKind::kFetchAndSub32:
    case IntrinsicKind::kFetchAndSub64:
    case IntrinsicKind::kFetchAndAnd8:
    case IntrinsicKind::kFetchAndAnd16:
    case IntrinsicKind::kFetchAndAnd32:
    case IntrinsicKind::kFetchAndAnd64:
    case IntrinsicKind::kFetchAndOr8:
    case IntrinsicKind::kFetchAndOr16:
    case IntrinsicKind::kFetchAndOr32:
    case IntrinsicKind::kFetchAndOr64:
    case IntrinsicKind::kFetchAndXor8:
    case IntrinsicKind::kFetchAndXor16:
    case IntrinsicKind::kFetchAndXor32:
    case IntrinsicKind::kFetchAndXor64:
    case IntrinsicKind::kFetchAndNand8:
    case IntrinsicKind::kFetchAndNand16:
    case IntrinsicKind::kFetchAndNand32:
    case IntrinsicKind::kFetchAndNand64:
      return IntrinsicCategory::kFetchAndOp;

    case IntrinsicKind::kDelaySlotBegin:
    case IntrinsicKind::kDelaySlotEnd:
      return IntrinsicCategory::kDelaySlot;

    case IntrinsicKind::kFPUExceptionTest:
    case IntrinsicKind::kFPUExceptionClear:
    case IntrinsicKind::kFPUExceptionRaise:
    case IntrinsicKind::kFPUSetRounding:
    case IntrinsicKind::kFPUGetRounding:
      return IntrinsicCategory::kFPU;

    case IntrinsicKind::kReadIOPort8:
    case IntrinsicKind::kReadIOPort16:
    case IntrinsicKind::kReadIOPort32:
    case IntrinsicKind::kWriteIOPort8:
    case IntrinsicKind::kWriteIOPort16:
    case IntrinsicKind::kWriteIOPort32:
      return IntrinsicCategory::kIOPort;

    case IntrinsicKind::kX86SetSegment:
    case IntrinsicKind::kX86SetDebugReg:
    case IntrinsicKind::kX86SetControlReg:
      return IntrinsicCategory::kX86Specific;
  }
  return IntrinsicCategory::kUnknown;
}

}  // namespace omill

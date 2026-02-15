#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recovers switch statements from dispatch_jump + computed table load patterns.
///
/// Pattern matched (after InstCombine/GVN):
///   %cmp = icmp ult i64 %idx, N
///   br i1 %cmp, label %switch_bb, label %default_bb
///   switch_bb:
///     %offset = shl i64 %idx, 2         ; or 3 for 8-byte entries
///     %addr = add i64 %offset, <table_base>
///     %ptr = inttoptr i64 %addr to ptr
///     %entry = load i32, ptr %ptr        ; or i64
///     %target = add i64 %entry, <image_base>  ; for RVA tables
///     call @__omill_dispatch_jump(ptr %state, i64 %target, ptr %mem)
///
/// Reads table entries from BinaryMemoryMap, resolves to block_<hex> or sub_<hex>,
/// and emits an LLVM switch instruction.
class RecoverJumpTablesPass
    : public llvm::PassInfoMixin<RecoverJumpTablesPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "RecoverJumpTablesPass"; }
};

}  // namespace omill

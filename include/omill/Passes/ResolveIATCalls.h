#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves __omill_dispatch_call invocations whose target address comes
/// from an IAT (Import Address Table) slot via RIP-relative addressing.
///
/// Pattern matched:
///   %addr = add i64 %program_counter, <const_offset>
///   %ptr  = inttoptr i64 %addr to ptr
///   %tgt  = load i64, ptr %ptr
///   call @__omill_dispatch_call(%state, %tgt, %mem)
///
/// The pass computes the actual IAT VA (function_entry_va + offset),
/// looks it up in the BinaryMemoryMap's import table, and replaces
/// the target with ptrtoint(@resolved_import).  LowerResolvedDispatchCalls
/// then handles the native ABI lowering.
class ResolveIATCallsPass
    : public llvm::PassInfoMixin<ResolveIATCallsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveIATCallsPass"; }
};

}  // namespace omill

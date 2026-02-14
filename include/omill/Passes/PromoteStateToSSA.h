#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Promotes State struct field accesses from GEP+load/store to SSA values.
///
/// This is the core optimization pass. After intrinsic lowering and barrier
/// removal, the lifted IR contains patterns like:
///
///   %ptr = getelementptr %State, %state_ptr, 0, <field_indices>
///   store <val>, ptr %ptr
///   ...
///   %ptr2 = getelementptr %State, %state_ptr, 0, <field_indices>
///   %val2 = load ptr %ptr2
///
/// This pass:
/// 1. Creates an alloca for each accessed State field
/// 2. Loads live-in fields from State at function entry
/// 3. Replaces all GEP+load/store with alloca access
/// 4. Stores live-out fields back to State before returns
/// 5. Lets LLVM's SROA/mem2reg promote allocas to SSA
class PromoteStateToSSAPass
    : public llvm::PassInfoMixin<PromoteStateToSSAPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "PromoteStateToSSAPass"; }
};

}  // namespace omill

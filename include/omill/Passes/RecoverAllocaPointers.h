#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Recover GEP-based alloca accesses from inttoptr(ptrtoint(alloca+C1)+C2)
/// patterns.  The lifted code emits ptrtoint of stack allocas (the R12 / VM
/// context pointer), does integer arithmetic, then inttoptr to read fields.
/// LLVM's BasicAA cannot see through the inttoptr barrier, so GVN cannot
/// forward stores.  This pass resolves the integer expression back to a GEP,
/// enabling standard alias analysis and store-to-load forwarding.
struct RecoverAllocaPointersPass
    : llvm::PassInfoMixin<RecoverAllocaPointersPass> {
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &FAM);
};

}  // namespace omill

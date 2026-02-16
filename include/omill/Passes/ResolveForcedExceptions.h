#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Resolves forced exception sites (ud2, int3) to their SEH handlers.
///
/// For each __remill_error call with a constant PC, looks up the .pdata
/// RUNTIME_FUNCTION to find the exception handler. If the handler is a
/// lifted function, replaces the error intrinsic with a CONTEXT bridge:
///
///   1. Allocate CONTEXT (1232 bytes) and EXCEPTION_RECORD (152 bytes)
///   2. Marshal State registers into CONTEXT
///   3. Store handler args (EXCEPTION_RECORD*, 0, CONTEXT*, 0) into State
///   4. Call the lifted handler
///   5. Unmarshal CONTEXT back into State
///   6. Load new RIP from CONTEXT and dispatch via __omill_dispatch_jump
///
/// Runs in Phase 3 before LowerErrorAndMissingPass. Unresolved error
/// sites (no handler or handler not lifted) are left for LowerErrorAndMissing.
class ResolveForcedExceptionsPass
    : public llvm::PassInfoMixin<ResolveForcedExceptionsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "ResolveForcedExceptionsPass"; }
};

}  // namespace omill

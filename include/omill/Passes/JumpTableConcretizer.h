#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Function pass that proactively scans unresolved dispatch-jump call sites
/// for jump table patterns and replaces them with switch instructions.
///
/// For each dispatch_jump(state, target_expr, mem), the pass:
///   1. Checks if target_expr is a load from a table address
///      (base + index * stride) using jt::decomposeTableAddress.
///   2. Computes the index range from dominating branch conditions
///      using jt::computeIndexRange.
///   3. Reads the table entries from BinaryMemoryMap.
///   4. Applies RVA→VA conversion if image_base != 0.
///   5. Builds a switch instruction mapping each index to the
///      corresponding target (intra-function BB or inter-function tail call).
///
/// This pass runs AFTER optimization has simplified the dispatch target
/// expression but BEFORE final control flow lowering.  It converts
/// indirect jumps that ResolveAndLowerControlFlow would miss because
/// the target isn't a simple constant.
class JumpTableConcretizerPass
    : public llvm::PassInfoMixin<JumpTableConcretizerPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "JumpTableConcretizerPass"; }
};

}  // namespace omill

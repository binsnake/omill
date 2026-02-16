#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Simplifies vector flag computation chains by collapsing
/// sext <N x i1> → extractelement → and/shift → bit masking patterns
/// into direct extractelement <N x i1> + zext.
///
/// After vector comparisons (e.g., PCMPEQB), the result is <N x i1>.
/// Remill's flag computation sext-extends to <N x i8>, then extracts
/// individual bytes and masks bits.  Since sext <N x i1> produces
/// all-zeros or all-ones, `and i8 %sext_byte, 1` is just
/// `zext i1 (extractelement <N x i1>, idx) to i8`.
///
/// Before:
///   %sext = sext <16 x i1> %cmp to <16 x i8>
///   %byte = extractelement <16 x i8> %sext, i64 5
///   %bit  = and i8 %byte, 1
///
/// After:
///   %flag = extractelement <16 x i1> %cmp, i64 5
///   %bit  = zext i1 %flag to i8
class SimplifyVectorFlagComputationPass
    : public llvm::PassInfoMixin<SimplifyVectorFlagComputationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "SimplifyVectorFlagComputationPass"; }
};

}  // namespace omill

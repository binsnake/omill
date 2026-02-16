#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Redirects extractelement from shufflevector blend masks to the actual
/// source operand.
///
/// When the lower half of an XMM register is written, the IR represents
/// this as a shufflevector blend taking lower bytes from a new value and
/// upper bytes from the old value.  Extracts from lanes that map back to
/// the old value can be redirected directly, potentially enabling the
/// shufflevector to be DCE'd.
///
/// Before:
///   %blended = shufflevector <16 x i8> %new_lo, <16 x i8> %old,
///     <i32 0, i32 1, ..., i32 7, i32 24, i32 25, ..., i32 31>
///   %byte = extractelement <16 x i8> %blended, i64 10
///
/// After:
///   %byte = extractelement <16 x i8> %old, i64 10
class CollapsePartialXMMWritesPass
    : public llvm::PassInfoMixin<CollapsePartialXMMWritesPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "CollapsePartialXMMWritesPass"; }
};

}  // namespace omill

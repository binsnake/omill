#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Coalesces byte-level extract→zext→shift→OR chains back into a single
/// wider extractelement.
///
/// After SROA decomposes XMM-width allocas into sub-fields, mem2reg produces
/// verbose reassembly patterns where an i64 value is built from 2-8 pieces
/// extracted at different widths (i8/i16/i32) from the same 128-bit vector,
/// zero-extended, shifted, and OR'd together.  This pass recognizes those
/// OR trees and replaces them with a single wider extractelement.
///
/// Before:
///   %bc32 = bitcast <16 x i8> %src to <4 x i32>
///   %hi32 = extractelement <4 x i32> %bc32, i64 1
///   %ext32 = zext i32 %hi32 to i64
///   %shl32 = shl i64 %ext32, 32
///   ... (more pieces) ...
///   %result = or disjoint i64 %shl32, %lower_pieces
///
/// After:
///   %wide = bitcast <16 x i8> %src to <2 x i64>
///   %result = extractelement <2 x i64> %wide, i64 0
class CoalesceByteReassemblyPass
    : public llvm::PassInfoMixin<CoalesceByteReassemblyPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "CoalesceByteReassemblyPass"; }
};

}  // namespace omill

#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Consolidated pass that simplifies vector reassembly patterns produced
/// by SROA decomposition of XMM-width allocas and remill's flag computation
/// lowering.
///
/// Runs four phases in order:
///  1. FoldConstantVectorChains — fold cascaded shufflevector/insertelement
///     chains to constant vectors when all elements are ultimately constant.
///  2. CollapsePartialXMMWrites — redirect extractelement through
///     shufflevector blend masks to the actual source operand.
///  3. CoalesceByteReassembly — collapse byte-level OR trees of
///     extract+zext+shift back into a single wider extractelement.
///  4. SimplifyVectorFlagComputation — simplify sext <N x i1> chains
///     into direct extractelement + zext/sext.
class SimplifyVectorReassemblyPass
    : public llvm::PassInfoMixin<SimplifyVectorReassemblyPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "SimplifyVectorReassemblyPass"; }
};

}  // namespace omill

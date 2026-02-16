#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Folds cascaded shufflevector/insertelement chains to constant vectors
/// when all output elements ultimately come from constant sources.
///
/// LLVM's InstCombine can fold `shufflevector(C1, C2, mask)` to a constant,
/// but it cannot see through cascaded shuffles like:
///   shuffle(C1, shuffle(V, C2, m1), m2)
/// where m2 only selects constant elements (some from C1, some from C2 via
/// the inner shuffle).  This pass traces each element through the chain and
/// replaces the result with a constant vector when possible.
///
/// This is critical for deobfuscating SSE-mutation patterns where PCMPEQD
/// and MOVMSKPS operate on values that are ultimately constant but hidden
/// behind multi-level shufflevector blends from SROA.
class FoldConstantVectorChainsPass
    : public llvm::PassInfoMixin<FoldConstantVectorChainsPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                               llvm::FunctionAnalysisManager &AM);
};

}  // namespace omill

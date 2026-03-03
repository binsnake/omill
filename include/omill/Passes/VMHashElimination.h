#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Eliminates branchless hash integrity checks from VM handler functions
/// using murmur-anchored taint propagation.
///
/// EAC's VM uses murmur-style hash chains for handler integrity verification.
/// The hash result is used as a branchless multiplier (0 or 1) — when the
/// check passes, the result is 1, preserving computed values.  When it fails
/// (tampered), the result is 0, corrupting computations.
///
/// **Anchor detection**: A `mul` instruction M is a "murmur mul" if it has
/// both `lshr(M, 60)` and `lshr(M, 32)` among its users.  This pair is
/// invariant across LLVM transforms (switch expansion, PHI insertion, etc.).
///
/// **Taint propagation**: Forward BFS from murmur muls through arithmetic
/// (xor, or, and, add, sub, mul, shifts, casts, phi, select).  Stops at
/// loads, stores, calls, icmp, branches.
///
/// **Integrity check elimination**: `icmp eq i64 %tainted, <large_const>`
/// (|const| > 2^32) is replaced with `i1 true`.
///
/// **Range check elimination**: `icmp ugt i64 %X, <const>` where const >
/// 2^48, and `llvm.umax.i64(%X, <const>)` downstream `and(result, 1)` →
/// replaced with `i64 1`.
///
/// InstCombine + ADCE in the pipeline then propagate: select(true, a, b) → a,
/// mul(x, 1) → x, and remove dead hash computation chains.
class VMHashEliminationPass
    : public llvm::PassInfoMixin<VMHashEliminationPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "VMHashEliminationPass"; }
};

}  // namespace omill

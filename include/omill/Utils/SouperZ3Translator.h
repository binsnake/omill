#pragma once

#if OMILL_ENABLE_Z3

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Instructions.h>

#include <z3++.h>

namespace omill {

/// Translates LLVM IR def-use chains to Z3 bitvector expressions.
///
/// Walks backward from a given llvm::Value through its defining instructions,
/// translating each to the corresponding Z3 bitvector operation.  Values with
/// no LLVM definition (function arguments, loads, PHI nodes) become fresh Z3
/// variables that can be constrained externally (e.g. by path constraints).
///
/// DAG nodes are cached so shared subexpressions are translated only once.
class LLVMZ3Translator {
 public:
  explicit LLVMZ3Translator(z3::context &ctx);

  /// Translate an LLVM value (following def-use chain) to a Z3 bitvector
  /// expression.  The value must have an integer type.
  z3::expr translate(llvm::Value *val);

  /// Translate an icmp condition to a Z3 boolean expression.
  z3::expr translateICmp(llvm::ICmpInst *icmp);

  /// Get or create a fresh Z3 variable for a value that can't be translated
  /// (loads, arguments, etc.).
  z3::expr getFreshVar(llvm::Value *val);

  /// Clear the translation cache.
  void reset();

 private:
  z3::context &ctx_;
  llvm::DenseMap<llvm::Value *, z3::expr *> cache_;
  std::vector<std::unique_ptr<z3::expr>> owned_exprs_;
  unsigned var_counter_ = 0;

  z3::expr cacheResult(llvm::Value *val, z3::expr result);
  unsigned getWidth(llvm::Value *val) const;
};

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

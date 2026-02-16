#pragma once

#if OMILL_ENABLE_Z3

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Instructions.h>

#include <z3++.h>

namespace omill {

class BinaryMemoryMap;

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

  /// Set the binary memory map for memory-aware translation.
  /// When set, loads from computable constant addresses will be resolved
  /// to concrete values from binary memory instead of fresh variables.
  void setBinaryMemory(const BinaryMemoryMap *map) { binary_mem_ = map; }

  /// Collect all fresh Z3 variables created during translation (loads,
  /// arguments, PHIs that couldn't be resolved).  Useful for identifying
  /// the "root cause" variable in recursive solving.
  void getUnresolvedVars(
      llvm::SmallVectorImpl<std::pair<llvm::Value *, z3::expr>> &out) const;

  /// Clear the translation cache.
  void reset();

 private:
  z3::context &ctx_;
  llvm::DenseMap<llvm::Value *, z3::expr *> cache_;
  std::vector<std::unique_ptr<z3::expr>> owned_exprs_;
  unsigned var_counter_ = 0;
  const BinaryMemoryMap *binary_mem_ = nullptr;

  /// Track which LLVM Values became fresh Z3 variables.
  llvm::SmallVector<std::pair<llvm::Value *, z3::expr *>, 8> fresh_vars_;

  z3::expr cacheResult(llvm::Value *val, z3::expr result);
  unsigned getWidth(llvm::Value *val) const;

  /// Try to translate a PHI node by enumerating constant incoming values.
  /// Returns std::nullopt if any incoming value is non-constant.
  std::optional<z3::expr> tryTranslatePHI(llvm::PHINode *phi);
};

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

#pragma once

#if OMILL_ENABLE_SOUPER

#include <llvm/ADT/DenseMap.h>

#include <z3++.h>

namespace souper {
struct Inst;
}

namespace omill {

/// Translates Souper Inst DAGs to Z3 bitvector expressions.
///
/// Souper extracts expression trees from LLVM IR.  This class maps each
/// Souper node to a Z3 bitvector expression, preserving widths and semantics.
/// DAG nodes are cached so shared subexpressions are translated only once.
class SouperZ3Translator {
 public:
  explicit SouperZ3Translator(z3::context &ctx);

  /// Translate a Souper Inst DAG to a Z3 bitvector expression.
  z3::expr translate(souper::Inst *inst);

  /// Get or create a Z3 variable for a Souper Var node.
  z3::expr getVar(souper::Inst *var);

  /// Clear the translation cache (for reuse across different DAGs).
  void reset();

 private:
  z3::context &ctx_;
  llvm::DenseMap<souper::Inst *, z3::expr *> cache_;
  std::vector<std::unique_ptr<z3::expr>> owned_exprs_;
  unsigned var_counter_ = 0;
};

}  // namespace omill

#endif  // OMILL_ENABLE_SOUPER

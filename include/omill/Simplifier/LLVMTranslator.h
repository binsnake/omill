#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/IRBuilder.h>

#include "omill/Simplifier/EqSat.h"

namespace omill {

/// Bidirectional translator between LLVM IR expression trees and EqSat ASTs.
///
/// Converts integer arithmetic expression trees to the EqSat representation
/// for MBA simplification, then reconstructs simplified LLVM IR from the
/// result.
class LLVMTranslator {
 public:
  static constexpr unsigned kDefaultMaxDepth = 64;

  LLVMTranslator();
  ~LLVMTranslator();

  LLVMTranslator(const LLVMTranslator &) = delete;
  LLVMTranslator &operator=(const LLVMTranslator &) = delete;

  /// Translate an LLVM Value to an EqSat AST node.
  EqSatAstIdx translate(llvm::Value *V, unsigned max_depth = kDefaultMaxDepth);

  /// Reconstruct an LLVM Value from an EqSat AST node.
  llvm::Value *reconstruct(EqSatAstIdx idx, llvm::IRBuilder<> &B);

  /// Translate, simplify, and reconstruct. Returns nullptr if no improvement.
  llvm::Value *simplify(llvm::Value *V, llvm::IRBuilder<> &B,
                        unsigned max_depth = kDefaultMaxDepth);

  /// Reset all caches for reuse with a new expression tree.
  void reset();

  /// Access the underlying context (for testing).
  EqSatContext *getContext() const { return ctx_; }

 private:
  EqSatContext *ctx_;
  llvm::DenseMap<llvm::Value *, EqSatAstIdx> value_to_ast_;
  llvm::DenseMap<uint32_t, llvm::Value *> reconstruct_cache_;
  llvm::SmallVector<llvm::Value *, 32> symbols_by_id_;
  unsigned next_symbol_id_ = 0;

  EqSatAstIdx makeSymbol(llvm::Value *V);
  static uint8_t getWidth(llvm::Value *V);
};

}  // namespace omill

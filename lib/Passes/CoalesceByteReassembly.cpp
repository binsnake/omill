#include "omill/Passes/CoalesceByteReassembly.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>

#define DEBUG_TYPE "coalesce-byte-reassembly"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace omill {

namespace {

/// A single contribution to the OR tree: a range of bytes extracted from a
/// source vector.
struct ByteContribution {
  /// The root vector value (traced through bitcasts).
  Value *root_vec = nullptr;
  /// Byte offset within the root vector where this contribution starts.
  unsigned src_byte_offset = 0;
  /// Number of bytes contributed.
  unsigned num_bytes = 0;
  /// Byte offset within the result i64 where this contribution is placed.
  unsigned dst_byte_offset = 0;
};

/// Trace a vector operand through bitcasts to find the root vector.
static Value *traceVectorRoot(Value *V) {
  while (auto *BC = dyn_cast<BitCastInst>(V))
    V = BC->getOperand(0);
  return V;
}

/// Try to decompose a leaf value into a ByteContribution.
/// Matches: zext(extractelement(vec, idx)) or
///          shl(zext(extractelement(vec, idx)), shift)
/// Returns true on success.
static bool matchLeaf(Value *V, unsigned dst_byte_offset,
                       ByteContribution &contrib) {
  Value *inner = V;
  unsigned shift_bits = 0;

  // Peel off shl by constant.
  Value *shl_lhs;
  ConstantInt *shl_amt;
  if (match(V, m_Shl(m_Value(shl_lhs), m_ConstantInt(shl_amt)))) {
    shift_bits = shl_amt->getZExtValue();
    if (shift_bits % 8 != 0)
      return false;
    inner = shl_lhs;
    dst_byte_offset = shift_bits / 8;
  }

  // Peel off zext.
  Value *zext_src;
  if (match(inner, m_ZExt(m_Value(zext_src))))
    inner = zext_src;

  // Must be extractelement from a vector.
  Value *vec;
  ConstantInt *idx;
  if (!match(inner, m_ExtractElt(m_Value(vec), m_ConstantInt(idx))))
    return false;

  auto *vec_ty = dyn_cast<FixedVectorType>(vec->getType());
  if (!vec_ty)
    return false;

  unsigned elem_bits = vec_ty->getElementType()->getPrimitiveSizeInBits();
  if (elem_bits % 8 != 0)
    return false;

  unsigned elem_bytes = elem_bits / 8;
  unsigned src_byte_offset = idx->getZExtValue() * elem_bytes;

  contrib.root_vec = traceVectorRoot(vec);
  contrib.src_byte_offset = src_byte_offset;
  contrib.num_bytes = elem_bytes;
  contrib.dst_byte_offset = dst_byte_offset;
  return true;
}

/// Recursively collect byte contributions from an OR tree.
/// Returns false if the tree contains unsupported patterns.
static bool collectContributions(Value *V,
                                  SmallVectorImpl<ByteContribution> &contribs) {
  // Try matching as an OR.
  Value *lhs, *rhs;
  if (match(V, m_DisjointOr(m_Value(lhs), m_Value(rhs)))) {
    return collectContributions(lhs, contribs) &&
           collectContributions(rhs, contribs);
  }

  // Try matching as a leaf.
  ByteContribution contrib;
  if (matchLeaf(V, 0, contrib)) {
    contribs.push_back(contrib);
    return true;
  }

  return false;
}

/// Check that contributions form a contiguous, aligned range of bytes from the
/// same root vector.  Supports both full (8-byte) and partial (1/2/4-byte)
/// reassembly, including high-byte patterns where min_dst > 0 (e.g., bytes
/// 4-7 reassembled into the upper half of an i64).
///
/// \param contribs        The collected byte contributions.
/// \param max_result_bytes The maximum number of result bytes (usually 8).
/// \param out_root        [out] The root vector value.
/// \param out_base_byte   [out] The starting source byte offset.
/// \param out_num_bytes   [out] The extraction size in bytes (power of 2).
/// \param out_min_dst     [out] The minimum destination byte offset.
static bool validateContributions(
    ArrayRef<ByteContribution> contribs, unsigned max_result_bytes,
    Value *&out_root, unsigned &out_base_byte, unsigned &out_num_bytes,
    unsigned &out_min_dst) {
  if (contribs.empty())
    return false;

  // All must share the same root vector.
  Value *root = contribs[0].root_vec;
  for (auto &c : contribs) {
    if (c.root_vec != root)
      return false;
  }

  // Root must be a 128-bit vector (16 bytes).
  auto *root_ty = dyn_cast<FixedVectorType>(root->getType());
  if (!root_ty)
    return false;
  unsigned root_bits = root_ty->getPrimitiveSizeInBits();
  if (root_bits != 128)
    return false;

  // Determine the actual byte range covered by contributions.
  unsigned min_dst = UINT_MAX;
  unsigned max_dst = 0;
  for (auto &c : contribs) {
    if (c.dst_byte_offset < min_dst)
      min_dst = c.dst_byte_offset;
    unsigned end = c.dst_byte_offset + c.num_bytes;
    if (end > max_dst)
      max_dst = end;
  }

  // Compute the span of destination bytes actually covered.
  unsigned span = max_dst - min_dst;

  // Round up span to next power of 2 for a valid extraction element size.
  unsigned extract_bytes = 1;
  while (extract_bytes < span)
    extract_bytes *= 2;
  if (extract_bytes > max_result_bytes)
    return false;

  // Build a byte map for the [min_dst, min_dst + extract_bytes) range.
  SmallVector<int, 16> byte_map(extract_bytes, -1);

  for (auto &c : contribs) {
    for (unsigned i = 0; i < c.num_bytes; ++i) {
      unsigned dst = c.dst_byte_offset + i;
      if (dst < min_dst || dst >= min_dst + extract_bytes)
        return false;
      unsigned local = dst - min_dst;
      if (byte_map[local] != -1)
        return false;  // Overlap.
      byte_map[local] = c.src_byte_offset + i;
    }
  }

  // All bytes in the extraction range must be covered.
  for (unsigned i = 0; i < extract_bytes; ++i) {
    if (byte_map[i] == -1)
      return false;
  }

  // Bytes must be contiguous and in-order from the source.
  unsigned base = byte_map[0];
  for (unsigned i = 1; i < extract_bytes; ++i) {
    if (byte_map[i] != (int)(base + i))
      return false;
  }

  // Base must be aligned to extract_bytes for a clean extractelement.
  if (base % extract_bytes != 0)
    return false;

  out_root = root;
  out_base_byte = base;
  out_num_bytes = extract_bytes;
  out_min_dst = min_dst;
  return true;
}

static bool runOnFunction(Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end(); ) {
      auto *I = &*it++;

      // Only look at OR instructions producing i64.
      auto *BO = dyn_cast<BinaryOperator>(I);
      if (!BO || BO->getOpcode() != Instruction::Or)
        continue;
      if (!BO->getType()->isIntegerTy(64))
        continue;

      // Must be `or disjoint`.
      if (!BO->hasPoisonGeneratingFlags() ||
          !cast<PossiblyDisjointInst>(BO)->isDisjoint())
        continue;

      SmallVector<ByteContribution, 8> contribs;
      if (!collectContributions(BO, contribs))
        continue;

      Value *root_vec = nullptr;
      unsigned base_byte = 0;
      unsigned num_bytes = 0;
      unsigned min_dst = 0;
      if (!validateContributions(contribs, 8, root_vec, base_byte, num_bytes,
                                 min_dst))
        continue;

      IRBuilder<> Builder(BO);

      // Build: bitcast root to <N x iM>, extractelement, zext to i64.
      unsigned elem_bits = num_bytes * 8;
      unsigned num_elems = 128 / elem_bits;
      auto *elem_ty = IntegerType::get(F.getContext(), elem_bits);
      auto *wide_ty = FixedVectorType::get(elem_ty, num_elems);
      Value *bc = Builder.CreateBitCast(root_vec, wide_ty);
      unsigned lane = base_byte / num_bytes;
      Value *extract = Builder.CreateExtractElement(bc, lane);

      // Zero-extend to i64 if the extraction is smaller than 8 bytes.
      Value *result;
      if (num_bytes < 8) {
        result = Builder.CreateZExt(extract, BO->getType());
      } else {
        result = extract;
      }

      // If the contributions start at a non-zero destination byte, shift left
      // to position the extracted value correctly in the i64.
      if (min_dst > 0) {
        result = Builder.CreateShl(result, min_dst * 8);
      }

      BO->replaceAllUsesWith(result);
      BO->eraseFromParent();
      changed = true;
    }
  }

  return changed;
}

}  // namespace

PreservedAnalyses CoalesceByteReassemblyPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  if (!runOnFunction(F))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

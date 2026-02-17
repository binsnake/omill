#include "omill/Passes/SimplifyVectorFlagComputation.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/Debug.h>

#define DEBUG_TYPE "simplify-vector-flag-computation"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace omill {

namespace {

/// Given a value that ultimately comes from `sext <N x i1> to <N x iK>`,
/// possibly through bitcast + extractelement + lshr + trunc chains,
/// determine the original i1 lane index.
///
/// \param V       The value to trace (typically the LHS of an `and` with a
///                power-of-2 mask, or a bare lshr result).
/// \param bit_pos The bit position within the extracted element that we care
///                about (i.e. log2 of the and-mask, or the lshr shift amount).
/// \param sext_out [out] The sext instruction found.
/// \param lane_out [out] The lane index in the original <N x i1> vector.
/// \returns true if the chain was successfully traced.
static bool traceSextOrigin(Value *V, unsigned bit_pos,
                            SExtInst *&sext_out, unsigned &lane_out) {
  // Peel optional trunc.
  if (auto *trunc = dyn_cast<TruncInst>(V))
    V = trunc->getOperand(0);

  // Peel optional lshr by constant.
  unsigned lshr_amt = 0;
  Value *lshr_lhs;
  ConstantInt *lshr_ci;
  if (match(V, m_LShr(m_Value(lshr_lhs), m_ConstantInt(lshr_ci)))) {
    lshr_amt = lshr_ci->getZExtValue();
    V = lshr_lhs;
  }

  // Must be extractelement.
  auto *EE = dyn_cast<ExtractElementInst>(V);
  if (!EE)
    return false;

  auto *idx_ci = dyn_cast<ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;
  unsigned idx = idx_ci->getZExtValue();

  Value *vec = EE->getVectorOperand();
  auto *vec_ty = dyn_cast<FixedVectorType>(vec->getType());
  if (!vec_ty)
    return false;
  unsigned elem_bits = vec_ty->getElementType()->getIntegerBitWidth();

  // Peel optional bitcast on the vector operand.
  if (auto *bc = dyn_cast<BitCastInst>(vec)) {
    vec = bc->getOperand(0);
  }

  // Must be sext <N x i1> to <N x iK>.
  auto *sext = dyn_cast<SExtInst>(vec);
  if (!sext)
    return false;

  auto *src_vec_ty = dyn_cast<FixedVectorType>(sext->getOperand(0)->getType());
  if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
    return false;

  auto *dst_vec_ty = dyn_cast<FixedVectorType>(sext->getType());
  if (!dst_vec_ty)
    return false;

  unsigned lane_bits = dst_vec_ty->getElementType()->getIntegerBitWidth();
  unsigned num_lanes = src_vec_ty->getNumElements();

  // Compute the global bit position within the sext result bitvector.
  unsigned global_bit = idx * elem_bits + lshr_amt + bit_pos;

  // Determine which lane this bit falls in.
  unsigned lane = global_bit / lane_bits;
  if (lane >= num_lanes)
    return false;

  sext_out = sext;
  lane_out = lane;
  return true;
}

/// Try to simplify an `and iK %val, 2^n` where %val traces back to a
/// sext <N x i1> through bitcast/extractelement/lshr/trunc chains.
/// Replaces with: zext(extractelement(<N x i1>, lane)) << bit_pos
static bool trySimplifyAndMask(Instruction *I) {
  Value *lhs, *rhs;
  if (!match(I, m_And(m_Value(lhs), m_Value(rhs))))
    return false;

  auto *mask_ci = dyn_cast<ConstantInt>(rhs);
  if (!mask_ci)
    return false;

  APInt mask_ap = mask_ci->getValue();
  if (!mask_ap.isPowerOf2())
    return false;

  unsigned bit_pos = mask_ap.logBase2();

  SExtInst *sext = nullptr;
  unsigned lane = 0;
  if (!traceSextOrigin(lhs, bit_pos, sext, lane))
    return false;

  // Build replacement:
  //   %flag = extractelement <N x i1> %cmp, lane
  //   %zext = zext i1 %flag to iK
  //   %result = shl iK %zext, bit_pos   [if bit_pos != 0]
  IRBuilder<> Builder(I);
  Value *flag = Builder.CreateExtractElement(
      sext->getOperand(0), Builder.getInt64(lane));
  Value *zext_val = Builder.CreateZExt(flag, I->getType());

  Value *result;
  if (bit_pos == 0) {
    result = zext_val;
  } else {
    result = Builder.CreateShl(zext_val, bit_pos);
  }

  I->replaceAllUsesWith(result);
  I->eraseFromParent();
  return true;
}

/// Try to simplify a bare `lshr(extractelement(bitcast(sext <N x i1>)), K)`
/// pattern that produces a 0-or-1 value without a trailing `and`.
/// This pattern appears in `or disjoint` chains assembling a MOVMSKPS result.
///
/// We match: trunc?(lshr(extractelement(bitcast(sext <N x i1>)), K))
/// where the result is a single-bit value used in or/zext chains.
static bool trySimplifyBareLshr(Instruction *I) {
  // Match lshr or trunc(lshr(...)).
  Value *inner = I;
  bool is_trunc = false;
  if (auto *trunc = dyn_cast<TruncInst>(I)) {
    inner = trunc->getOperand(0);
    is_trunc = true;
  }

  Value *lshr_lhs;
  ConstantInt *lshr_ci;
  if (!match(inner, m_LShr(m_Value(lshr_lhs), m_ConstantInt(lshr_ci))))
    return false;

  unsigned shift_amt = lshr_ci->getZExtValue();

  // The lshr operand must be extractelement.
  auto *EE = dyn_cast<ExtractElementInst>(lshr_lhs);
  if (!EE)
    return false;

  auto *idx_ci = dyn_cast<ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;

  Value *vec = EE->getVectorOperand();

  // Peel bitcast.
  if (auto *bc = dyn_cast<BitCastInst>(vec))
    vec = bc->getOperand(0);

  auto *sext = dyn_cast<SExtInst>(vec);
  if (!sext)
    return false;

  auto *src_vec_ty = dyn_cast<FixedVectorType>(sext->getOperand(0)->getType());
  if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
    return false;

  auto *dst_vec_ty = dyn_cast<FixedVectorType>(sext->getType());
  if (!dst_vec_ty)
    return false;

  auto *ee_vec_ty = dyn_cast<FixedVectorType>(EE->getVectorOperand()->getType());
  if (!ee_vec_ty)
    return false;

  unsigned elem_bits = ee_vec_ty->getElementType()->getIntegerBitWidth();
  unsigned lane_bits = dst_vec_ty->getElementType()->getIntegerBitWidth();
  unsigned num_lanes = src_vec_ty->getNumElements();
  unsigned idx = idx_ci->getZExtValue();

  // The shift must land exactly on a lane boundary's MSB or produce a 1-bit
  // value.  For this to be a clean single-bit extraction, the shifted result
  // must be 0 or 1.  Since sext produces all-ones or all-zeros, any shift
  // that extracts a bit within a lane boundary works.
  unsigned global_bit = idx * elem_bits + shift_amt;
  unsigned lane = global_bit / lane_bits;
  if (lane >= num_lanes)
    return false;

  // Verify this produces a 0-or-1 result: the shift must move the highest
  // non-zero bit of the element to bit 0 (or extract a bit from an all-ones
  // lane that, after shifting, leaves only 1 bit set).
  // For sext all-ones, lshr by (elem_bits - 1) gives 1.
  // For sext all-zeros, lshr by anything gives 0.
  // But more generally, since the entire lane is uniform, any bit extraction
  // gives the same truth value.  We just need to verify the result is only
  // used as a 0-or-1 value.
  //
  // Simple check: the shift amount should be (elem_bits - 1) for a clean
  // MSB extraction, OR the result should be truncated to i1/used in or.
  // We'll be conservative and require shift_amt == elem_bits - 1 for bare
  // lshr without trunc, or accept any shift if truncated.
  if (!is_trunc && shift_amt != elem_bits - 1)
    return false;

  IRBuilder<> Builder(I);
  Value *flag = Builder.CreateExtractElement(
      sext->getOperand(0), Builder.getInt64(lane));
  Value *result = Builder.CreateZExt(flag, I->getType());

  I->replaceAllUsesWith(result);
  I->eraseFromParent();
  return true;
}

/// Scalarize `extractelement` from `sext <N x i1>` (with or without bitcast).
///
/// Since `sext <N x i1> to <N x iK>` produces all-ones or all-zeros per lane,
/// every sub-element (byte, i16, etc.) within a lane has the same uniform
/// value.  We can always replace with a scalar sext:
///
///   extractelement <M x iJ> (bitcast? (sext <N x i1> to <N x iK>)), idx
///   →  sext(extractelement <N x i1>, lane) to iJ
///
/// This enables InstCombine to fold downstream `and`, `lshr`, `zext` chains.
static bool tryScalarizeExtractFromSext(Instruction *I) {
  auto *EE = dyn_cast<ExtractElementInst>(I);
  if (!EE)
    return false;

  auto *idx_ci = dyn_cast<ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;
  unsigned idx = idx_ci->getZExtValue();

  Value *vec = EE->getVectorOperand();
  auto *vec_ty = dyn_cast<FixedVectorType>(vec->getType());
  if (!vec_ty || !vec_ty->getElementType()->isIntegerTy())
    return false;
  unsigned elem_bits = vec_ty->getElementType()->getIntegerBitWidth();

  // Peel optional bitcast.
  Value *inner = vec;
  if (auto *bc = dyn_cast<BitCastInst>(inner))
    inner = bc->getOperand(0);

  auto *sext = dyn_cast<SExtInst>(inner);
  if (!sext)
    return false;

  auto *src_vec_ty = dyn_cast<FixedVectorType>(sext->getOperand(0)->getType());
  if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
    return false;

  auto *dst_vec_ty = dyn_cast<FixedVectorType>(sext->getType());
  if (!dst_vec_ty)
    return false;

  unsigned lane_bits = dst_vec_ty->getElementType()->getIntegerBitWidth();
  unsigned num_lanes = src_vec_ty->getNumElements();

  // If extracting directly from the sext (no bitcast), elem == lane size.
  // Just scalarize: extractelement(sext(vec), idx) → sext(extractelement(vec, idx))
  if (inner == vec) {
    if (idx >= num_lanes)
      return false;
    IRBuilder<> Builder(I);
    Value *flag = Builder.CreateExtractElement(sext->getOperand(0),
                                               Builder.getInt64(idx));
    Value *result = Builder.CreateSExt(flag, I->getType());
    I->replaceAllUsesWith(result);
    I->eraseFromParent();
    return true;
  }

  // With bitcast: determine which lane the extracted element falls in.
  // Each lane is lane_bits wide; each extracted element is elem_bits wide.
  // The element at index `idx` spans bits [idx*elem_bits, (idx+1)*elem_bits).
  // It must fall entirely within one lane.
  unsigned bit_lo = idx * elem_bits;
  unsigned bit_hi = bit_lo + elem_bits;
  unsigned lane_lo = bit_lo / lane_bits;
  unsigned lane_hi = (bit_hi - 1) / lane_bits;
  if (lane_lo != lane_hi || lane_lo >= num_lanes)
    return false;

  IRBuilder<> Builder(I);
  Value *flag = Builder.CreateExtractElement(sext->getOperand(0),
                                             Builder.getInt64(lane_lo));
  Value *result = Builder.CreateSExt(flag, I->getType());
  I->replaceAllUsesWith(result);
  I->eraseFromParent();
  return true;
}

static bool runOnFunction(Function &F) {
  bool changed = false;
  bool changed_this_iter;

  do {
    changed_this_iter = false;

    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ) {
        Instruction *I = &*it++;

        // Try the and-mask pattern (handles both direct sext and
        // bitcast+lshr+trunc chains).
        if (trySimplifyAndMask(I)) {
          changed_this_iter = true;
          continue;
        }

        // Try bare lshr pattern (no trailing and).
        if (trySimplifyBareLshr(I)) {
          changed_this_iter = true;
          continue;
        }

        // Scalarize extractelement from sext <N x i1> (unconditional).
        if (tryScalarizeExtractFromSext(I)) {
          changed_this_iter = true;
          continue;
        }
      }
    }

    changed |= changed_this_iter;
  } while (changed_this_iter);

  return changed;
}

}  // namespace

PreservedAnalyses SimplifyVectorFlagComputationPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  if (!runOnFunction(F))
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

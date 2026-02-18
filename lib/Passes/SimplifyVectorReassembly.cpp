#include "omill/Passes/SimplifyVectorReassembly.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/Debug.h>

#define DEBUG_TYPE "simplify-vector-reassembly"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace omill {

namespace {

// ============================================================================
// Phase 1: FoldConstantVectorChains
// ============================================================================

/// Trace a single element of a vector value through nested shufflevectors
/// and insertelement chains to find the ultimate constant source.
Constant *traceElement(Value *V, unsigned idx, unsigned depth) {
  if (depth > 16)
    return nullptr;

  if (auto *C = dyn_cast<Constant>(V)) {
    auto *VTy = dyn_cast<FixedVectorType>(V->getType());
    if (!VTy)
      return nullptr;

    if (auto *CV = dyn_cast<ConstantVector>(C))
      return CV->getAggregateElement(idx);
    if (auto *CDV = dyn_cast<ConstantDataVector>(C))
      return CDV->getElementAsConstant(idx);
    if (isa<ConstantAggregateZero>(C))
      return Constant::getNullValue(VTy->getElementType());
    if (isa<PoisonValue>(C))
      return PoisonValue::get(VTy->getElementType());
    if (isa<UndefValue>(C))
      return UndefValue::get(VTy->getElementType());
    return nullptr;
  }

  if (auto *SV = dyn_cast<ShuffleVectorInst>(V)) {
    auto *VTy = dyn_cast<FixedVectorType>(V->getType());
    if (!VTy)
      return nullptr;

    int mask = SV->getMaskValue(idx);
    if (mask < 0)
      return PoisonValue::get(VTy->getElementType());

    auto *SrcTy = cast<FixedVectorType>(SV->getOperand(0)->getType());
    unsigned num = SrcTy->getNumElements();

    if (static_cast<unsigned>(mask) < num)
      return traceElement(SV->getOperand(0), mask, depth + 1);
    else
      return traceElement(SV->getOperand(1), mask - num, depth + 1);
  }

  if (auto *IE = dyn_cast<InsertElementInst>(V)) {
    auto *idx_val = dyn_cast<ConstantInt>(IE->getOperand(2));
    if (!idx_val)
      return nullptr;

    if (idx_val->getZExtValue() == idx) {
      if (auto *C = dyn_cast<Constant>(IE->getOperand(1)))
        return C;
      return nullptr;
    }
    return traceElement(IE->getOperand(0), idx, depth + 1);
  }

  return nullptr;
}

static bool foldConstantVectorChains(Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end();) {
      auto *I = &*it++;

      if (!isa<ShuffleVectorInst>(I) && !isa<InsertElementInst>(I))
        continue;

      auto *VTy = dyn_cast<FixedVectorType>(I->getType());
      if (!VTy)
        continue;

      unsigned num_elems = VTy->getNumElements();
      SmallVector<Constant *, 16> elements;
      bool all_const = true;

      for (unsigned i = 0; i < num_elems; ++i) {
        auto *elem = traceElement(I, i, 0);
        if (!elem) {
          all_const = false;
          break;
        }
        elements.push_back(elem);
      }

      if (!all_const)
        continue;

      LLVM_DEBUG(dbgs() << "[FoldConstVec] folding: " << *I << "\n");

      auto *folded = ConstantVector::get(elements);
      I->replaceAllUsesWith(folded);
      I->eraseFromParent();
      changed = true;
    }
  }

  return changed;
}

// ============================================================================
// Phase 2: CollapsePartialXMMWrites
// ============================================================================

static bool collapsePartialXMMWrites(Function &F) {
  bool changed = false;
  bool changed_this_iter;

  do {
    changed_this_iter = false;

    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ) {
        auto *EE = dyn_cast<ExtractElementInst>(&*it++);
        if (!EE)
          continue;

        auto *idx_ci = dyn_cast<ConstantInt>(EE->getIndexOperand());
        if (!idx_ci)
          continue;

        auto *SV = dyn_cast<ShuffleVectorInst>(EE->getVectorOperand());
        if (!SV)
          continue;

        auto *in_ty = dyn_cast<FixedVectorType>(SV->getOperand(0)->getType());
        if (!in_ty)
          continue;

        unsigned lane = idx_ci->getZExtValue();
        int mask_val = SV->getMaskValue(lane);
        if (mask_val < 0)
          continue;

        unsigned num_in_elts = in_ty->getNumElements();
        unsigned mask_unsigned = static_cast<unsigned>(mask_val);

        Value *src_vec;
        unsigned src_lane;
        if (mask_unsigned < num_in_elts) {
          src_vec = SV->getOperand(0);
          src_lane = mask_unsigned;
        } else {
          src_vec = SV->getOperand(1);
          src_lane = mask_unsigned - num_in_elts;
        }

        // Resolve through nested shufflevectors (depth limit 8).
        for (unsigned depth = 0; depth < 8; ++depth) {
          auto *inner_sv = dyn_cast<ShuffleVectorInst>(src_vec);
          if (!inner_sv)
            break;
          auto *inner_in_ty =
              dyn_cast<FixedVectorType>(inner_sv->getOperand(0)->getType());
          if (!inner_in_ty)
            break;
          int inner_mask = inner_sv->getMaskValue(src_lane);
          if (inner_mask < 0)
            break;
          unsigned inner_n = inner_in_ty->getNumElements();
          if ((unsigned)inner_mask < inner_n) {
            src_vec = inner_sv->getOperand(0);
            src_lane = (unsigned)inner_mask;
          } else {
            src_vec = inner_sv->getOperand(1);
            src_lane = (unsigned)inner_mask - inner_n;
          }
        }

        if (src_vec == EE->getVectorOperand() && src_lane == lane)
          continue;

        auto *new_idx = ConstantInt::get(idx_ci->getType(), src_lane);
        auto *new_ee = ExtractElementInst::Create(src_vec, new_idx);
        new_ee->insertBefore(EE->getIterator());
        EE->replaceAllUsesWith(new_ee);
        EE->eraseFromParent();
        changed_this_iter = true;
      }
    }

    changed |= changed_this_iter;
  } while (changed_this_iter);

  return changed;
}

// ============================================================================
// Phase 3: CoalesceByteReassembly
// ============================================================================

struct ByteContribution {
  Value *root_vec = nullptr;
  unsigned src_byte_offset = 0;
  unsigned num_bytes = 0;
  unsigned dst_byte_offset = 0;
};

static Value *traceVectorRoot(Value *V) {
  while (auto *BC = dyn_cast<BitCastInst>(V))
    V = BC->getOperand(0);
  return V;
}

static bool matchLeaf(Value *V, unsigned dst_byte_offset,
                       ByteContribution &contrib) {
  Value *inner = V;
  unsigned shift_bits = 0;

  Value *shl_lhs;
  ConstantInt *shl_amt;
  if (match(V, m_Shl(m_Value(shl_lhs), m_ConstantInt(shl_amt)))) {
    shift_bits = shl_amt->getZExtValue();
    if (shift_bits % 8 != 0)
      return false;
    inner = shl_lhs;
    dst_byte_offset = shift_bits / 8;
  }

  Value *zext_src;
  if (match(inner, m_ZExt(m_Value(zext_src))))
    inner = zext_src;

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

static bool collectContributions(Value *V,
                                  SmallVectorImpl<ByteContribution> &contribs) {
  Value *lhs, *rhs;
  if (match(V, m_DisjointOr(m_Value(lhs), m_Value(rhs)))) {
    return collectContributions(lhs, contribs) &&
           collectContributions(rhs, contribs);
  }

  ByteContribution contrib;
  if (matchLeaf(V, 0, contrib)) {
    contribs.push_back(contrib);
    return true;
  }

  return false;
}

static bool validateContributions(
    ArrayRef<ByteContribution> contribs, unsigned max_result_bytes,
    Value *&out_root, unsigned &out_base_byte, unsigned &out_num_bytes,
    unsigned &out_min_dst) {
  if (contribs.empty())
    return false;

  Value *root = contribs[0].root_vec;
  for (auto &c : contribs) {
    if (c.root_vec != root)
      return false;
  }

  auto *root_ty = dyn_cast<FixedVectorType>(root->getType());
  if (!root_ty)
    return false;
  unsigned root_bits = root_ty->getPrimitiveSizeInBits();
  if (root_bits != 128)
    return false;

  unsigned min_dst = UINT_MAX;
  unsigned max_dst = 0;
  for (auto &c : contribs) {
    if (c.dst_byte_offset < min_dst)
      min_dst = c.dst_byte_offset;
    unsigned end = c.dst_byte_offset + c.num_bytes;
    if (end > max_dst)
      max_dst = end;
  }

  unsigned span = max_dst - min_dst;

  unsigned extract_bytes = 1;
  while (extract_bytes < span)
    extract_bytes *= 2;
  if (extract_bytes > max_result_bytes)
    return false;

  SmallVector<int, 16> byte_map(extract_bytes, -1);

  for (auto &c : contribs) {
    for (unsigned i = 0; i < c.num_bytes; ++i) {
      unsigned dst = c.dst_byte_offset + i;
      if (dst < min_dst || dst >= min_dst + extract_bytes)
        return false;
      unsigned local = dst - min_dst;
      if (byte_map[local] != -1)
        return false;
      byte_map[local] = c.src_byte_offset + i;
    }
  }

  for (unsigned i = 0; i < extract_bytes; ++i) {
    if (byte_map[i] == -1)
      return false;
  }

  unsigned base = byte_map[0];
  for (unsigned i = 1; i < extract_bytes; ++i) {
    if (byte_map[i] != (int)(base + i))
      return false;
  }

  if (base % extract_bytes != 0)
    return false;

  out_root = root;
  out_base_byte = base;
  out_num_bytes = extract_bytes;
  out_min_dst = min_dst;
  return true;
}

static bool coalesceByteReassembly(Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end(); ) {
      auto *I = &*it++;

      auto *BO = dyn_cast<BinaryOperator>(I);
      if (!BO || BO->getOpcode() != Instruction::Or)
        continue;
      if (!BO->getType()->isIntegerTy(64))
        continue;

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

      unsigned elem_bits = num_bytes * 8;
      unsigned num_elems = 128 / elem_bits;
      auto *elem_ty = IntegerType::get(F.getContext(), elem_bits);
      auto *wide_ty = FixedVectorType::get(elem_ty, num_elems);
      Value *bc = Builder.CreateBitCast(root_vec, wide_ty);
      unsigned lane = base_byte / num_bytes;
      Value *extract = Builder.CreateExtractElement(bc, lane);

      Value *result;
      if (num_bytes < 8) {
        result = Builder.CreateZExt(extract, BO->getType());
      } else {
        result = extract;
      }

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

// ============================================================================
// Phase 4: SimplifyVectorFlagComputation
// ============================================================================

static bool traceSextOrigin(Value *V, unsigned bit_pos,
                            SExtInst *&sext_out, unsigned &lane_out) {
  if (auto *trunc = dyn_cast<TruncInst>(V))
    V = trunc->getOperand(0);

  unsigned lshr_amt = 0;
  Value *lshr_lhs;
  ConstantInt *lshr_ci;
  if (match(V, m_LShr(m_Value(lshr_lhs), m_ConstantInt(lshr_ci)))) {
    lshr_amt = lshr_ci->getZExtValue();
    V = lshr_lhs;
  }

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

  if (auto *bc = dyn_cast<BitCastInst>(vec)) {
    vec = bc->getOperand(0);
  }

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

  unsigned global_bit = idx * elem_bits + lshr_amt + bit_pos;

  unsigned lane = global_bit / lane_bits;
  if (lane >= num_lanes)
    return false;

  sext_out = sext;
  lane_out = lane;
  return true;
}

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

static bool trySimplifyBareLshr(Instruction *I) {
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

  auto *EE = dyn_cast<ExtractElementInst>(lshr_lhs);
  if (!EE)
    return false;

  auto *idx_ci = dyn_cast<ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;

  Value *vec = EE->getVectorOperand();

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

  unsigned global_bit = idx * elem_bits + shift_amt;
  unsigned lane = global_bit / lane_bits;
  if (lane >= num_lanes)
    return false;

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

static bool simplifyVectorFlagComputation(Function &F) {
  bool changed = false;
  bool changed_this_iter;

  do {
    changed_this_iter = false;

    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ) {
        Instruction *I = &*it++;

        if (trySimplifyAndMask(I)) {
          changed_this_iter = true;
          continue;
        }

        if (trySimplifyBareLshr(I)) {
          changed_this_iter = true;
          continue;
        }

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

// ============================================================================
// Pass entry point
// ============================================================================

PreservedAnalyses SimplifyVectorReassemblyPass::run(
    Function &F, FunctionAnalysisManager &AM) {
  bool changed = false;

  changed |= foldConstantVectorChains(F);
  changed |= collapsePartialXMMWrites(F);
  changed |= coalesceByteReassembly(F);
  changed |= simplifyVectorFlagComputation(F);

  if (!changed)
    return PreservedAnalyses::all();

  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  return PA;
}

}  // namespace omill

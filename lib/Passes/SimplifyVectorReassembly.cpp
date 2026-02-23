#include "omill/Passes/SimplifyVectorReassembly.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/Debug.h>

#define DEBUG_TYPE "simplify-vector-reassembly"

namespace omill {

namespace {

using namespace llvm::PatternMatch;

// ============================================================================
// Phase 1: FoldConstantVectorChains
// ============================================================================

/// Trace a single element of a vector value through nested shufflevectors
/// and insertelement chains to find the ultimate constant source.
llvm::Constant *traceElement(llvm::Value *V, unsigned idx, unsigned depth) {
  if (depth > 16)
    return nullptr;

  if (auto *C = llvm::dyn_cast<llvm::Constant>(V)) {
    auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(V->getType());
    if (!VTy)
      return nullptr;

    if (auto *CV = llvm::dyn_cast<llvm::ConstantVector>(C))
      return CV->getAggregateElement(idx);
    if (auto *CDV = llvm::dyn_cast<llvm::ConstantDataVector>(C))
      return CDV->getElementAsConstant(idx);
    if (llvm::isa<llvm::ConstantAggregateZero>(C))
      return llvm::Constant::getNullValue(VTy->getElementType());
    if (llvm::isa<llvm::PoisonValue>(C))
      return llvm::PoisonValue::get(VTy->getElementType());
    if (llvm::isa<llvm::UndefValue>(C))
      return llvm::UndefValue::get(VTy->getElementType());
    return nullptr;
  }

  if (auto *SV = llvm::dyn_cast<llvm::ShuffleVectorInst>(V)) {
    auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(V->getType());
    if (!VTy)
      return nullptr;

    int mask = SV->getMaskValue(idx);
    if (mask < 0)
      return llvm::PoisonValue::get(VTy->getElementType());

    auto *SrcTy = llvm::cast<llvm::FixedVectorType>(SV->getOperand(0)->getType());
    unsigned num = SrcTy->getNumElements();

    if (static_cast<unsigned>(mask) < num)
      return traceElement(SV->getOperand(0), mask, depth + 1);
    else
      return traceElement(SV->getOperand(1), mask - num, depth + 1);
  }

  if (auto *IE = llvm::dyn_cast<llvm::InsertElementInst>(V)) {
    auto *idx_val = llvm::dyn_cast<llvm::ConstantInt>(IE->getOperand(2));
    if (!idx_val)
      return nullptr;

    if (idx_val->getZExtValue() == idx) {
      if (auto *C = llvm::dyn_cast<llvm::Constant>(IE->getOperand(1)))
        return C;
      return nullptr;
    }
    return traceElement(IE->getOperand(0), idx, depth + 1);
  }

  return nullptr;
}

static bool foldConstantVectorChains(llvm::Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end();) {
      auto *I = &*it++;

      if (!llvm::isa<llvm::ShuffleVectorInst>(I) && !llvm::isa<llvm::InsertElementInst>(I))
        continue;

      auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(I->getType());
      if (!VTy)
        continue;

      unsigned num_elems = VTy->getNumElements();
      llvm::SmallVector<llvm::Constant *, 16> elements;
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

      LLVM_DEBUG(llvm::dbgs() << "[FoldConstVec] folding: " << *I << "\n");

      auto *folded = llvm::ConstantVector::get(elements);
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

static bool collapsePartialXMMWrites(llvm::Function &F) {
  bool changed = false;
  bool changed_this_iter;

  do {
    changed_this_iter = false;

    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ) {
        auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&*it++);
        if (!EE)
          continue;

        auto *idx_ci = llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand());
        if (!idx_ci)
          continue;

        auto *SV = llvm::dyn_cast<llvm::ShuffleVectorInst>(EE->getVectorOperand());
        if (!SV)
          continue;

        auto *in_ty = llvm::dyn_cast<llvm::FixedVectorType>(SV->getOperand(0)->getType());
        if (!in_ty)
          continue;

        unsigned lane = idx_ci->getZExtValue();
        int mask_val = SV->getMaskValue(lane);
        if (mask_val < 0)
          continue;

        unsigned num_in_elts = in_ty->getNumElements();
        unsigned mask_unsigned = static_cast<unsigned>(mask_val);

        llvm::Value *src_vec;
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
          auto *inner_sv = llvm::dyn_cast<llvm::ShuffleVectorInst>(src_vec);
          if (!inner_sv)
            break;
          auto *inner_in_ty =
              llvm::dyn_cast<llvm::FixedVectorType>(inner_sv->getOperand(0)->getType());
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

        auto *new_idx = llvm::ConstantInt::get(idx_ci->getType(), src_lane);
        auto *new_ee = llvm::ExtractElementInst::Create(src_vec, new_idx);
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
  llvm::Value *root_vec = nullptr;
  unsigned src_byte_offset = 0;
  unsigned num_bytes = 0;
  unsigned dst_byte_offset = 0;
};

static llvm::Value *traceVectorRoot(llvm::Value *V) {
  while (auto *BC = llvm::dyn_cast<llvm::BitCastInst>(V))
    V = BC->getOperand(0);
  return V;
}

static bool matchLeaf(llvm::Value *V, unsigned dst_byte_offset,
                       ByteContribution &contrib) {
  llvm::Value *inner = V;
  unsigned shift_bits = 0;

  llvm::Value *shl_lhs;
  llvm::ConstantInt *shl_amt;
  if (match(V, m_Shl(m_Value(shl_lhs), m_ConstantInt(shl_amt)))) {
    shift_bits = shl_amt->getZExtValue();
    if (shift_bits % 8 != 0)
      return false;
    inner = shl_lhs;
    dst_byte_offset = shift_bits / 8;
  }

  llvm::Value *zext_src;
  if (match(inner, m_ZExt(m_Value(zext_src))))
    inner = zext_src;

  llvm::Value *vec;
  llvm::ConstantInt *idx;
  if (!match(inner, m_ExtractElt(m_Value(vec), m_ConstantInt(idx))))
    return false;

  auto *vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(vec->getType());
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

static bool collectContributions(llvm::Value *V,
                                  llvm::SmallVectorImpl<ByteContribution> &contribs) {
  llvm::Value *lhs, *rhs;
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
    llvm::ArrayRef<ByteContribution> contribs, unsigned max_result_bytes,
    llvm::Value *&out_root, unsigned &out_base_byte, unsigned &out_num_bytes,
    unsigned &out_min_dst) {
  if (contribs.empty())
    return false;

  llvm::Value *root = contribs[0].root_vec;
  for (auto &c : contribs) {
    if (c.root_vec != root)
      return false;
  }

  auto *root_ty = llvm::dyn_cast<llvm::FixedVectorType>(root->getType());
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

  llvm::SmallVector<int, 16> byte_map(extract_bytes, -1);

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

static bool coalesceByteReassembly(llvm::Function &F) {
  bool changed = false;

  for (auto &BB : F) {
    for (auto it = BB.begin(); it != BB.end(); ) {
      auto *I = &*it++;

      auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(I);
      if (!BO || BO->getOpcode() != llvm::Instruction::Or)
        continue;
      if (!BO->getType()->isIntegerTy(64))
        continue;

      if (!BO->hasPoisonGeneratingFlags() ||
          !llvm::cast<llvm::PossiblyDisjointInst>(BO)->isDisjoint())
        continue;

      llvm::SmallVector<ByteContribution, 8> contribs;
      if (!collectContributions(BO, contribs))
        continue;

      llvm::Value *root_vec = nullptr;
      unsigned base_byte = 0;
      unsigned num_bytes = 0;
      unsigned min_dst = 0;
      if (!validateContributions(contribs, 8, root_vec, base_byte, num_bytes,
                                 min_dst))
        continue;

      llvm::IRBuilder<> Builder(BO);

      unsigned elem_bits = num_bytes * 8;
      unsigned num_elems = 128 / elem_bits;
      auto *elem_ty = llvm::IntegerType::get(F.getContext(), elem_bits);
      auto *wide_ty = llvm::FixedVectorType::get(elem_ty, num_elems);
      llvm::Value *bc = Builder.CreateBitCast(root_vec, wide_ty);
      unsigned lane = base_byte / num_bytes;
      llvm::Value *extract = Builder.CreateExtractElement(bc, lane);

      llvm::Value *result;
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

static bool traceSextOrigin(llvm::Value *V, unsigned bit_pos,
                            llvm::SExtInst *&sext_out, unsigned &lane_out) {
  if (auto *trunc = llvm::dyn_cast<llvm::TruncInst>(V))
    V = trunc->getOperand(0);

  unsigned lshr_amt = 0;
  llvm::Value *lshr_lhs;
  llvm::ConstantInt *lshr_ci;
  if (match(V, m_LShr(m_Value(lshr_lhs), m_ConstantInt(lshr_ci)))) {
    lshr_amt = lshr_ci->getZExtValue();
    V = lshr_lhs;
  }

  auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(V);
  if (!EE)
    return false;

  auto *idx_ci = llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;
  unsigned idx = idx_ci->getZExtValue();

  llvm::Value *vec = EE->getVectorOperand();
  auto *vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(vec->getType());
  if (!vec_ty)
    return false;
  unsigned elem_bits = vec_ty->getElementType()->getIntegerBitWidth();

  if (auto *bc = llvm::dyn_cast<llvm::BitCastInst>(vec)) {
    vec = bc->getOperand(0);
  }

  auto *sext = llvm::dyn_cast<llvm::SExtInst>(vec);
  if (!sext)
    return false;

  auto *src_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(sext->getOperand(0)->getType());
  if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
    return false;

  auto *dst_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(sext->getType());
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

static bool trySimplifyAndMask(llvm::Instruction *I) {
  llvm::Value *lhs, *rhs;
  if (!match(I, m_And(m_Value(lhs), m_Value(rhs))))
    return false;

  auto *mask_ci = llvm::dyn_cast<llvm::ConstantInt>(rhs);
  if (!mask_ci)
    return false;

  llvm::APInt mask_ap = mask_ci->getValue();
  if (!mask_ap.isPowerOf2())
    return false;

  unsigned bit_pos = mask_ap.logBase2();

  llvm::SExtInst *sext = nullptr;
  unsigned lane = 0;
  if (!traceSextOrigin(lhs, bit_pos, sext, lane))
    return false;

  llvm::IRBuilder<> Builder(I);
  llvm::Value *flag = Builder.CreateExtractElement(
      sext->getOperand(0), Builder.getInt64(lane));
  llvm::Value *zext_val = Builder.CreateZExt(flag, I->getType());

  llvm::Value *result;
  if (bit_pos == 0) {
    result = zext_val;
  } else {
    result = Builder.CreateShl(zext_val, bit_pos);
  }

  I->replaceAllUsesWith(result);
  I->eraseFromParent();
  return true;
}

static bool trySimplifyBareLshr(llvm::Instruction *I) {
  llvm::Value *inner = I;
  bool is_trunc = false;
  if (auto *trunc = llvm::dyn_cast<llvm::TruncInst>(I)) {
    inner = trunc->getOperand(0);
    is_trunc = true;
  }

  llvm::Value *lshr_lhs;
  llvm::ConstantInt *lshr_ci;
  if (!match(inner, m_LShr(m_Value(lshr_lhs), m_ConstantInt(lshr_ci))))
    return false;

  unsigned shift_amt = lshr_ci->getZExtValue();

  auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(lshr_lhs);
  if (!EE)
    return false;

  auto *idx_ci = llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;

  llvm::Value *vec = EE->getVectorOperand();

  if (auto *bc = llvm::dyn_cast<llvm::BitCastInst>(vec))
    vec = bc->getOperand(0);

  auto *sext = llvm::dyn_cast<llvm::SExtInst>(vec);
  if (!sext)
    return false;

  auto *src_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(sext->getOperand(0)->getType());
  if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
    return false;

  auto *dst_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(sext->getType());
  if (!dst_vec_ty)
    return false;

  auto *ee_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(EE->getVectorOperand()->getType());
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

  llvm::IRBuilder<> Builder(I);
  llvm::Value *flag = Builder.CreateExtractElement(
      sext->getOperand(0), Builder.getInt64(lane));
  llvm::Value *result = Builder.CreateZExt(flag, I->getType());

  I->replaceAllUsesWith(result);
  I->eraseFromParent();
  return true;
}

static bool tryScalarizeExtractFromSext(llvm::Instruction *I) {
  auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(I);
  if (!EE)
    return false;

  auto *idx_ci = llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand());
  if (!idx_ci)
    return false;
  unsigned idx = idx_ci->getZExtValue();

  llvm::Value *vec = EE->getVectorOperand();
  auto *vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(vec->getType());
  if (!vec_ty || !vec_ty->getElementType()->isIntegerTy())
    return false;
  unsigned elem_bits = vec_ty->getElementType()->getIntegerBitWidth();

  llvm::Value *inner = vec;
  if (auto *bc = llvm::dyn_cast<llvm::BitCastInst>(inner))
    inner = bc->getOperand(0);

  auto *sext = llvm::dyn_cast<llvm::SExtInst>(inner);
  if (!sext)
    return false;

  auto *src_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(sext->getOperand(0)->getType());
  if (!src_vec_ty || !src_vec_ty->getElementType()->isIntegerTy(1))
    return false;

  auto *dst_vec_ty = llvm::dyn_cast<llvm::FixedVectorType>(sext->getType());
  if (!dst_vec_ty)
    return false;

  unsigned lane_bits = dst_vec_ty->getElementType()->getIntegerBitWidth();
  unsigned num_lanes = src_vec_ty->getNumElements();

  if (inner == vec) {
    if (idx >= num_lanes)
      return false;
    llvm::IRBuilder<> Builder(I);
    llvm::Value *flag = Builder.CreateExtractElement(sext->getOperand(0),
                                               Builder.getInt64(idx));
    llvm::Value *result = Builder.CreateSExt(flag, I->getType());
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

  llvm::IRBuilder<> Builder(I);
  llvm::Value *flag = Builder.CreateExtractElement(sext->getOperand(0),
                                             Builder.getInt64(lane_lo));
  llvm::Value *result = Builder.CreateSExt(flag, I->getType());
  I->replaceAllUsesWith(result);
  I->eraseFromParent();
  return true;
}

static bool simplifyVectorFlagComputation(llvm::Function &F) {
  bool changed = false;
  bool changed_this_iter;

  do {
    changed_this_iter = false;

    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ) {
        llvm::Instruction *I = &*it++;

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

llvm::PreservedAnalyses SimplifyVectorReassemblyPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  changed |= foldConstantVectorChains(F);
  changed |= collapsePartialXMMWrites(F);
  changed |= coalesceByteReassembly(F);
  changed |= simplifyVectorFlagComputation(F);

  if (!changed)
    return llvm::PreservedAnalyses::all();

  llvm::PreservedAnalyses PA;
  PA.preserveSet<llvm::CFGAnalyses>();
  return PA;
}

}  // namespace omill

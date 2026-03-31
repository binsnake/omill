#pragma once

// Internal header — shared helpers for RecoverJumpTables and
// SymbolicJumpTableSolver.  Not installed.

#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/KnownBits.h>
#include <llvm/Support/Format.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

#include <cstdlib>
#include <optional>

namespace omill {
namespace jt {

using namespace llvm::PatternMatch;

/// A linear address decomposition: ptr = base + index * stride.
struct LinearAddress {
  llvm::Value *index;
  uint64_t base;
  unsigned stride;
};

inline llvm::Value *stripSimpleValueCasts(llvm::Value *V) {
  while (true) {
    if (auto *cast = llvm::dyn_cast<llvm::CastInst>(V)) {
      V = cast->getOperand(0);
      continue;
    }
    if (auto *freeze = llvm::dyn_cast<llvm::FreezeInst>(V)) {
      V = freeze->getOperand(0);
      continue;
    }
    if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
      switch (ce->getOpcode()) {
        case llvm::Instruction::IntToPtr:
        case llvm::Instruction::PtrToInt:
        case llvm::Instruction::BitCast:
        case llvm::Instruction::Trunc:
        case llvm::Instruction::ZExt:
        case llvm::Instruction::SExt:
          V = ce->getOperand(0);
          continue;
        default:
          break;
      }
    }
    break;
  }
  return V;
}

inline bool containsLoadLikeValue(llvm::Value *V, unsigned depth = 0) {
  if (!V || depth > 8)
    return false;

  V = stripSimpleValueCasts(V);
  if (llvm::isa<llvm::LoadInst>(V))
    return true;

  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
  if (!BO)
    return false;

  switch (BO->getOpcode()) {
    case llvm::Instruction::Add:
    case llvm::Instruction::Sub:
    case llvm::Instruction::And:
    case llvm::Instruction::Or:
    case llvm::Instruction::Xor:
      return containsLoadLikeValue(BO->getOperand(0), depth + 1) ||
             containsLoadLikeValue(BO->getOperand(1), depth + 1);
    default:
      return false;
  }
}

inline llvm::LoadInst *extractUnderlyingLoad(llvm::Value *V,
                                             unsigned depth = 0) {
  if (!V || depth > 8)
    return nullptr;

  V = stripSimpleValueCasts(V);
  if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V))
    return LI;

  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
  if (!BO)
    return nullptr;

  llvm::LoadInst *lhs_load = extractUnderlyingLoad(BO->getOperand(0), depth + 1);
  llvm::LoadInst *rhs_load = extractUnderlyingLoad(BO->getOperand(1), depth + 1);
  if (lhs_load && !rhs_load)
    return lhs_load;
  if (rhs_load && !lhs_load)
    return rhs_load;
  return nullptr;
}

inline bool trySplitDynamicRVAConversion(llvm::Value *target,
                                         llvm::Value *&image_base_value,
                                         llvm::Value *&load_value) {
  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(target);
  if (!BO || BO->getOpcode() != llvm::Instruction::Add)
    return false;
  llvm::Value *lhs = BO->getOperand(0);
  llvm::Value *rhs = BO->getOperand(1);

  auto *lhs_load = extractUnderlyingLoad(lhs);
  auto *rhs_load = extractUnderlyingLoad(rhs);
  bool lhs_load_like = (lhs_load != nullptr);
  bool rhs_load_like = (rhs_load != nullptr);

  if (lhs_load_like && !rhs_load_like) {
    load_value = lhs;
    image_base_value = rhs;
    return true;
  }
  if (rhs_load_like && !lhs_load_like) {
    load_value = rhs;
    image_base_value = lhs;
    return true;
  }

  if (lhs_load_like && rhs_load_like) {
    auto lhs_bits =
        lhs_load->getType()->getScalarSizeInBits();
    auto rhs_bits =
        rhs_load->getType()->getScalarSizeInBits();
    if (lhs_bits != rhs_bits) {
      if (lhs_bits < rhs_bits) {
        load_value = lhs;
        image_base_value = rhs;
      } else {
        load_value = rhs;
        image_base_value = lhs;
      }
      return true;
    }
  }
  return false;
}

inline std::optional<uint64_t> foldConstAtEntryPC(
    llvm::Value *V, const llvm::Function &F,
    llvm::DenseMap<llvm::Value *, std::optional<uint64_t>> &memo,
    llvm::SmallPtrSet<llvm::Value *, 32> &in_progress,
    unsigned depth = 0) {
  if (!V || depth > 24)
    return std::nullopt;

  if (auto it = memo.find(V); it != memo.end())
    return it->second;

  if (in_progress.contains(V))
    return std::nullopt;
  in_progress.insert(V);

  auto finish = [&](std::optional<uint64_t> val) -> std::optional<uint64_t> {
    in_progress.erase(V);
    memo[V] = val;
    return val;
  };

  // Treat the lifted function's program_counter parameter as entry VA.
  if (F.arg_size() >= 2 && V == F.getArg(1))
    return finish(extractEntryVA(F.getName()));

  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    if (ci->getValue().getActiveBits() <= 64)
      return finish(ci->getZExtValue());
    return finish(std::nullopt);
  }

  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto lhs = foldConstAtEntryPC(BO->getOperand(0), F, memo, in_progress,
                                  depth + 1);
    auto rhs = foldConstAtEntryPC(BO->getOperand(1), F, memo, in_progress,
                                  depth + 1);
    if (lhs && rhs) {
      if (BO->getOpcode() == llvm::Instruction::Add)
        return finish(*lhs + *rhs);
      if (BO->getOpcode() == llvm::Instruction::Sub)
        return finish(*lhs - *rhs);
    }
    return finish(std::nullopt);
  }

  if (auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
    std::optional<uint64_t> merged;
    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
      auto val = foldConstAtEntryPC(PN->getIncomingValue(i), F, memo,
                                    in_progress, depth + 1);
      if (!val)
        continue;
      if (!merged)
        merged = *val;
      else if (*merged != *val)
        return finish(std::nullopt);
    }
    return finish(merged);
  }

  if (auto *SI = llvm::dyn_cast<llvm::SelectInst>(V)) {
    auto tv = foldConstAtEntryPC(SI->getTrueValue(), F, memo, in_progress,
                                 depth + 1);
    auto fv = foldConstAtEntryPC(SI->getFalseValue(), F, memo, in_progress,
                                 depth + 1);
    if (tv && fv && *tv == *fv)
      return finish(*tv);
    // Optimistic: if only one arm folds, use it.  This is sound for jump
    // table resolution because the result is validated against the binary
    // memory map — an incorrect base produces unreadable addresses and the
    // candidate is discarded harmlessly.
    if (tv && !fv)
      return finish(*tv);
    if (fv && !tv)
      return finish(*fv);
    return finish(std::nullopt);
  }

  if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V))
    return finish(foldConstAtEntryPC(CI->getOperand(0), F, memo, in_progress,
                                     depth + 1));

  if (auto *FI = llvm::dyn_cast<llvm::FreezeInst>(V))
    return finish(foldConstAtEntryPC(FI->getOperand(0), F, memo, in_progress,
                                     depth + 1));

  // Load from State GEP: walk backwards to find the nearest dominating store
  // to the same pointer and fold through the stored value.  This handles the
  // pattern where PromoteStateToSSA flushed a register (e.g. R10D) to State
  // and a later block reloads it, but GVN failed to forward due to aliasing.
  if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
    auto *ptr = LI->getPointerOperand();
    // Only handle loads from State GEPs (arg0 + const offset).
    auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr);
    if (gep && gep->getPointerOperand() == F.getArg(0) &&
        gep->hasAllConstantIndices()) {
      // Compute the byte offset of this GEP.
      llvm::APInt load_offset(64, 0);
      if (!gep->accumulateConstantOffset(
              F.getDataLayout(), load_offset))
        return finish(std::nullopt);
      uint64_t target_offset = load_offset.getZExtValue();

      // Match stores by offset, not pointer identity, because inlining
      // may produce distinct GEP instructions at the same offset.
      auto matchesOffset = [&](llvm::Value *store_ptr) -> bool {
        if (store_ptr == ptr) return true;
        auto *sg = llvm::dyn_cast<llvm::GetElementPtrInst>(store_ptr);
        if (!sg || sg->getPointerOperand() != F.getArg(0) ||
            !sg->hasAllConstantIndices())
          return false;
        llvm::APInt so(64, 0);
        if (!sg->accumulateConstantOffset(
                F.getDataLayout(), so))
          return false;
        return so.getZExtValue() == target_offset;
      };

      // Walk backwards in same block to find store to same State offset.
      auto *BB = LI->getParent();
      llvm::StoreInst *found_store = nullptr;
      for (auto it = llvm::BasicBlock::reverse_iterator(
               LI->getIterator());
           it != BB->rend(); ++it) {
        if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it)) {
          if (matchesOffset(SI->getPointerOperand())) {
            found_store = SI;
            break;
          }
        }
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&*it))
          if (!CI->doesNotAccessMemory())
            break;
      }
      // Walk up the single-predecessor chain to find the store.
      if (!found_store) {
        llvm::SmallPtrSet<llvm::BasicBlock *, 8> visited;
        visited.insert(BB);
        auto *cur = BB;
        for (unsigned chain = 0; chain < 8 && !found_store; ++chain) {
          auto *pred = cur->getSinglePredecessor();
          if (!pred || visited.count(pred))
            break;
          visited.insert(pred);
          for (auto &I : llvm::reverse(*pred)) {
            if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
              if (matchesOffset(SI->getPointerOperand())) {
                found_store = SI;
                break;
              }
            }
            if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
              if (!CI->doesNotAccessMemory())
                goto done_walk;
          }
          cur = pred;
        }
        done_walk:;
      }
      if (found_store) {
        return finish(foldConstAtEntryPC(found_store->getValueOperand(), F,
                                         memo, in_progress, depth + 1));
      }
    }
  }

  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr ||
        CE->getOpcode() == llvm::Instruction::PtrToInt ||
        CE->getOpcode() == llvm::Instruction::BitCast ||
        CE->getOpcode() == llvm::Instruction::Trunc ||
        CE->getOpcode() == llvm::Instruction::ZExt ||
        CE->getOpcode() == llvm::Instruction::SExt) {
      return finish(foldConstAtEntryPC(CE->getOperand(0), F, memo,
                                       in_progress, depth + 1));
    }
    if (CE->getOpcode() == llvm::Instruction::Add ||
        CE->getOpcode() == llvm::Instruction::Sub) {
      auto lhs = foldConstAtEntryPC(CE->getOperand(0), F, memo, in_progress,
                                    depth + 1);
      auto rhs = foldConstAtEntryPC(CE->getOperand(1), F, memo, in_progress,
                                    depth + 1);
      if (lhs && rhs) {
        if (CE->getOpcode() == llvm::Instruction::Add)
          return finish(*lhs + *rhs);
        return finish(*lhs - *rhs);
      }
    }
  }

  return finish(std::nullopt);
}

inline std::optional<uint64_t> foldConstAtEntryPC(llvm::Value *V,
                                                  const llvm::Function &F) {
  llvm::DenseMap<llvm::Value *, std::optional<uint64_t>> memo;
  llvm::SmallPtrSet<llvm::Value *, 32> in_progress;
  return foldConstAtEntryPC(V, F, memo, in_progress);
}

// ---------------------------------------------------------------------------
// Address decomposition
// ---------------------------------------------------------------------------

/// Decompose a pointer operand into base + index * stride.
/// Handles: inttoptr(add(shl/mul/zext/sext/gep, const_base))
///          inttoptr(add(add(..., const), const_base))
///          inttoptr(or(shl(idx, N), base)) when low bits of base are zero
inline std::optional<LinearAddress> decomposeTableAddress(
    llvm::Value *ptr, const llvm::Function *F = nullptr) {
  // Strip inttoptr.
  llvm::Value *addr = nullptr;
  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
    addr = ITP->getOperand(0);
  else if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    // getelementptr i8, ptr %base, i64 %scaled_idx
    if (GEP->getNumIndices() == 1 && GEP->getSourceElementType()->isIntegerTy(8)) {
      auto *base_ptr = GEP->getPointerOperand();
      auto *idx_val = GEP->getOperand(1);
      // base_ptr must be a constant (inttoptr of constant).
      if (auto *base_ce = llvm::dyn_cast<llvm::ConstantExpr>(base_ptr)) {
        if (base_ce->getOpcode() == llvm::Instruction::IntToPtr) {
          if (auto *base_ci = llvm::dyn_cast<llvm::ConstantInt>(base_ce->getOperand(0))) {
            // Check if idx_val has a stride.
            llvm::Value *idx;
            llvm::ConstantInt *shift_ci;
            if (match(idx_val, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
              unsigned shift = shift_ci->getZExtValue();
              if (shift >= 1 && shift <= 3)
                return LinearAddress{idx, base_ci->getZExtValue(), 1u << shift};
            }
            llvm::ConstantInt *stride_ci;
            if (match(idx_val, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
              uint64_t stride = stride_ci->getZExtValue();
              if (stride >= 1 && stride <= 8)
                return LinearAddress{idx, base_ci->getZExtValue(),
                                     static_cast<unsigned>(stride)};
            }
            // Stride 1.
            return LinearAddress{idx_val, base_ci->getZExtValue(), 1};
          }
        }
      }
      if (auto *base_itp = llvm::dyn_cast<llvm::IntToPtrInst>(base_ptr)) {
        if (F) {
          if (auto base_val = foldConstAtEntryPC(base_itp->getOperand(0), *F)) {
            // Check if idx_val has a stride.
            llvm::Value *idx;
            llvm::ConstantInt *shift_ci;
            if (match(idx_val, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
              unsigned shift = shift_ci->getZExtValue();
              if (shift >= 1 && shift <= 3)
                return LinearAddress{idx, *base_val, 1u << shift};
            }
            llvm::ConstantInt *stride_ci;
            if (match(idx_val, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
              uint64_t stride = stride_ci->getZExtValue();
              if (stride >= 1 && stride <= 8)
                return LinearAddress{idx, *base_val,
                                     static_cast<unsigned>(stride)};
            }
            return LinearAddress{idx_val, *base_val, 1};
          }
        }
      }
    }
    return std::nullopt;
  } else {
    return std::nullopt;
  }

  // Accumulate constant offsets through chained adds.
  // addr = add(add(add(scaled, c1), c2), c3) => base = c1+c2+c3
  uint64_t accum_base = 0;
  while (true) {
    llvm::Value *lhs, *rhs;
    if (!match(addr, m_Add(m_Value(lhs), m_Value(rhs))))
      break;

    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
      accum_base += ci->getZExtValue();
      addr = lhs;
    } else if (F) {
      if (auto folded = foldConstAtEntryPC(rhs, *F)) {
        accum_base += *folded;
        addr = lhs;
      } else if (auto folded_lhs = foldConstAtEntryPC(lhs, *F)) {
        accum_base += *folded_lhs;
        addr = rhs;
      } else {
        break;
      }
    } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
      accum_base += ci->getZExtValue();
      addr = rhs;
    } else {
      break;
    }
  }

  // If we peeled at least one constant, addr is now the scaled part.
  if (accum_base != 0) {
    llvm::Value *scaled = addr;
    llvm::Value *idx;
    llvm::ConstantInt *shift_ci;
    if (match(scaled, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
      unsigned shift = shift_ci->getZExtValue();
      if (shift >= 1 && shift <= 3)
        return LinearAddress{idx, accum_base, 1u << shift};
    }
    llvm::ConstantInt *stride_ci;
    if (match(scaled, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
      uint64_t stride = stride_ci->getZExtValue();
      if (stride >= 1 && stride <= 8)
        return LinearAddress{idx, accum_base, static_cast<unsigned>(stride)};
    }
    // zext/sext wrapping shl/mul.
    llvm::Value *inner;
    if (match(scaled, m_ZExt(m_Value(inner))) ||
        match(scaled, m_SExt(m_Value(inner)))) {
      if (match(inner, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
        unsigned shift = shift_ci->getZExtValue();
        if (shift >= 1 && shift <= 3)
          return LinearAddress{idx, accum_base, 1u << shift};
      }
      if (match(inner, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
        uint64_t stride = stride_ci->getZExtValue();
        if (stride >= 1 && stride <= 8)
          return LinearAddress{idx, accum_base, static_cast<unsigned>(stride)};
      }
    }
    // add(non_const_base, shl/mul(idx, stride)) — after GVN forwards a
    // State register store, the base register value appears as an SSA
    // expression (e.g. R10D = NEXT_PC + offset).  Try to fold it.
    if (F) {
      auto tryScaledAdd = [&](llvm::Value *extra,
                              llvm::Value *rest) -> std::optional<LinearAddress> {
        auto folded = foldConstAtEntryPC(extra, *F);
        if (!folded)
          return std::nullopt;
        uint64_t total_base = accum_base + *folded;
        if (match(rest, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
          unsigned shift = shift_ci->getZExtValue();
          if (shift >= 1 && shift <= 3)
            return LinearAddress{idx, total_base, 1u << shift};
        }
        if (match(rest, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
          uint64_t stride = stride_ci->getZExtValue();
          if (stride >= 1 && stride <= 8)
            return LinearAddress{idx, total_base, static_cast<unsigned>(stride)};
        }
        return std::nullopt;
      };
      llvm::Value *add_lhs, *add_rhs;
      if (match(scaled, m_Add(m_Value(add_lhs), m_Value(add_rhs)))) {
        if (auto r = tryScaledAdd(add_lhs, add_rhs))
          return *r;
        if (auto r = tryScaledAdd(add_rhs, add_lhs))
          return *r;
      }
    }
    return std::nullopt;
  }

  // OR-as-add: or(shl(idx, N), base_const) when low bits of base are zero.
  {
    llvm::Value *lhs, *rhs;
    if (match(addr, m_Or(m_Value(lhs), m_Value(rhs)))) {
      llvm::ConstantInt *base_ci = nullptr;
      llvm::Value *scaled = nullptr;
      if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
        base_ci = ci;
        scaled = lhs;
      } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
        base_ci = ci;
        scaled = rhs;
      }
      if (base_ci && scaled) {
        llvm::Value *idx;
        llvm::ConstantInt *shift_ci;
        if (match(scaled, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
          unsigned shift = shift_ci->getZExtValue();
          uint64_t base_val = base_ci->getZExtValue();
          // Check that low `shift` bits of base are zero (OR == ADD).
          if (shift >= 1 && shift <= 3 && (base_val & ((1u << shift) - 1)) == 0)
            return LinearAddress{idx, base_val, 1u << shift};
        }
      }
    }
  }

  // Single add(scaled, const_base) — the original simple pattern.
  {
    llvm::Value *lhs, *rhs;
    if (!match(addr, m_Add(m_Value(lhs), m_Value(rhs))))
      return std::nullopt;

    llvm::ConstantInt *base_ci = nullptr;
    llvm::Value *scaled = nullptr;
    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
      base_ci = ci;
      scaled = lhs;
    } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
      base_ci = ci;
      scaled = rhs;
    } else {
      return std::nullopt;
    }

    uint64_t base = base_ci->getZExtValue();
    llvm::Value *idx;
    llvm::ConstantInt *shift_ci;
    if (match(scaled, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
      unsigned shift = shift_ci->getZExtValue();
      if (shift >= 1 && shift <= 3)
        return LinearAddress{idx, base, 1u << shift};
      return std::nullopt;
    }
    llvm::ConstantInt *stride_ci;
    if (match(scaled, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
      uint64_t stride = stride_ci->getZExtValue();
      if (stride >= 1 && stride <= 8)
        return LinearAddress{idx, base, static_cast<unsigned>(stride)};
      return std::nullopt;
    }
    llvm::Value *inner;
    if (match(scaled, m_ZExt(m_Value(inner))) ||
        match(scaled, m_SExt(m_Value(inner)))) {
      if (match(inner, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
        unsigned shift = shift_ci->getZExtValue();
        if (shift >= 1 && shift <= 3)
          return LinearAddress{idx, base, 1u << shift};
      }
      if (match(inner, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
        uint64_t stride = stride_ci->getZExtValue();
        if (stride >= 1 && stride <= 8)
          return LinearAddress{idx, base, static_cast<unsigned>(stride)};
      }
    }
    return std::nullopt;
  }
}

inline std::optional<LinearAddress> decomposeTableAddressWithDynamicBase(
    llvm::Value *ptr, llvm::Value *dynamic_base, uint64_t concrete_base) {
  auto *addr = llvm::dyn_cast<llvm::IntToPtrInst>(ptr);
  if (!addr)
    return std::nullopt;

  llvm::Value *expr = addr->getOperand(0);
  uint64_t accum_base = 0;

  while (true) {
    llvm::Value *lhs = nullptr;
    llvm::Value *rhs = nullptr;
    if (!match(expr, m_Add(m_Value(lhs), m_Value(rhs))))
      break;

    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
      accum_base += ci->getZExtValue();
      expr = lhs;
      continue;
    }
    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
      accum_base += ci->getZExtValue();
      expr = rhs;
      continue;
    }
    break;
  }

  llvm::Value *lhs = nullptr;
  llvm::Value *rhs = nullptr;
  if (!match(expr, m_Add(m_Value(lhs), m_Value(rhs))))
    return std::nullopt;

  llvm::Value *scaled = nullptr;
  if (stripSimpleValueCasts(lhs) == stripSimpleValueCasts(dynamic_base)) {
    scaled = rhs;
  } else if (stripSimpleValueCasts(rhs) == stripSimpleValueCasts(dynamic_base)) {
    scaled = lhs;
  } else {
    return std::nullopt;
  }

  llvm::Value *idx = nullptr;
  llvm::ConstantInt *shift_ci = nullptr;
  if (match(scaled, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
    unsigned shift = shift_ci->getZExtValue();
    if (shift >= 1 && shift <= 3)
      return LinearAddress{idx, concrete_base + accum_base, 1u << shift};
    return std::nullopt;
  }

  llvm::ConstantInt *stride_ci = nullptr;
  if (match(scaled, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
    uint64_t stride = stride_ci->getZExtValue();
    if (stride >= 1 && stride <= 8)
      return LinearAddress{idx, concrete_base + accum_base,
                           static_cast<unsigned>(stride)};
  }

  return std::nullopt;
}

// ---------------------------------------------------------------------------
// Index range computation
// ---------------------------------------------------------------------------

inline bool matchIndexEqConst(llvm::Value *V, llvm::Value *idx,
                              uint64_t &N) {
  V = stripSimpleValueCasts(V);
  auto *ICI = llvm::dyn_cast<llvm::ICmpInst>(V);
  if (!ICI || ICI->getPredicate() != llvm::ICmpInst::ICMP_EQ)
    return false;

  auto *lhs = stripSimpleValueCasts(ICI->getOperand(0));
  auto *rhs = stripSimpleValueCasts(ICI->getOperand(1));
  if (lhs == idx) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
      N = CI->getZExtValue();
      return true;
    }
  }
  if (rhs == idx) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
      N = CI->getZExtValue();
      return true;
    }
  }
  return false;
}

inline bool matchIndexUpperBoundTruth(llvm::Value *V, llvm::Value *idx,
                                      uint64_t &bound) {
  V = stripSimpleValueCasts(V);
  auto *ICI = llvm::dyn_cast<llvm::ICmpInst>(V);
  if (ICI) {
    auto *lhs = stripSimpleValueCasts(ICI->getOperand(0));
    auto *rhs = stripSimpleValueCasts(ICI->getOperand(1));
    auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs);
    if (lhs == idx && CI) {
      switch (ICI->getPredicate()) {
        case llvm::ICmpInst::ICMP_ULT:
        case llvm::ICmpInst::ICMP_SLT:
          bound = CI->getZExtValue();
          return true;
        case llvm::ICmpInst::ICMP_ULE:
        case llvm::ICmpInst::ICMP_SLE:
          bound = CI->getZExtValue() + 1;
          return true;
        default:
          break;
      }
    }
  }

  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
  if (!BO || BO->getOpcode() != llvm::Instruction::Or)
    return false;

  uint64_t eq_N = 0;
  uint64_t ult_bound = 0;
  if (matchIndexEqConst(BO->getOperand(0), idx, eq_N) &&
      matchIndexUpperBoundTruth(BO->getOperand(1), idx, ult_bound) &&
      ult_bound == eq_N) {
    bound = eq_N + 1;
    return true;
  }
  if (matchIndexEqConst(BO->getOperand(1), idx, eq_N) &&
      matchIndexUpperBoundTruth(BO->getOperand(0), idx, ult_bound) &&
      ult_bound == eq_N) {
    bound = eq_N + 1;
    return true;
  }
  return false;
}

/// Collect a ConstantRange for `idx` by walking predecessors of `bb`.
/// Returns the upper bound (exclusive) if a valid range can be determined.
inline std::optional<uint64_t> computeIndexRange(llvm::Value *idx,
                                                  llvm::BasicBlock *bb,
                                                  unsigned depth = 0) {
  const unsigned kMaxDepth = 3;
  std::optional<uint64_t> syntactic_bound;

  // Fast path: AND mask.
  llvm::Value *orig;
  llvm::ConstantInt *mask_ci;
  if (match(idx, m_And(m_Value(orig), m_ConstantInt(mask_ci)))) {
    uint64_t mask = mask_ci->getZExtValue();
    if ((mask & (mask + 1)) == 0)
      syntactic_bound = mask + 1;
  }

  // ZExt/SExt: narrow to source width.
  if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(idx)) {
    unsigned src_bits = zext->getSrcTy()->getIntegerBitWidth();
    uint64_t max_val = (1ULL << src_bits);
    // Also try to get tighter bounds from predecessors of the source.
    auto inner = computeIndexRange(zext->getOperand(0), bb, depth);
    if (inner && *inner < max_val)
      return *inner;
    // The zext itself limits to [0, 2^src_bits).
    if (max_val <= 1024)
      syntactic_bound = syntactic_bound ? std::min(*syntactic_bound, max_val)
                                        : std::optional<uint64_t>(max_val);
  }

  // PHI: union of ranges from each incoming block.
  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(idx)) {
    if (depth >= kMaxDepth)
      return std::nullopt;
    uint64_t max_bound = 0;
    bool all_bounded = true;
    for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
      auto *inc_val = phi->getIncomingValue(i);
      auto *inc_bb = phi->getIncomingBlock(i);
      // If incoming value is a constant, its "range" is [val, val+1).
      if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(inc_val)) {
        uint64_t v = ci->getZExtValue();
        if (v + 1 > max_bound)
          max_bound = v + 1;
        continue;
      }
      auto bound = computeIndexRange(inc_val, inc_bb, depth + 1);
      if (!bound) {
        all_bounded = false;
        break;
      }
      if (*bound > max_bound)
        max_bound = *bound;
    }
    if (all_bounded && max_bound > 0 && max_bound <= 1024)
      return max_bound;
  }

  // Walk predecessors looking for conditional branches with icmp on idx.
  // Collect the tightest (minimum) upper bound from all predecessors.
  std::optional<uint64_t> best_bound;

  auto tryBound = [&](uint64_t b) {
    if (!best_bound || b < *best_bound)
      best_bound = b;
  };

  // Walk up to kMaxDepth levels of single-predecessor chains.
  llvm::SmallVector<llvm::BasicBlock *, 4> worklist;
  llvm::SmallPtrSet<llvm::BasicBlock *, 8> visited;
  worklist.push_back(bb);
  unsigned walk_depth = 0;

  while (!worklist.empty() && walk_depth <= kMaxDepth) {
    llvm::SmallVector<llvm::BasicBlock *, 4> next;
    for (auto *cur : worklist) {
      if (!visited.insert(cur).second)
        continue;
      for (auto *pred : predecessors(cur)) {
        auto *BI = llvm::dyn_cast<llvm::BranchInst>(pred->getTerminator());
        if (!BI) {
          next.push_back(pred);
          continue;
        }

        // Unconditional branches — walk through them.
        if (!BI->isConditional()) {
          next.push_back(pred);
          continue;
        }

        auto *ICI = llvm::dyn_cast<llvm::ICmpInst>(BI->getCondition());
        if (!ICI) {
          next.push_back(pred);
          continue;
        }

        auto pred_type = ICI->getPredicate();
        auto *lhs = ICI->getOperand(0);
        auto *rhs = ICI->getOperand(1);
        bool on_true = (BI->getSuccessor(0) == cur);
        bool on_false = (BI->getSuccessor(1) == cur);

        // Recognize branch conditions that materialize "idx <= N" as a
        // non-zero byte/bit and then compare that against zero.
        llvm::Value *truthy = nullptr;
        if (pred_type == llvm::ICmpInst::ICMP_EQ ||
            pred_type == llvm::ICmpInst::ICMP_NE) {
          auto *lhs_stripped = stripSimpleValueCasts(lhs);
          auto *rhs_stripped = stripSimpleValueCasts(rhs);
          if (match(rhs_stripped, m_ZeroInt())) {
            truthy = lhs_stripped;
          } else if (match(lhs_stripped, m_ZeroInt())) {
            truthy = rhs_stripped;
          }
        }
        if (truthy) {
          uint64_t guarded_bound = 0;
          if (matchIndexUpperBoundTruth(truthy, idx, guarded_bound)) {
            if ((pred_type == llvm::ICmpInst::ICMP_EQ && on_false) ||
                (pred_type == llvm::ICmpInst::ICMP_NE && on_true)) {
              tryBound(guarded_bound);
              continue;
            }
          }
        }

        // Match idx on the LHS.
        if (lhs != idx) {
          next.push_back(pred);
          continue;
        }

        auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs);
        if (!CI) {
          next.push_back(pred);
          continue;
        }

        uint64_t N = CI->getZExtValue();

        // icmp ult idx, N — true edge => idx < N
        if (pred_type == llvm::ICmpInst::ICMP_ULT && on_true)
          tryBound(N);
        // icmp uge idx, N — false edge => idx < N
        if (pred_type == llvm::ICmpInst::ICMP_UGE && on_false)
          tryBound(N);
        // icmp ule idx, N — true edge => idx <= N => idx < N+1
        if (pred_type == llvm::ICmpInst::ICMP_ULE && on_true)
          tryBound(N + 1);
        // icmp ugt idx, N — false edge => idx <= N => idx < N+1
        if (pred_type == llvm::ICmpInst::ICMP_UGT && on_false)
          tryBound(N + 1);
        // icmp slt idx, N — true edge, if N > 0 and reasonable
        if (pred_type == llvm::ICmpInst::ICMP_SLT && on_true && N > 0 &&
            N <= 1024)
          tryBound(N);
        // icmp sle idx, N — true edge
        if (pred_type == llvm::ICmpInst::ICMP_SLE && on_true && N < 1024)
          tryBound(N + 1);
      }
    }
    worklist = std::move(next);
    ++walk_depth;
  }

  if (best_bound && syntactic_bound)
    return std::min(*best_bound, *syntactic_bound);
  if (best_bound)
    return best_bound;
  return syntactic_bound;
}

// ---------------------------------------------------------------------------
// RVA unwrapping
// ---------------------------------------------------------------------------

/// Strip RVA→VA conversion: target = add(zext/sext(load_val), image_base).
/// Returns {image_base, inner_value}.
inline std::pair<uint64_t, llvm::Value *>
unwrapRVAConversion(llvm::Value *target, const llvm::Function *F = nullptr) {
  llvm::Value *loaded;
  llvm::ConstantInt *addend;

  if (match(target, m_Add(m_Value(loaded), m_ConstantInt(addend))))
    return {addend->getZExtValue(), loaded};
  if (match(target, m_Add(m_ConstantInt(addend), m_Value(loaded))))
    return {addend->getZExtValue(), loaded};

  // Some lifted traces keep image-base arithmetic as
  // add(load_or_zext, program_counter + const). Fold that term.
  llvm::Value *lhs = nullptr;
  llvm::Value *rhs = nullptr;
  if (match(target, m_Add(m_Value(lhs), m_Value(rhs))) && F) {
    if (auto folded_rhs = foldConstAtEntryPC(rhs, *F))
      return {*folded_rhs, lhs};
    if (auto folded_lhs = foldConstAtEntryPC(lhs, *F))
      return {*folded_lhs, rhs};
  }

  return {0, target};
}

// ---------------------------------------------------------------------------
// Table reading
// ---------------------------------------------------------------------------

/// Read `count` entries from binary memory at `base` with given `stride`.
/// Returns the raw integer values.  Returns std::nullopt if any entry
/// is unreadable.
inline std::optional<llvm::SmallVector<uint64_t, 16>>
readTableEntries(const BinaryMemoryMap &map, uint64_t base, unsigned stride,
                 uint64_t count) {
  llvm::SmallVector<uint64_t, 16> entries;
  entries.reserve(count);
  for (uint64_t i = 0; i < count; ++i) {
    uint64_t entry_addr = base + i * stride;
    auto val = map.readInt(entry_addr, stride);
    if (!val)
      return std::nullopt;
    entries.push_back(*val);
  }
  return entries;
}

/// Apply RVA→VA conversion to raw table values.
inline void applyRVAConversion(llvm::MutableArrayRef<uint64_t> entries,
                               uint64_t image_base, unsigned stride) {
  if (image_base == 0)
    return;
  for (auto &v : entries) {
    if (stride == 4)
      v = static_cast<uint64_t>(static_cast<int32_t>(v));
    v += image_base;
  }
}

inline unsigned trimTrailingInvalidEntries(
    llvm::SmallVectorImpl<uint64_t> &entries, const BinaryMemoryMap &map) {
  unsigned trimmed = 0;
  const bool has_image_bounds = map.imageBase() != 0 && map.imageSize() != 0;
  while (!entries.empty()) {
    uint64_t target = entries.back();
    bool plausible = (target != 0);
    if (plausible && has_image_bounds) {
      plausible = target >= map.imageBase() &&
                  target < (map.imageBase() + map.imageSize());
    }
    if (plausible)
      break;
    entries.pop_back();
    ++trimmed;
  }
  return trimmed;
}

// ---------------------------------------------------------------------------
// Switch building
// ---------------------------------------------------------------------------

struct SwitchResult {
  bool changed = false;
};

/// Build a switch instruction from resolved table entries.
/// Replaces the dispatch_call + ret in the given BB.
inline SwitchResult buildSwitchFromEntries(
    llvm::ArrayRef<uint64_t> entry_targets, llvm::Value *index,
    uint64_t image_base, llvm::CallInst *dispatch_call,
    llvm::ReturnInst *ret, llvm::BranchInst *branch, llvm::Function &F,
    const BinaryMemoryMap &map,
    const LiftedFunctionMap *lifted) {

  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *BB = dispatch_call->getParent();

  struct CaseTarget {
    uint64_t index;
    llvm::BasicBlock *target_bb;
  };
  llvm::SmallVector<CaseTarget, 16> cases;
  bool all_resolved = true;
  const bool debug_jump_tables =
      (std::getenv("OMILL_DEBUG_JUMP_TABLES") != nullptr);

  for (uint64_t i = 0; i < entry_targets.size(); ++i) {
    uint64_t target_va = entry_targets[i];
    llvm::BasicBlock *local_bb = nullptr;
    auto local_block_name =
        (llvm::Twine("block_") + llvm::Twine::utohexstr(target_va)).str();
    for (auto &candidate_bb : F) {
      if (candidate_bb.getName() == local_block_name) {
        local_bb = &candidate_bb;
        break;
      }
    }
    if (local_bb) {
      if (debug_jump_tables) {
        llvm::errs() << "[jt-build] " << F.getName()
                     << " entry[" << i << "]=0x"
                     << llvm::format_hex(target_va, 10)
                     << " -> local-bb " << local_bb->getName() << "\n";
      }
      cases.push_back({i, local_bb});
      continue;
    }

    // Prefer lifted block/function targets over direct intra-function edges.
    // This avoids introducing new CFG predecessors into trace-lifted blocks
    // whose PHIs were built for a different predecessor set.
    auto *target_fn = lifted ? lifted->lookup(target_va) : nullptr;
    if (!target_fn) {
      auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(target_va)).str();
      target_fn = F.getParent()->getFunction(block_name);
    }
    if (!target_fn) {
      auto lifted_name = (llvm::Twine("sub_") + llvm::Twine::utohexstr(target_va)).str();
      target_fn = F.getParent()->getFunction(lifted_name);
    }
    if (target_fn) {
      if (debug_jump_tables) {
        llvm::errs() << "[jt-build] " << F.getName()
                     << " entry[" << i << "]=0x"
                     << llvm::format_hex(target_va, 10)
                     << " -> fn " << target_fn->getName() << "\n";
      }
      char name[64];
      snprintf(name, sizeof(name), "jt_case_%llu",
               (unsigned long long)i);
      auto *trampoline = llvm::BasicBlock::Create(Ctx, name, &F);
      llvm::IRBuilder<> TBuilder(trampoline);

      auto *state = dispatch_call->getArgOperand(0);
      auto *pc_val = llvm::ConstantInt::get(i64_ty, target_va);
      auto *mem = dispatch_call->getArgOperand(2);

      auto *tail = TBuilder.CreateCall(target_fn, {state, pc_val, mem});
      tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
      TBuilder.CreateRet(tail);

      cases.push_back({i, trampoline});
      continue;
    }

    if (debug_jump_tables) {
      llvm::errs() << "[jt-build] " << F.getName()
                   << " entry[" << i << "]=0x"
                   << llvm::format_hex(target_va, 10)
                   << " unresolved\n";
    }
    all_resolved = false;
  }

  if (cases.empty())
    return {false};

  auto *join_bb = branch ? branch->getSuccessor(0) : nullptr;

  // Create default block.
  llvm::BasicBlock *default_bb = nullptr;
  if (!all_resolved || cases.size() < entry_targets.size()) {
    default_bb = llvm::BasicBlock::Create(Ctx, "jt_default", &F);
    llvm::IRBuilder<> DBuilder(default_bb);
    auto *dispatch_fn = dispatch_call->getCalledFunction();
    auto *new_call = DBuilder.CreateCall(
        dispatch_fn,
        {dispatch_call->getArgOperand(0),
         dispatch_call->getArgOperand(1),
         dispatch_call->getArgOperand(2)});
    if (ret) {
      DBuilder.CreateRet(new_call);
    } else {
      for (auto &I : *join_bb) {
        auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
        if (!phi)
          break;
        int incoming_idx = phi->getBasicBlockIndex(BB);
        if (incoming_idx < 0)
          continue;
        auto *old_incoming = phi->getIncomingValue(incoming_idx);
        llvm::Value *new_incoming = old_incoming;
        if (old_incoming == dispatch_call) {
          new_incoming = new_call;
        } else if (auto *incoming_inst =
                       llvm::dyn_cast<llvm::Instruction>(old_incoming)) {
          if (incoming_inst->getParent() == BB)
            new_incoming = llvm::PoisonValue::get(phi->getType());
        }
        phi->addIncoming(new_incoming, default_bb);
      }
      DBuilder.CreateBr(join_bb);
    }
  } else {
    default_bb = llvm::BasicBlock::Create(Ctx, "jt_default", &F);
    new llvm::UnreachableInst(Ctx, default_bb);
  }

  // Save old successors for PHI cleanup.
  llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

  // Build switch.
  llvm::IRBuilder<> Builder(dispatch_call);
  auto *sw = Builder.CreateSwitch(index, default_bb, cases.size());
  for (auto &c : cases)
    sw->addCase(
        llvm::ConstantInt::get(
            llvm::cast<llvm::IntegerType>(index->getType()), c.index),
        c.target_bb);

  // Erase original dispatch_jump + ret.
  dispatch_call->replaceAllUsesWith(
      llvm::PoisonValue::get(dispatch_call->getType()));
  if (ret)
    ret->eraseFromParent();
  else
    branch->eraseFromParent();
  dispatch_call->eraseFromParent();

  // Clean up dead instructions after switch.
  while (&BB->back() != sw) {
    auto &dead = BB->back();
    if (!dead.use_empty())
      dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
    dead.eraseFromParent();
  }

  // Update PHI nodes for removed predecessors.
  llvm::SmallPtrSet<llvm::BasicBlock *, 16> new_succs(
      successors(BB).begin(), successors(BB).end());
  for (auto *old_succ : old_succs)
    if (!new_succs.count(old_succ))
      old_succ->removePredecessor(BB);

  return {true};
}

}  // namespace jt
}  // namespace omill

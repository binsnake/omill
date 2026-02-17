#if OMILL_ENABLE_Z3

#include "omill/Utils/TranslationValidator.h"

#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <algorithm>
#include <set>

namespace omill {

TranslationValidator::TranslationValidator(z3::context &ctx) : ctx_(ctx) {}

z3::expr *TranslationValidator::own(z3::expr e) {
  auto p = std::make_unique<z3::expr>(e);
  auto *ptr = p.get();
  owned_.push_back(std::move(p));
  return ptr;
}

void TranslationValidator::snapshotBefore(llvm::Function &F) {
  snapshot_module_ = llvm::CloneModule(*F.getParent());
  snapshot_fn_name_ = F.getName().str();
}

void TranslationValidator::setCompareOffsets(std::vector<unsigned> offsets) {
  compare_offsets_ = std::move(offsets);
}

void TranslationValidator::setMaxStateOffset(unsigned max_offset) {
  max_state_offset_ = max_offset;
}

unsigned TranslationValidator::getBitWidth(llvm::Type *T) {
  if (T->isIntegerTy())
    return T->getIntegerBitWidth();
  if (T->isPointerTy())
    return 64;
  if (auto *VT = llvm::dyn_cast<llvm::FixedVectorType>(T))
    return VT->getNumElements() * getBitWidth(VT->getElementType());
  if (T->isFloatTy())
    return 32;
  if (T->isDoubleTy())
    return 64;
  return 64;
}

z3::expr TranslationValidator::translateValue(
    llvm::Value *V, llvm::DenseMap<llvm::Value *, z3::expr *> &value_map,
    z3::expr state_array) {
  auto it = value_map.find(V);
  if (it != value_map.end())
    return *it->second;

  // Constant integer.
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    unsigned w = CI->getBitWidth();
    if (w > 64) {
      llvm::SmallString<64> str_buf;
      CI->getValue().toString(str_buf, 10, false);
      auto e = ctx_.bv_val(str_buf.c_str(), w);
      value_map[V] = own(e);
      return e;
    }
    auto e = ctx_.bv_val(CI->getZExtValue(), w);
    value_map[V] = own(e);
    return e;
  }

  // Constant vector.
  if (auto *CV = llvm::dyn_cast<llvm::ConstantVector>(V)) {
    auto *VTy = llvm::cast<llvm::FixedVectorType>(CV->getType());
    unsigned N = VTy->getNumElements();
    unsigned elem_w = getBitWidth(VTy->getElementType());
    auto e0 = translateValue(CV->getOperand(0), value_map, state_array);
    if (e0.get_sort().bv_size() != elem_w)
      e0 = e0.extract(elem_w - 1, 0);
    z3::expr result = e0;
    for (unsigned i = 1; i < N; ++i) {
      auto ei = translateValue(CV->getOperand(i), value_map, state_array);
      if (ei.get_sort().bv_size() != elem_w)
        ei = ei.extract(elem_w - 1, 0);
      result = z3::concat(ei, result);
    }
    value_map[V] = own(result);
    return result;
  }

  // ConstantDataVector.
  if (auto *CDV = llvm::dyn_cast<llvm::ConstantDataVector>(V)) {
    auto *VTy = llvm::cast<llvm::FixedVectorType>(CDV->getType());
    unsigned N = VTy->getNumElements();
    unsigned elem_w = getBitWidth(VTy->getElementType());
    z3::expr result = ctx_.bv_val(CDV->getElementAsInteger(0), elem_w);
    for (unsigned i = 1; i < N; ++i) {
      auto ei = ctx_.bv_val(CDV->getElementAsInteger(i), elem_w);
      result = z3::concat(ei, result);
    }
    value_map[V] = own(result);
    return result;
  }

  // ConstantAggregateZero.
  if (llvm::isa<llvm::ConstantAggregateZero>(V)) {
    unsigned w = getBitWidth(V->getType());
    auto e = ctx_.bv_val(0, w);
    value_map[V] = own(e);
    return e;
  }

  // Poison/undef → fresh variable.
  if (llvm::isa<llvm::PoisonValue>(V) || llvm::isa<llvm::UndefValue>(V)) {
    unsigned w = getBitWidth(V->getType());
    auto e = ctx_.bv_const(
        ("undef_" + std::to_string(var_counter_++)).c_str(), w);
    value_map[V] = own(e);
    return e;
  }

  // Constant expression.
  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
    if (CE->getOpcode() == llvm::Instruction::BitCast) {
      auto src = translateValue(CE->getOperand(0), value_map, state_array);
      unsigned dst_w = getBitWidth(CE->getType());
      unsigned src_w = src.get_sort().bv_size();
      z3::expr result(ctx_);
      if (dst_w == src_w)
        result = src;
      else if (dst_w < src_w)
        result = src.extract(dst_w - 1, 0);
      else
        result = z3::zext(src, dst_w - src_w);
      value_map[V] = own(result);
      return result;
    }
  }

  // Function argument.
  if (auto *Arg = llvm::dyn_cast<llvm::Argument>(V)) {
    unsigned w = getBitWidth(V->getType());
    std::string name = "arg" + std::to_string(Arg->getArgNo());
    auto e = ctx_.bv_const(name.c_str(), w);
    value_map[V] = own(e);
    return e;
  }

  // Default: fresh variable.
  unsigned w = getBitWidth(V->getType());
  auto e =
      ctx_.bv_const(("v_" + std::to_string(var_counter_++)).c_str(), w);
  value_map[V] = own(e);
  return e;
}

z3::expr TranslationValidator::encodeBlock(
    llvm::BasicBlock &BB, z3::expr state_array, z3::expr &ret_val,
    llvm::DenseMap<llvm::Value *, z3::expr *> &value_map) {
  auto &DL = BB.getParent()->getParent()->getDataLayout();

  for (auto &I : BB) {
    // Load from State.
    if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      auto *ptr = LI->getPointerOperand();

      int64_t offset = -1;
      if (auto *arg = llvm::dyn_cast<llvm::Argument>(ptr)) {
        if (arg->getArgNo() == 0)
          offset = 0;
      }
      if (offset < 0) {
        if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(ptr)) {
          llvm::APInt ap(64, 0);
          if (GEP->accumulateConstantOffset(DL, ap)) {
            auto *base = GEP->getPointerOperand();
            if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
              if (arg->getArgNo() == 0)
                offset = ap.getSExtValue();
            }
          }
        }
      }

      if (offset >= 0) {
        unsigned total_bits = getBitWidth(LI->getType());
        unsigned bytes = total_bits / 8;
        z3::expr result = z3::select(state_array,
                                      ctx_.bv_val((unsigned)offset, 64));
        for (unsigned i = 1; i < bytes; ++i) {
          auto byte_i = z3::select(
              state_array, ctx_.bv_val((unsigned)(offset + i), 64));
          result = z3::concat(byte_i, result);
        }
        value_map[&I] = own(result);
        continue;
      }

      value_map[&I] = own(translateValue(&I, value_map, state_array));
      continue;
    }

    // Store to State.
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto *ptr = SI->getPointerOperand();
      auto *val = SI->getValueOperand();

      int64_t offset = -1;
      if (auto *arg = llvm::dyn_cast<llvm::Argument>(ptr)) {
        if (arg->getArgNo() == 0)
          offset = 0;
      }
      if (offset < 0) {
        if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(ptr)) {
          llvm::APInt ap(64, 0);
          if (GEP->accumulateConstantOffset(DL, ap)) {
            auto *base = GEP->getPointerOperand();
            if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
              if (arg->getArgNo() == 0)
                offset = ap.getSExtValue();
            }
          }
        }
      }

      if (offset >= 0) {
        auto z3_val = translateValue(val, value_map, state_array);
        unsigned total_bits = getBitWidth(val->getType());
        unsigned bytes = total_bits / 8;

        if (z3_val.get_sort().bv_size() != total_bits) {
          if (z3_val.get_sort().bv_size() > total_bits)
            z3_val = z3_val.extract(total_bits - 1, 0);
          else
            z3_val = z3::zext(z3_val, total_bits - z3_val.get_sort().bv_size());
        }

        for (unsigned i = 0; i < bytes; ++i) {
          auto byte_val = z3_val.extract(i * 8 + 7, i * 8);
          state_array = z3::store(
              state_array, ctx_.bv_val((unsigned)(offset + i), 64), byte_val);
          written_offsets_.push_back((unsigned)(offset + i));
        }
      }
      continue;
    }

    // Binary operations.
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
      auto lhs = translateValue(BO->getOperand(0), value_map, state_array);
      auto rhs = translateValue(BO->getOperand(1), value_map, state_array);

      unsigned lw = lhs.get_sort().bv_size();
      unsigned rw = rhs.get_sort().bv_size();
      if (lw != rw) {
        if (lw > rw)
          rhs = z3::zext(rhs, lw - rw);
        else
          lhs = z3::zext(lhs, rw - lw);
      }

      z3::expr result(ctx_);
      switch (BO->getOpcode()) {
        case llvm::Instruction::Add:  result = lhs + rhs; break;
        case llvm::Instruction::Sub:  result = lhs - rhs; break;
        case llvm::Instruction::Mul:  result = lhs * rhs; break;
        case llvm::Instruction::And:  result = lhs & rhs; break;
        case llvm::Instruction::Or:   result = lhs | rhs; break;
        case llvm::Instruction::Xor:  result = lhs ^ rhs; break;
        case llvm::Instruction::Shl:  result = z3::shl(lhs, rhs); break;
        case llvm::Instruction::LShr: result = z3::lshr(lhs, rhs); break;
        case llvm::Instruction::AShr: result = z3::ashr(lhs, rhs); break;
        case llvm::Instruction::UDiv: result = z3::udiv(lhs, rhs); break;
        case llvm::Instruction::SDiv: result = lhs / rhs; break;
        case llvm::Instruction::URem: result = z3::urem(lhs, rhs); break;
        case llvm::Instruction::SRem: result = z3::srem(lhs, rhs); break;
        default:
          result = translateValue(&I, value_map, state_array);
          break;
      }
      value_map[&I] = own(result);
      continue;
    }

    // ZExt.
    if (auto *ZE = llvm::dyn_cast<llvm::ZExtInst>(&I)) {
      auto src = translateValue(ZE->getOperand(0), value_map, state_array);
      unsigned dst_w = getBitWidth(ZE->getType());
      unsigned src_w = src.get_sort().bv_size();
      if (dst_w > src_w)
        value_map[&I] = own(z3::zext(src, dst_w - src_w));
      else
        value_map[&I] = own(src);
      continue;
    }

    // SExt — handles both scalar and vector.
    if (auto *SE = llvm::dyn_cast<llvm::SExtInst>(&I)) {
      auto *src_ty = SE->getOperand(0)->getType();
      auto *dst_ty = SE->getType();

      if (auto *src_vty = llvm::dyn_cast<llvm::FixedVectorType>(src_ty)) {
        auto *dst_vty = llvm::cast<llvm::FixedVectorType>(dst_ty);
        unsigned N = src_vty->getNumElements();
        unsigned src_ew = getBitWidth(src_vty->getElementType());
        unsigned dst_ew = getBitWidth(dst_vty->getElementType());

        auto src = translateValue(SE->getOperand(0), value_map, state_array);
        auto elem0 = src.extract(src_ew - 1, 0);
        z3::expr result = z3::sext(elem0, dst_ew - src_ew);
        for (unsigned i = 1; i < N; ++i) {
          auto elem = src.extract((i + 1) * src_ew - 1, i * src_ew);
          auto ext = z3::sext(elem, dst_ew - src_ew);
          result = z3::concat(ext, result);
        }
        value_map[&I] = own(result);
        continue;
      }

      auto src = translateValue(SE->getOperand(0), value_map, state_array);
      unsigned dst_w = getBitWidth(dst_ty);
      unsigned src_w = src.get_sort().bv_size();
      if (dst_w > src_w)
        value_map[&I] = own(z3::sext(src, dst_w - src_w));
      else
        value_map[&I] = own(src);
      continue;
    }

    // Trunc.
    if (auto *T = llvm::dyn_cast<llvm::TruncInst>(&I)) {
      auto src = translateValue(T->getOperand(0), value_map, state_array);
      unsigned dst_w = getBitWidth(T->getType());
      value_map[&I] = own(src.extract(dst_w - 1, 0));
      continue;
    }

    // BitCast — reinterpret bits.
    if (auto *BC = llvm::dyn_cast<llvm::BitCastInst>(&I)) {
      auto src = translateValue(BC->getOperand(0), value_map, state_array);
      unsigned dst_w = getBitWidth(BC->getType());
      unsigned src_w = src.get_sort().bv_size();

      z3::expr result(ctx_);
      if (dst_w == src_w)
        result = src;
      else if (dst_w < src_w)
        result = src.extract(dst_w - 1, 0);
      else
        result = z3::zext(src, dst_w - src_w);
      value_map[&I] = own(result);
      continue;
    }

    // ExtractElement.
    if (auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&I)) {
      auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(
          EE->getVectorOperand()->getType());
      if (VTy) {
        auto vec = translateValue(EE->getVectorOperand(), value_map,
                                   state_array);
        unsigned elem_w = getBitWidth(VTy->getElementType());
        unsigned N = VTy->getNumElements();

        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(
                EE->getIndexOperand())) {
          unsigned idx = (unsigned)CI->getZExtValue();
          if (idx < N) {
            unsigned lo = idx * elem_w;
            unsigned hi = lo + elem_w - 1;
            value_map[&I] = own(vec.extract(hi, lo));
            continue;
          }
        }

        auto idx = translateValue(EE->getIndexOperand(), value_map,
                                   state_array);
        unsigned idx_w = idx.get_sort().bv_size();
        z3::expr result = vec.extract(elem_w - 1, 0);
        for (unsigned i = 1; i < N; ++i) {
          auto cond = (idx == ctx_.bv_val(i, idx_w));
          auto elem = vec.extract((i + 1) * elem_w - 1, i * elem_w);
          result = z3::ite(cond, elem, result);
        }
        value_map[&I] = own(result);
        continue;
      }
      value_map[&I] = own(translateValue(&I, value_map, state_array));
      continue;
    }

    // InsertElement.
    if (auto *IE = llvm::dyn_cast<llvm::InsertElementInst>(&I)) {
      auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(IE->getType());
      if (VTy) {
        auto vec = translateValue(IE->getOperand(0), value_map, state_array);
        auto val = translateValue(IE->getOperand(1), value_map, state_array);
        unsigned elem_w = getBitWidth(VTy->getElementType());
        unsigned N = VTy->getNumElements();

        if (val.get_sort().bv_size() != elem_w) {
          if (val.get_sort().bv_size() > elem_w)
            val = val.extract(elem_w - 1, 0);
          else
            val = z3::zext(val, elem_w - val.get_sort().bv_size());
        }

        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(IE->getOperand(2))) {
          unsigned idx = (unsigned)CI->getZExtValue();
          if (idx < N) {
            std::vector<z3::expr> elems;
            for (unsigned i = 0; i < N; ++i)
              elems.push_back(vec.extract((i + 1) * elem_w - 1, i * elem_w));
            elems[idx] = val;

            z3::expr result = elems[0];
            for (unsigned i = 1; i < N; ++i)
              result = z3::concat(elems[i], result);
            value_map[&I] = own(result);
            continue;
          }
        }

        value_map[&I] = own(translateValue(&I, value_map, state_array));
        continue;
      }
      value_map[&I] = own(translateValue(&I, value_map, state_array));
      continue;
    }

    // ShuffleVector.
    if (auto *SV = llvm::dyn_cast<llvm::ShuffleVectorInst>(&I)) {
      auto *src_vty = llvm::dyn_cast<llvm::FixedVectorType>(
          SV->getOperand(0)->getType());
      auto *dst_vty = llvm::dyn_cast<llvm::FixedVectorType>(SV->getType());
      if (src_vty && dst_vty) {
        auto v1 = translateValue(SV->getOperand(0), value_map, state_array);
        auto v2 = translateValue(SV->getOperand(1), value_map, state_array);
        unsigned elem_w = getBitWidth(src_vty->getElementType());
        unsigned src_n = src_vty->getNumElements();
        unsigned dst_n = dst_vty->getNumElements();

        auto mask = SV->getShuffleMask();
        auto getElem = [&](int idx) -> z3::expr {
          if (idx < 0 || idx == llvm::PoisonMaskElem) {
            return ctx_.bv_const(
                ("shuf_undef_" + std::to_string(var_counter_++)).c_str(),
                elem_w);
          }
          unsigned uidx = (unsigned)idx;
          if (uidx < src_n)
            return v1.extract((uidx + 1) * elem_w - 1, uidx * elem_w);
          unsigned idx2 = uidx - src_n;
          return v2.extract((idx2 + 1) * elem_w - 1, idx2 * elem_w);
        };

        z3::expr result = getElem(mask[0]);
        for (unsigned i = 1; i < dst_n; ++i)
          result = z3::concat(getElem(mask[i]), result);

        value_map[&I] = own(result);
        continue;
      }
      value_map[&I] = own(translateValue(&I, value_map, state_array));
      continue;
    }

    // ICmp.
    if (auto *IC = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
      auto lhs = translateValue(IC->getOperand(0), value_map, state_array);
      auto rhs = translateValue(IC->getOperand(1), value_map, state_array);

      unsigned lw = lhs.get_sort().bv_size();
      unsigned rw = rhs.get_sort().bv_size();
      if (lw != rw) {
        if (lw > rw)
          rhs = z3::zext(rhs, lw - rw);
        else
          lhs = z3::zext(lhs, rw - lw);
      }

      z3::expr cond(ctx_);
      switch (IC->getPredicate()) {
        case llvm::CmpInst::ICMP_EQ:  cond = (lhs == rhs); break;
        case llvm::CmpInst::ICMP_NE:  cond = (lhs != rhs); break;
        case llvm::CmpInst::ICMP_UGT: cond = z3::ugt(lhs, rhs); break;
        case llvm::CmpInst::ICMP_UGE: cond = z3::uge(lhs, rhs); break;
        case llvm::CmpInst::ICMP_ULT: cond = z3::ult(lhs, rhs); break;
        case llvm::CmpInst::ICMP_ULE: cond = z3::ule(lhs, rhs); break;
        case llvm::CmpInst::ICMP_SGT: cond = (lhs > rhs); break;
        case llvm::CmpInst::ICMP_SGE: cond = (lhs >= rhs); break;
        case llvm::CmpInst::ICMP_SLT: cond = (lhs < rhs); break;
        case llvm::CmpInst::ICMP_SLE: cond = (lhs <= rhs); break;
        default: cond = ctx_.bool_val(false); break;
      }
      auto result = z3::ite(cond, ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      value_map[&I] = own(result);
      continue;
    }

    // Select.
    if (auto *Sel = llvm::dyn_cast<llvm::SelectInst>(&I)) {
      auto cond = translateValue(Sel->getCondition(), value_map, state_array);
      auto tv = translateValue(Sel->getTrueValue(), value_map, state_array);
      auto fv = translateValue(Sel->getFalseValue(), value_map, state_array);

      unsigned tw = tv.get_sort().bv_size();
      unsigned fw = fv.get_sort().bv_size();
      if (tw != fw) {
        if (tw > fw)
          fv = z3::zext(fv, tw - fw);
        else
          tv = z3::zext(tv, fw - tw);
      }

      z3::expr cond_bool(ctx_);
      if (cond.get_sort().is_bv())
        cond_bool = (cond == ctx_.bv_val(1, cond.get_sort().bv_size()));
      else
        cond_bool = cond;

      value_map[&I] = own(z3::ite(cond_bool, tv, fv));
      continue;
    }

    // Return.
    if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
      if (RI->getReturnValue()) {
        unsigned w = getBitWidth(RI->getReturnValue()->getType());
        ret_val = translateValue(RI->getReturnValue(), value_map, state_array);
        if (ret_val.get_sort().bv_size() != w) {
          if (ret_val.get_sort().bv_size() > w)
            ret_val = ret_val.extract(w - 1, 0);
          else
            ret_val = z3::zext(ret_val, w - ret_val.get_sort().bv_size());
        }
      }
      continue;
    }

    // GEP.
    if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I)) {
      llvm::APInt ap(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap)) {
        auto base = translateValue(GEP->getPointerOperand(), value_map,
                                    state_array);
        auto offset_val = ctx_.bv_val(ap.getZExtValue(), 64);
        value_map[&I] = own(base + offset_val);
      } else {
        value_map[&I] = own(translateValue(&I, value_map, state_array));
      }
      continue;
    }

    // Alloca.
    if (llvm::isa<llvm::AllocaInst>(&I)) {
      auto e = ctx_.bv_const(
          ("alloca_" + std::to_string(var_counter_++)).c_str(), 64);
      value_map[&I] = own(e);
      continue;
    }

    // PHI nodes — handled in encodeFunction.
    if (llvm::isa<llvm::PHINode>(&I))
      continue;

    // Branch — handled in encodeFunction.
    if (llvm::isa<llvm::BranchInst>(&I))
      continue;

    // Call — opaque.
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (!CI->getType()->isVoidTy()) {
        unsigned w = getBitWidth(CI->getType());
        auto e = ctx_.bv_const(
            ("call_" + std::to_string(var_counter_++)).c_str(), w);
        value_map[&I] = own(e);
      }
      continue;
    }
  }

  return state_array;
}

z3::expr TranslationValidator::encodeFunction(llvm::Function &F,
                                               z3::expr state_array,
                                               z3::expr &ret_val) {
  llvm::DenseMap<llvm::Value *, z3::expr *> value_map;

  // Map arg0 to State pointer base address only if it's a pointer type.
  if (F.arg_size() > 0 && F.getArg(0)->getType()->isPointerTy())
    value_map[F.getArg(0)] = own(ctx_.bv_val(0, 64));

  if (F.size() == 1)
    return encodeBlock(F.getEntryBlock(), state_array, ret_val, value_map);

  // Multi-block: RPO traversal with path conditions for loop-free CFGs.
  llvm::SmallVector<llvm::BasicBlock *, 16> rpo_order;
  {
    llvm::ReversePostOrderTraversal<llvm::Function *> RPOT(&F);
    for (auto *BB : RPOT)
      rpo_order.push_back(BB);
  }

  llvm::DenseMap<llvm::BasicBlock *, unsigned> rpo_index;
  for (unsigned i = 0; i < rpo_order.size(); ++i)
    rpo_index[rpo_order[i]] = i;

  bool has_backedge = false;
  for (auto *BB : rpo_order) {
    for (auto *Succ : llvm::successors(BB)) {
      if (rpo_index.count(Succ) && rpo_index[Succ] <= rpo_index[BB]) {
        has_backedge = true;
        break;
      }
    }
    if (has_backedge) break;
  }

  if (has_backedge) {
    z3::expr current_state = state_array;
    for (auto &BB : F)
      current_state = encodeBlock(BB, current_state, ret_val, value_map);
    return current_state;
  }

  // Per-block: post-encoding state and path condition.
  struct BlockInfo {
    z3::expr post_state;
    z3::expr path_cond;
    BlockInfo(z3::expr s, z3::expr pc) : post_state(s), path_cond(pc) {}
  };
  llvm::DenseMap<llvm::BasicBlock *, BlockInfo *> block_info;
  std::vector<std::unique_ptr<BlockInfo>> bi_storage;

  auto make_bi = [&](z3::expr s, z3::expr pc) -> BlockInfo * {
    auto p = std::make_unique<BlockInfo>(s, pc);
    auto *ptr = p.get();
    bi_storage.push_back(std::move(p));
    return ptr;
  };

  z3::expr final_state = state_array;

  for (auto *BB : rpo_order) {
    // Merge incoming states for non-entry blocks.
    z3::expr block_state = state_array;
    z3::expr block_pc = ctx_.bool_val(BB == &F.getEntryBlock());

    if (BB != &F.getEntryBlock()) {
      // Collect predecessors that have been encoded.
      bool first = true;
      for (auto *Pred : llvm::predecessors(BB)) {
        auto it = block_info.find(Pred);
        if (it == block_info.end()) continue;

        auto &pi = *it->second;

        // Determine the edge condition from Pred to BB.
        z3::expr edge_cond = pi.path_cond;
        if (auto *br = llvm::dyn_cast<llvm::BranchInst>(
                Pred->getTerminator())) {
          if (br->isConditional()) {
            auto cond = translateValue(br->getCondition(), value_map,
                                        pi.post_state);
            z3::expr cond_bool(ctx_);
            if (cond.get_sort().is_bv())
              cond_bool = (cond == ctx_.bv_val(1, cond.get_sort().bv_size()));
            else
              cond_bool = cond;

            if (br->getSuccessor(0) == BB)
              edge_cond = (pi.path_cond && cond_bool);
            else
              edge_cond = (pi.path_cond && !cond_bool);
          }
        }

        if (first) {
          block_state = pi.post_state;
          block_pc = edge_cond;
          first = false;
        } else {
          block_state = z3::ite(edge_cond, pi.post_state, block_state);
          block_pc = (block_pc || edge_cond);
        }
      }
    }

    // Encode PHI nodes.
    for (auto &I : *BB) {
      auto *PN = llvm::dyn_cast<llvm::PHINode>(&I);
      if (!PN) break;

      unsigned w = getBitWidth(PN->getType());
      z3::expr phi_val = ctx_.bv_const(
          ("phi_def_" + std::to_string(var_counter_++)).c_str(), w);

      bool first_phi = true;
      for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
        auto *inc_bb = PN->getIncomingBlock(i);
        auto *inc_val = PN->getIncomingValue(i);

        auto it = block_info.find(inc_bb);
        if (it == block_info.end()) continue;

        auto inc_z3 = translateValue(inc_val, value_map, it->second->post_state);
        if (inc_z3.get_sort().bv_size() != w) {
          if (inc_z3.get_sort().bv_size() > w)
            inc_z3 = inc_z3.extract(w - 1, 0);
          else
            inc_z3 = z3::zext(inc_z3, w - inc_z3.get_sort().bv_size());
        }

        // Compute edge condition.
        z3::expr edge_cond = it->second->path_cond;
        if (auto *br = llvm::dyn_cast<llvm::BranchInst>(
                inc_bb->getTerminator())) {
          if (br->isConditional()) {
            auto cond = translateValue(br->getCondition(), value_map,
                                        it->second->post_state);
            z3::expr cond_bool(ctx_);
            if (cond.get_sort().is_bv())
              cond_bool = (cond == ctx_.bv_val(1, cond.get_sort().bv_size()));
            else
              cond_bool = cond;

            if (br->getSuccessor(0) == BB)
              edge_cond = (it->second->path_cond && cond_bool);
            else
              edge_cond = (it->second->path_cond && !cond_bool);
          }
        }

        if (first_phi) {
          phi_val = inc_z3;
          first_phi = false;
        } else {
          phi_val = z3::ite(edge_cond, inc_z3, phi_val);
        }
      }
      value_map[PN] = own(phi_val);
    }

    // Encode block instructions.
    auto post_state = encodeBlock(*BB, block_state, ret_val, value_map);
    block_info[BB] = make_bi(post_state, block_pc);

    if (llvm::isa<llvm::ReturnInst>(BB->getTerminator()))
      final_state = post_state;
  }

  return final_state;
}

TranslationValidator::Result TranslationValidator::verify(llvm::Function &F) {
  Result result;
  result.equivalent = false;

  if (!snapshot_module_) {
    result.counterexample = "No snapshot taken before pass";
    return result;
  }

  auto *snapshot_fn = snapshot_module_->getFunction(snapshot_fn_name_);
  if (!snapshot_fn) {
    result.counterexample = "Snapshot function not found";
    return result;
  }

  owned_.clear();
  var_counter_ = 0;

  result.counterexample = "Z3 solver did not produce a result";

  try {
  auto addr_sort = ctx_.bv_sort(64);
  auto byte_sort = ctx_.bv_sort(8);
  auto state_before =
      ctx_.constant("state_init", ctx_.array_sort(addr_sort, byte_sort));

  // Encode pre-pass function.
  written_offsets_.clear();
  z3::expr ret_before = ctx_.bv_val(0, 64);
  auto final_state_before =
      encodeFunction(*snapshot_fn, state_before, ret_before);
  auto before_written = written_offsets_;

  // Encode post-pass function.
  written_offsets_.clear();
  var_counter_ = 0;
  z3::expr ret_after = ctx_.bv_val(0, 64);
  auto final_state_after = encodeFunction(F, state_before, ret_after);
  auto after_written = written_offsets_;

  {
    z3::solver solver(ctx_);

    // Determine offsets to compare.
    std::set<unsigned> offsets_to_compare;

    if (!compare_offsets_.empty()) {
      for (auto off : compare_offsets_)
        offsets_to_compare.insert(off);
    } else {
      for (auto off : before_written)
        if (off < max_state_offset_)
          offsets_to_compare.insert(off);
      for (auto off : after_written)
        if (off < max_state_offset_)
          offsets_to_compare.insert(off);

      if (offsets_to_compare.empty()) {
        for (unsigned off = 0; off < 128; ++off)
          offsets_to_compare.insert(off);
      }
    }

    z3::expr_vector inequalities(ctx_);
    for (unsigned off : offsets_to_compare) {
      auto addr = ctx_.bv_val(off, 64);
      auto byte_before = z3::select(final_state_before, addr);
      auto byte_after = z3::select(final_state_after, addr);
      inequalities.push_back(byte_before != byte_after);
    }

    // Compare return values.
    unsigned rb_w = ret_before.get_sort().bv_size();
    unsigned ra_w = ret_after.get_sort().bv_size();
    if (rb_w == ra_w) {
      inequalities.push_back(ret_before != ret_after);
    } else {
      unsigned w = std::max(rb_w, ra_w);
      auto rb = rb_w < w ? z3::zext(ret_before, w - rb_w) : ret_before;
      auto ra = ra_w < w ? z3::zext(ret_after, w - ra_w) : ret_after;
      inequalities.push_back(rb != ra);
    }

    auto any_diff = z3::mk_or(inequalities);
    solver.add(any_diff);

    auto check = solver.check();
    if (check == z3::unsat) {
      result.equivalent = true;
    } else if (check == z3::sat) {
      result.equivalent = false;
      auto model_str = solver.get_model().to_string();
      result.counterexample =
          model_str.empty() ? "SAT (functions differ)" : model_str;
    } else {
      result.equivalent = false;
      result.counterexample = "Z3 returned unknown";
    }
  }  // solver scope
  } catch (z3::exception &e) {
    result.equivalent = false;
    result.counterexample = std::string("Z3 exception: ") + e.msg();
  }

  return result;
}

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

#if OMILL_ENABLE_SOUPER

#include "omill/Utils/SouperZ3Translator.h"

#include <souper/Inst/Inst.h>

#include <llvm/Support/raw_ostream.h>

#include <cassert>

namespace omill {

SouperZ3Translator::SouperZ3Translator(z3::context &ctx) : ctx_(ctx) {}

void SouperZ3Translator::reset() {
  cache_.clear();
  owned_exprs_.clear();
  var_counter_ = 0;
}

z3::expr SouperZ3Translator::getVar(souper::Inst *var) {
  auto it = cache_.find(var);
  if (it != cache_.end())
    return *it->second;

  std::string name;
  if (!var->Name.empty()) {
    name = var->Name;
  } else {
    name = "v" + std::to_string(var_counter_++);
  }

  auto expr = std::make_unique<z3::expr>(ctx_.bv_const(name.c_str(), var->Width));
  auto *ptr = expr.get();
  cache_[var] = ptr;
  owned_exprs_.push_back(std::move(expr));
  return *ptr;
}

z3::expr SouperZ3Translator::translate(souper::Inst *inst) {
  assert(inst && "null Inst");

  // Check cache first (DAG dedup).
  auto it = cache_.find(inst);
  if (it != cache_.end())
    return *it->second;

  z3::expr result(ctx_);

  using K = souper::Inst::Kind;
  switch (inst->K) {
    case K::Const: {
      // Convert APInt to Z3 bitvector constant.
      llvm::SmallString<64> str;
      inst->Val.toStringUnsigned(str);
      result = ctx_.bv_val(str.c_str(), inst->Width);
      break;
    }

    case K::UntypedConst: {
      llvm::SmallString<64> str;
      inst->Val.toStringUnsigned(str);
      result = ctx_.bv_val(str.c_str(), inst->Width);
      break;
    }

    case K::Var:
    case K::Hole:
    case K::ReservedConst:
    case K::ReservedInst: {
      return getVar(inst);
    }

    case K::Phi: {
      // PHI nodes are treated as fresh unconstrained variables.
      // Path constraints from branch conditions will bound them.
      return getVar(inst);
    }

    // Binary arithmetic.
    case K::Add:
    case K::AddNSW:
    case K::AddNUW:
    case K::AddNW: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs + rhs;
      break;
    }

    case K::Sub:
    case K::SubNSW:
    case K::SubNUW:
    case K::SubNW: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs - rhs;
      break;
    }

    case K::Mul:
    case K::MulNSW:
    case K::MulNUW:
    case K::MulNW: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs * rhs;
      break;
    }

    case K::UDiv:
    case K::UDivExact: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::udiv(lhs, rhs);
      break;
    }

    case K::SDiv:
    case K::SDivExact: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs / rhs;  // Z3 default is signed division.
      break;
    }

    case K::URem: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::urem(lhs, rhs);
      break;
    }

    case K::SRem: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::srem(lhs, rhs);
      break;
    }

    // Bitwise.
    case K::And: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs & rhs;
      break;
    }

    case K::Or: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs | rhs;
      break;
    }

    case K::Xor: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs ^ rhs;
      break;
    }

    case K::Shl:
    case K::ShlNSW:
    case K::ShlNUW:
    case K::ShlNW: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::shl(lhs, rhs);
      break;
    }

    case K::LShr:
    case K::LShrExact: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::lshr(lhs, rhs);
      break;
    }

    case K::AShr:
    case K::AShrExact: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ashr(lhs, rhs);
      break;
    }

    // Conversions.
    case K::ZExt: {
      auto inner = translate(inst->Ops[0]);
      unsigned src_width = inst->Ops[0]->Width;
      unsigned ext = inst->Width - src_width;
      result = z3::zext(inner, ext);
      break;
    }

    case K::SExt: {
      auto inner = translate(inst->Ops[0]);
      unsigned src_width = inst->Ops[0]->Width;
      unsigned ext = inst->Width - src_width;
      result = z3::sext(inner, ext);
      break;
    }

    case K::Trunc: {
      auto inner = translate(inst->Ops[0]);
      result = inner.extract(inst->Width - 1, 0);
      break;
    }

    // Comparisons — produce 1-bit bitvector.
    case K::Eq: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ite(lhs == rhs, ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    case K::Ne: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ite(lhs != rhs, ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    case K::Ult: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ite(z3::ult(lhs, rhs), ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    case K::Slt: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ite(lhs < rhs, ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    case K::Ule: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ite(z3::ule(lhs, rhs), ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    case K::Sle: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = z3::ite(lhs <= rhs, ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    // Select (ternary).
    case K::Select: {
      auto cond = translate(inst->Ops[0]);
      auto tval = translate(inst->Ops[1]);
      auto fval = translate(inst->Ops[2]);
      result = z3::ite(cond == ctx_.bv_val(1, 1), tval, fval);
      break;
    }

    // Bit manipulation — model conservatively as uninterpreted variables.
    case K::CtPop:
    case K::BSwap:
    case K::Cttz:
    case K::Ctlz:
    case K::BitReverse:
    case K::FShl:
    case K::FShr:
    case K::Freeze: {
      return getVar(inst);
    }

    // Overflow intrinsics — extract the result (first element).
    case K::SAddWithOverflow:
    case K::SAddO:
    case K::UAddWithOverflow:
    case K::UAddO: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs + rhs;
      break;
    }

    case K::SSubWithOverflow:
    case K::SSubO:
    case K::USubWithOverflow:
    case K::USubO: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs - rhs;
      break;
    }

    case K::SMulWithOverflow:
    case K::SMulO:
    case K::UMulWithOverflow:
    case K::UMulO: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs * rhs;
      break;
    }

    // Saturating arithmetic.
    case K::SAddSat: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs + rhs;  // Approximate — Z3 doesn't have native saturation.
      break;
    }

    case K::UAddSat: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs + rhs;
      break;
    }

    case K::SSubSat: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs - rhs;
      break;
    }

    case K::USubSat: {
      auto lhs = translate(inst->Ops[0]);
      auto rhs = translate(inst->Ops[1]);
      result = lhs - rhs;
      break;
    }

    case K::ExtractValue: {
      // ExtractValue from aggregate — translate the source and hope for
      // the best.  Most commonly this extracts from overflow intrinsics.
      result = translate(inst->Ops[0]);
      break;
    }

    case K::None:
    default: {
      // Unknown — treat as fresh variable.
      return getVar(inst);
    }
  }

  // Cache the result.
  auto expr = std::make_unique<z3::expr>(result);
  auto *ptr = expr.get();
  cache_[inst] = ptr;
  owned_exprs_.push_back(std::move(expr));
  return *ptr;
}

}  // namespace omill

#endif  // OMILL_ENABLE_SOUPER

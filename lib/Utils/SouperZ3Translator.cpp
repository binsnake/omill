#if OMILL_ENABLE_Z3

#include "omill/Utils/SouperZ3Translator.h"

#include <llvm/ADT/SmallString.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"

#include <cassert>

namespace omill {

LLVMZ3Translator::LLVMZ3Translator(z3::context &ctx) : ctx_(ctx) {}

void LLVMZ3Translator::reset() {
  cache_.clear();
  owned_exprs_.clear();
  fresh_vars_.clear();
  var_counter_ = 0;
}

unsigned LLVMZ3Translator::getWidth(llvm::Value *val) const {
  auto *ty = val->getType();
  if (ty->isIntegerTy())
    return ty->getIntegerBitWidth();
  if (ty->isPointerTy())
    return 64;  // x86-64
  return 64;
}

z3::expr LLVMZ3Translator::cacheResult(llvm::Value *val, z3::expr result) {
  auto expr = std::make_unique<z3::expr>(result);
  auto *ptr = expr.get();
  cache_[val] = ptr;
  owned_exprs_.push_back(std::move(expr));
  return *ptr;
}

z3::expr LLVMZ3Translator::getFreshVar(llvm::Value *val) {
  auto it = cache_.find(val);
  if (it != cache_.end())
    return *it->second;

  std::string name;
  if (val->hasName()) {
    name = val->getName().str();
  } else {
    name = "v" + std::to_string(var_counter_++);
  }

  unsigned width = getWidth(val);
  auto result = cacheResult(val, ctx_.bv_const(name.c_str(), width));

  // Track this as a fresh variable for recursive resolution.
  fresh_vars_.push_back({val, cache_[val]});

  return result;
}

void LLVMZ3Translator::getUnresolvedVars(
    llvm::SmallVectorImpl<std::pair<llvm::Value *, z3::expr>> &out) const {
  for (auto &[val, expr_ptr] : fresh_vars_)
    out.push_back({val, *expr_ptr});
}

std::optional<z3::expr> LLVMZ3Translator::tryTranslatePHI(
    llvm::PHINode *phi) {
  unsigned n = phi->getNumIncomingValues();
  if (n == 0)
    return std::nullopt;

  // Check if all incoming values are constants.
  llvm::SmallVector<llvm::ConstantInt *, 8> constants;
  for (unsigned i = 0; i < n; ++i) {
    auto *ci = llvm::dyn_cast<llvm::ConstantInt>(phi->getIncomingValue(i));
    if (!ci)
      return std::nullopt;
    constants.push_back(ci);
  }

  // Build: ite(phi_sel == 0, c0, ite(phi_sel == 1, c1, ...))
  // where phi_sel is a fresh variable selecting among incoming values.
  unsigned width = getWidth(phi);

  // Deduplicate constants.
  llvm::SmallVector<uint64_t, 8> unique_vals;
  for (auto *ci : constants) {
    uint64_t v = ci->getZExtValue();
    bool found = false;
    for (auto u : unique_vals)
      if (u == v) { found = true; break; }
    if (!found)
      unique_vals.push_back(v);
  }

  if (unique_vals.size() == 1) {
    // All paths lead to the same constant.
    llvm::SmallString<80> str;
    llvm::APInt(width, unique_vals[0]).toStringUnsigned(str);
    return ctx_.bv_val(str.c_str(), width);
  }

  // Build OR of equalities: (result == c0) || (result == c1) || ...
  // We create a fresh variable and constrain it to be one of the constants.
  // But since Z3 doesn't support returning constrained vars directly, we
  // encode as a nested ITE with a selector variable.
  std::string sel_name = "phi_sel_" + std::to_string(var_counter_++);
  unsigned sel_bits = 1;
  while ((1u << sel_bits) < unique_vals.size())
    ++sel_bits;
  auto sel = ctx_.bv_const(sel_name.c_str(), sel_bits);

  // Build bottom-up: last value is the default.
  llvm::SmallString<80> str_last;
  llvm::APInt(width, unique_vals.back()).toStringUnsigned(str_last);
  z3::expr result = ctx_.bv_val(str_last.c_str(), width);
  for (int i = (int)unique_vals.size() - 2; i >= 0; --i) {
    llvm::SmallString<80> str_i;
    llvm::APInt(width, unique_vals[i]).toStringUnsigned(str_i);
    auto val_expr = ctx_.bv_val(str_i.c_str(), width);
    result = z3::ite(sel == ctx_.bv_val(i, sel_bits), val_expr, result);
  }

  // Bound the selector.
  // We store this as a "side constraint" by encoding it into the expression:
  // ite(sel < N, ite_chain, default_val) — but since the outer ITE already
  // handles all cases, the selector is implicitly bounded.

  return result;
}

z3::expr LLVMZ3Translator::translateICmp(llvm::ICmpInst *icmp) {
  auto lhs = translate(icmp->getOperand(0));
  auto rhs = translate(icmp->getOperand(1));

  switch (icmp->getPredicate()) {
    case llvm::ICmpInst::ICMP_EQ:
      return lhs == rhs;
    case llvm::ICmpInst::ICMP_NE:
      return lhs != rhs;
    case llvm::ICmpInst::ICMP_ULT:
      return z3::ult(lhs, rhs);
    case llvm::ICmpInst::ICMP_ULE:
      return z3::ule(lhs, rhs);
    case llvm::ICmpInst::ICMP_UGT:
      return z3::ugt(lhs, rhs);
    case llvm::ICmpInst::ICMP_UGE:
      return z3::uge(lhs, rhs);
    case llvm::ICmpInst::ICMP_SLT:
      return lhs < rhs;
    case llvm::ICmpInst::ICMP_SLE:
      return lhs <= rhs;
    case llvm::ICmpInst::ICMP_SGT:
      return lhs > rhs;
    case llvm::ICmpInst::ICMP_SGE:
      return lhs >= rhs;
    default:
      return ctx_.bool_val(true);
  }
}

z3::expr LLVMZ3Translator::translate(llvm::Value *val) {
  assert(val && "null Value");

  // Check cache.
  auto it = cache_.find(val);
  if (it != cache_.end())
    return *it->second;

  unsigned width = getWidth(val);

  // Constants.
  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
    llvm::SmallString<80> str;
    ci->getValue().toStringUnsigned(str);
    return cacheResult(val, ctx_.bv_val(str.c_str(), width));
  }

  // Poison/undef → fresh variable.
  if (llvm::isa<llvm::PoisonValue>(val) || llvm::isa<llvm::UndefValue>(val))
    return getFreshVar(val);

  // Instructions.
  auto *inst = llvm::dyn_cast<llvm::Instruction>(val);
  if (!inst)
    return getFreshVar(val);

  z3::expr result(ctx_);

  switch (inst->getOpcode()) {
    // Binary arithmetic.
    case llvm::Instruction::Add: {
      result = translate(inst->getOperand(0)) + translate(inst->getOperand(1));
      break;
    }
    case llvm::Instruction::Sub: {
      result = translate(inst->getOperand(0)) - translate(inst->getOperand(1));
      break;
    }
    case llvm::Instruction::Mul: {
      result = translate(inst->getOperand(0)) * translate(inst->getOperand(1));
      break;
    }
    case llvm::Instruction::UDiv: {
      result = z3::udiv(translate(inst->getOperand(0)),
                        translate(inst->getOperand(1)));
      break;
    }
    case llvm::Instruction::SDiv: {
      result =
          translate(inst->getOperand(0)) / translate(inst->getOperand(1));
      break;
    }
    case llvm::Instruction::URem: {
      result = z3::urem(translate(inst->getOperand(0)),
                        translate(inst->getOperand(1)));
      break;
    }
    case llvm::Instruction::SRem: {
      result = z3::srem(translate(inst->getOperand(0)),
                        translate(inst->getOperand(1)));
      break;
    }

    // Bitwise.
    case llvm::Instruction::And: {
      result = translate(inst->getOperand(0)) & translate(inst->getOperand(1));
      break;
    }
    case llvm::Instruction::Or: {
      result = translate(inst->getOperand(0)) | translate(inst->getOperand(1));
      break;
    }
    case llvm::Instruction::Xor: {
      result = translate(inst->getOperand(0)) ^ translate(inst->getOperand(1));
      break;
    }

    // Shifts.
    case llvm::Instruction::Shl: {
      result = z3::shl(translate(inst->getOperand(0)),
                       translate(inst->getOperand(1)));
      break;
    }
    case llvm::Instruction::LShr: {
      result = z3::lshr(translate(inst->getOperand(0)),
                        translate(inst->getOperand(1)));
      break;
    }
    case llvm::Instruction::AShr: {
      result = z3::ashr(translate(inst->getOperand(0)),
                        translate(inst->getOperand(1)));
      break;
    }

    // Conversions.
    case llvm::Instruction::ZExt: {
      auto inner = translate(inst->getOperand(0));
      unsigned src_width = getWidth(inst->getOperand(0));
      result = z3::zext(inner, width - src_width);
      break;
    }
    case llvm::Instruction::SExt: {
      auto inner = translate(inst->getOperand(0));
      unsigned src_width = getWidth(inst->getOperand(0));
      result = z3::sext(inner, width - src_width);
      break;
    }
    case llvm::Instruction::Trunc: {
      auto inner = translate(inst->getOperand(0));
      result = inner.extract(width - 1, 0);
      break;
    }

    // Integer comparison → 1-bit bitvector.
    case llvm::Instruction::ICmp: {
      auto *icmp = llvm::cast<llvm::ICmpInst>(inst);
      auto lhs = translate(icmp->getOperand(0));
      auto rhs = translate(icmp->getOperand(1));
      z3::expr cond(ctx_);

      switch (icmp->getPredicate()) {
        case llvm::ICmpInst::ICMP_EQ:
          cond = (lhs == rhs);
          break;
        case llvm::ICmpInst::ICMP_NE:
          cond = (lhs != rhs);
          break;
        case llvm::ICmpInst::ICMP_ULT:
          cond = z3::ult(lhs, rhs);
          break;
        case llvm::ICmpInst::ICMP_ULE:
          cond = z3::ule(lhs, rhs);
          break;
        case llvm::ICmpInst::ICMP_UGT:
          cond = z3::ugt(lhs, rhs);
          break;
        case llvm::ICmpInst::ICMP_UGE:
          cond = z3::uge(lhs, rhs);
          break;
        case llvm::ICmpInst::ICMP_SLT:
          cond = (lhs < rhs);
          break;
        case llvm::ICmpInst::ICMP_SLE:
          cond = (lhs <= rhs);
          break;
        case llvm::ICmpInst::ICMP_SGT:
          cond = (lhs > rhs);
          break;
        case llvm::ICmpInst::ICMP_SGE:
          cond = (lhs >= rhs);
          break;
        default:
          cond = ctx_.bool_val(true);
          break;
      }
      result = z3::ite(cond, ctx_.bv_val(1, 1), ctx_.bv_val(0, 1));
      break;
    }

    // Select.
    case llvm::Instruction::Select: {
      auto *sel = llvm::cast<llvm::SelectInst>(inst);
      auto cond = translate(sel->getCondition());
      auto tval = translate(sel->getTrueValue());
      auto fval = translate(sel->getFalseValue());
      // Condition is i1 → 1-bit bv.
      result = z3::ite(cond == ctx_.bv_val(1, 1), tval, fval);
      break;
    }

    // IntToPtr / PtrToInt — pass through the integer operand.
    case llvm::Instruction::IntToPtr: {
      result = translate(inst->getOperand(0));
      break;
    }
    case llvm::Instruction::PtrToInt: {
      result = translate(inst->getOperand(0));
      break;
    }

    // PHI nodes — try constant resolution, else fresh variable.
    case llvm::Instruction::PHI: {
      auto *phi = llvm::cast<llvm::PHINode>(inst);
      if (auto phi_result = tryTranslatePHI(phi)) {
        return cacheResult(val, *phi_result);
      }
      return getFreshVar(val);
    }

    // Loads — try memory dereference if address is a constant.
    case llvm::Instruction::Load: {
      auto *load = llvm::cast<llvm::LoadInst>(inst);
      if (binary_mem_) {
        // Try to resolve the address to a constant.
        auto *ptr = load->getPointerOperand();
        // Strip inttoptr.
        llvm::Value *addr_val = nullptr;
        if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
          addr_val = itp->getOperand(0);
        else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
          if (ce->getOpcode() == llvm::Instruction::IntToPtr)
            addr_val = ce->getOperand(0);
        }

        if (addr_val) {
          if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(addr_val)) {
            uint64_t addr = ci->getZExtValue();
            unsigned byte_size = width / 8;
            if (auto mem_val = binary_mem_->readInt(addr, byte_size)) {
              llvm::SmallString<80> str;
              llvm::APInt(width, *mem_val).toStringUnsigned(str);
              return cacheResult(val, ctx_.bv_val(str.c_str(), width));
            }
          }
        }
      }
      return getFreshVar(val);
    }

    // Calls → fresh variable.
    case llvm::Instruction::Call:
    default: {
      return getFreshVar(val);
    }
  }

  return cacheResult(val, result);
}

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

#if OMILL_ENABLE_Z3

#include "omill/Utils/SouperZ3Translator.h"

#include <llvm/ADT/SmallString.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>

#include <cassert>

namespace omill {

LLVMZ3Translator::LLVMZ3Translator(z3::context &ctx) : ctx_(ctx) {}

void LLVMZ3Translator::reset() {
  cache_.clear();
  owned_exprs_.clear();
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
  return cacheResult(val, ctx_.bv_const(name.c_str(), width));
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

    // PHI nodes → fresh variable (constrained by path).
    case llvm::Instruction::PHI:
    // Loads → fresh variable (value comes from memory).
    case llvm::Instruction::Load:
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

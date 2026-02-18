#include "omill/Simplifier/LLVMTranslator.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Debug.h>

#define DEBUG_TYPE "eqsat-translator"

namespace omill {

LLVMTranslator::LLVMTranslator() : ctx_(CreateContext()) {}

LLVMTranslator::~LLVMTranslator() {
  DestroyContext(ctx_);
}

void LLVMTranslator::reset() {
  value_to_ast_.clear();
  reconstruct_cache_.clear();
  symbols_by_id_.clear();
  next_symbol_id_ = 0;
}

uint8_t LLVMTranslator::getWidth(llvm::Value *V) {
  auto *ty = V->getType();
  if (ty->isIntegerTy())
    return static_cast<uint8_t>(ty->getIntegerBitWidth());
  return 0;
}

EqSatAstIdx LLVMTranslator::makeSymbol(llvm::Value *V) {
  unsigned id = next_symbol_id_++;
  // Use a simple name like "v0", "v1", etc.
  std::string name = "v" + std::to_string(id);
  uint8_t w = getWidth(V);
  if (w == 0) w = 64;  // fallback for non-integer types

  EqSatAstIdx idx = ContextSymbol(ctx_, name.c_str(), w);
  ContextSetImutData(ctx_, idx, static_cast<uint64_t>(id));

  if (id >= symbols_by_id_.size())
    symbols_by_id_.resize(id + 1, nullptr);
  symbols_by_id_[id] = V;

  value_to_ast_[V] = idx;
  return idx;
}

EqSatAstIdx LLVMTranslator::translate(llvm::Value *V, unsigned max_depth) {
  // Check cache first.
  auto it = value_to_ast_.find(V);
  if (it != value_to_ast_.end())
    return it->second;

  // Non-integer types are opaque.
  if (!V->getType()->isIntegerTy())
    return makeSymbol(V);

  // Wide integers (i128 from XMM, etc.) exceed EqSat's uint64_t constant range.
  if (V->getType()->getIntegerBitWidth() > 64)
    return makeSymbol(V);

  // Depth limit → opaque.
  if (max_depth == 0)
    return makeSymbol(V);

  uint8_t w = getWidth(V);

  // Constants.
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    EqSatAstIdx idx = ContextConstant(ctx_, CI->getZExtValue(), w);
    value_to_ast_[V] = idx;
    return idx;
  }

  // Binary operators.
  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    unsigned next = max_depth - 1;

    switch (BO->getOpcode()) {
      case llvm::Instruction::Add: {
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto idx = ContextAdd(ctx_, a, b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::Sub: {
        // sub a, b → add(a, add(neg(b), 1))  i.e. a + (~b + 1) = a - b
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto neg_b = ContextNeg(ctx_, b);
        auto one = ContextConstant(ctx_, 1, w);
        auto minus_b = ContextAdd(ctx_, neg_b, one);
        auto idx = ContextAdd(ctx_, a, minus_b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::Mul: {
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto idx = ContextMul(ctx_, a, b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::And: {
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto idx = ContextAnd(ctx_, a, b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::Or: {
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto idx = ContextOr(ctx_, a, b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::Xor: {
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto idx = ContextXor(ctx_, a, b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::LShr: {
        auto a = translate(BO->getOperand(0), next);
        auto b = translate(BO->getOperand(1), next);
        auto idx = ContextLshr(ctx_, a, b);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::Shl: {
        // Constant shift → mul(a, 1 << C).
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
          uint64_t shift_amt = C->getZExtValue();
          if (shift_amt < w) {
            auto a = translate(BO->getOperand(0), next);
            auto mul_const =
                ContextConstant(ctx_, uint64_t(1) << shift_amt, w);
            auto idx = ContextMul(ctx_, a, mul_const);
            value_to_ast_[V] = idx;
            return idx;
          }
        }
        // Variable shift → opaque.
        return makeSymbol(V);
      }
      case llvm::Instruction::AShr:
        // Arithmetic shift right → opaque (no EqSat equivalent).
        return makeSymbol(V);
      default:
        return makeSymbol(V);
    }
  }

  // Cast instructions.
  if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V)) {
    unsigned next = max_depth - 1;
    switch (CI->getOpcode()) {
      case llvm::Instruction::ZExt: {
        auto src = translate(CI->getOperand(0), next);
        uint8_t target_w = static_cast<uint8_t>(
            CI->getType()->getIntegerBitWidth());
        auto idx = ContextZext(ctx_, src, target_w);
        value_to_ast_[V] = idx;
        return idx;
      }
      case llvm::Instruction::Trunc: {
        auto src = translate(CI->getOperand(0), next);
        uint8_t target_w = static_cast<uint8_t>(
            CI->getType()->getIntegerBitWidth());
        auto idx = ContextTrunc(ctx_, src, target_w);
        value_to_ast_[V] = idx;
        return idx;
      }
      default:
        // sext and others → opaque.
        return makeSymbol(V);
    }
  }

  // Everything else (args, loads, PHIs, calls) → opaque symbol.
  return makeSymbol(V);
}

llvm::Value *LLVMTranslator::reconstruct(EqSatAstIdx idx,
                                          llvm::IRBuilder<> &B) {
  // Check cache.
  auto it = reconstruct_cache_.find(idx.idx);
  if (it != reconstruct_cache_.end())
    return it->second;

  uint8_t opcode = ContextGetOpcode(ctx_, idx);
  llvm::Value *result = nullptr;

  switch (opcode) {
    case EQSAT_OP_CONSTANT: {
      uint64_t val = ContextGetConstantValue(ctx_, idx);
      uint8_t w = ContextGetWidth(ctx_, idx);
      auto *ty = llvm::IntegerType::get(B.getContext(), w);
      result = llvm::ConstantInt::get(ty, val);
      break;
    }
    case EQSAT_OP_SYMBOL: {
      uint64_t id = ContextGetImutData(ctx_, idx);
      assert(id < symbols_by_id_.size() && "Symbol ID out of range");
      result = symbols_by_id_[static_cast<unsigned>(id)];
      break;
    }
    case EQSAT_OP_ADD: {
      auto *lhs = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *rhs = reconstruct(ContextGetOp1(ctx_, idx), B);
      result = B.CreateAdd(lhs, rhs);
      break;
    }
    case EQSAT_OP_MUL: {
      auto *lhs = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *rhs = reconstruct(ContextGetOp1(ctx_, idx), B);
      result = B.CreateMul(lhs, rhs);
      break;
    }
    case EQSAT_OP_AND: {
      auto *lhs = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *rhs = reconstruct(ContextGetOp1(ctx_, idx), B);
      result = B.CreateAnd(lhs, rhs);
      break;
    }
    case EQSAT_OP_OR: {
      auto *lhs = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *rhs = reconstruct(ContextGetOp1(ctx_, idx), B);
      result = B.CreateOr(lhs, rhs);
      break;
    }
    case EQSAT_OP_XOR: {
      auto *lhs = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *rhs = reconstruct(ContextGetOp1(ctx_, idx), B);
      result = B.CreateXor(lhs, rhs);
      break;
    }
    case EQSAT_OP_NEG: {
      // Bitwise NOT: ~x = xor x, -1
      auto *operand = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *neg_one = llvm::ConstantInt::getSigned(operand->getType(), -1);
      result = B.CreateXor(operand, neg_one);
      break;
    }
    case EQSAT_OP_LSHR: {
      auto *lhs = reconstruct(ContextGetOp0(ctx_, idx), B);
      auto *rhs = reconstruct(ContextGetOp1(ctx_, idx), B);
      result = B.CreateLShr(lhs, rhs);
      break;
    }
    case EQSAT_OP_ZEXT: {
      auto *operand = reconstruct(ContextGetOp0(ctx_, idx), B);
      uint8_t w = ContextGetWidth(ctx_, idx);
      auto *target_ty = llvm::IntegerType::get(B.getContext(), w);
      result = B.CreateZExt(operand, target_ty);
      break;
    }
    case EQSAT_OP_TRUNC: {
      auto *operand = reconstruct(ContextGetOp0(ctx_, idx), B);
      uint8_t w = ContextGetWidth(ctx_, idx);
      auto *target_ty = llvm::IntegerType::get(B.getContext(), w);
      result = B.CreateTrunc(operand, target_ty);
      break;
    }
    case EQSAT_OP_POW: {
      // Try to fold: if both operands are constants, compute at compile time.
      auto op0 = ContextGetOp0(ctx_, idx);
      auto op1 = ContextGetOp1(ctx_, idx);
      uint8_t op0_opc = ContextGetOpcode(ctx_, op0);
      uint8_t op1_opc = ContextGetOpcode(ctx_, op1);

      if (op0_opc == EQSAT_OP_CONSTANT && op1_opc == EQSAT_OP_CONSTANT) {
        uint64_t base = ContextGetConstantValue(ctx_, op0);
        uint64_t exp = ContextGetConstantValue(ctx_, op1);
        uint64_t val = Pow(base, exp);
        uint8_t w = ContextGetWidth(ctx_, idx);
        auto *ty = llvm::IntegerType::get(B.getContext(), w);
        result = llvm::ConstantInt::get(ty, val);
      } else if (op0_opc == EQSAT_OP_CONSTANT &&
                 ContextGetConstantValue(ctx_, op0) == 2) {
        // 2^exp → shl(1, exp)
        auto *exp_v = reconstruct(op1, B);
        auto *one = llvm::ConstantInt::get(exp_v->getType(), 1);
        result = B.CreateShl(one, exp_v);
      } else {
        llvm_unreachable("Cannot reconstruct non-constant Pow");
      }
      break;
    }
    default:
      llvm_unreachable("Unknown EqSat opcode during reconstruction");
  }

  reconstruct_cache_[idx.idx] = result;
  return result;
}

llvm::Value *LLVMTranslator::simplify(llvm::Value *V, llvm::IRBuilder<> &B,
                                       unsigned max_depth) {
  EqSatAstIdx original = translate(V, max_depth);
  EqSatAstIdx simplified = ContextRecursiveSimplify(ctx_, original);

  // No change.
  if (simplified.idx == original.idx)
    return nullptr;

  // Check cost improvement.
  uint32_t orig_cost = ContextGetCost(ctx_, original);
  uint32_t simp_cost = ContextGetCost(ctx_, simplified);
  if (simp_cost >= orig_cost)
    return nullptr;

  LLVM_DEBUG(llvm::dbgs() << "EqSat: cost " << orig_cost << " → " << simp_cost
                          << "\n");

  return reconstruct(simplified, B);
}

}  // namespace omill

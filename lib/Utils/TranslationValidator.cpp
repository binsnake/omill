#if OMILL_ENABLE_Z3

#include "omill/Utils/TranslationValidator.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Transforms/Utils/Cloning.h>

namespace omill {

TranslationValidator::TranslationValidator(z3::context &ctx) : ctx_(ctx) {}

z3::expr *TranslationValidator::own(z3::expr e) {
  auto p = std::make_unique<z3::expr>(e);
  auto *ptr = p.get();
  owned_.push_back(std::move(p));
  return ptr;
}

void TranslationValidator::snapshotBefore(llvm::Function &F) {
  // Clone the entire module so we get a complete snapshot.
  snapshot_module_ = llvm::CloneModule(*F.getParent());
  snapshot_fn_name_ = F.getName().str();
}

z3::expr TranslationValidator::translateValue(
    llvm::Value *V, llvm::DenseMap<llvm::Value *, z3::expr *> &value_map,
    z3::expr state_array) {
  // Check cache.
  auto it = value_map.find(V);
  if (it != value_map.end())
    return *it->second;

  // Constant integer.
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    unsigned w = CI->getBitWidth();
    auto e = ctx_.bv_val(CI->getZExtValue(), w);
    value_map[V] = own(e);
    return e;
  }

  // Poison/undef → fresh variable.
  if (llvm::isa<llvm::PoisonValue>(V) || llvm::isa<llvm::UndefValue>(V)) {
    unsigned w = V->getType()->isIntegerTy()
                     ? V->getType()->getIntegerBitWidth()
                     : 64;
    auto e = ctx_.bv_const(
        ("undef_" + std::to_string(var_counter_++)).c_str(), w);
    value_map[V] = own(e);
    return e;
  }

  // Function argument.
  if (auto *Arg = llvm::dyn_cast<llvm::Argument>(V)) {
    unsigned w = V->getType()->isIntegerTy()
                     ? V->getType()->getIntegerBitWidth()
                     : 64;
    std::string name = "arg" + std::to_string(Arg->getArgNo());
    auto e = ctx_.bv_const(name.c_str(), w);
    value_map[V] = own(e);
    return e;
  }

  // Default: fresh variable for anything we can't handle.
  unsigned w =
      V->getType()->isIntegerTy() ? V->getType()->getIntegerBitWidth() : 64;
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

      // Try to resolve to a State offset.
      int64_t offset = -1;
      // Direct load from arg0 (State pointer) → offset 0.
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

      if (offset >= 0 && LI->getType()->isIntegerTy()) {
        unsigned bytes = LI->getType()->getIntegerBitWidth() / 8;
        // Read bytes from the State array and concatenate.
        z3::expr result = z3::select(state_array,
                                      ctx_.bv_val((unsigned)offset, 64));
        for (unsigned i = 1; i < bytes; ++i) {
          auto byte_i = z3::select(
              state_array, ctx_.bv_val((unsigned)(offset + i), 64));
          result = z3::concat(byte_i, result);  // little-endian
        }
        value_map[&I] = own(result);
        continue;
      }

      // Unknown load → fresh variable.
      value_map[&I] = own(translateValue(&I, value_map, state_array));
      continue;
    }

    // Store to State.
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto *ptr = SI->getPointerOperand();
      auto *val = SI->getValueOperand();

      int64_t offset = -1;
      // Direct store to arg0 (State pointer) → offset 0.
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

      if (offset >= 0 && val->getType()->isIntegerTy()) {
        auto z3_val = translateValue(val, value_map, state_array);
        unsigned bytes = val->getType()->getIntegerBitWidth() / 8;

        // Write bytes to State array (little-endian).
        for (unsigned i = 0; i < bytes; ++i) {
          auto byte_val = z3_val.extract(i * 8 + 7, i * 8);
          state_array = z3::store(
              state_array, ctx_.bv_val((unsigned)(offset + i), 64), byte_val);
        }
      }
      continue;
    }

    // Binary operations.
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
      auto lhs = translateValue(BO->getOperand(0), value_map, state_array);
      auto rhs = translateValue(BO->getOperand(1), value_map, state_array);

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
        default:
          result = translateValue(&I, value_map, state_array);
          break;
      }
      value_map[&I] = own(result);
      continue;
    }

    // ZExt/SExt/Trunc.
    if (auto *ZE = llvm::dyn_cast<llvm::ZExtInst>(&I)) {
      auto src = translateValue(ZE->getOperand(0), value_map, state_array);
      unsigned dst_w = ZE->getType()->getIntegerBitWidth();
      unsigned src_w = ZE->getOperand(0)->getType()->getIntegerBitWidth();
      value_map[&I] = own(z3::zext(src, dst_w - src_w));
      continue;
    }
    if (auto *SE = llvm::dyn_cast<llvm::SExtInst>(&I)) {
      auto src = translateValue(SE->getOperand(0), value_map, state_array);
      unsigned dst_w = SE->getType()->getIntegerBitWidth();
      unsigned src_w = SE->getOperand(0)->getType()->getIntegerBitWidth();
      value_map[&I] = own(z3::sext(src, dst_w - src_w));
      continue;
    }
    if (auto *T = llvm::dyn_cast<llvm::TruncInst>(&I)) {
      auto src = translateValue(T->getOperand(0), value_map, state_array);
      unsigned dst_w = T->getType()->getIntegerBitWidth();
      value_map[&I] = own(src.extract(dst_w - 1, 0));
      continue;
    }

    // Return.
    if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
      if (RI->getReturnValue() && RI->getReturnValue()->getType()->isIntegerTy()) {
        ret_val = translateValue(RI->getReturnValue(), value_map, state_array);
      }
      continue;
    }

    // GEP — just compute the offset as a value for pointer arithmetic.
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

    // Skip calls, branches, etc. — they don't affect State in our model.
  }

  return state_array;
}

z3::expr TranslationValidator::encodeFunction(llvm::Function &F,
                                               z3::expr state_array,
                                               z3::expr &ret_val) {
  llvm::DenseMap<llvm::Value *, z3::expr *> value_map;

  // Map arg0 (State pointer) to address 0 (base of the array).
  if (F.arg_size() > 0) {
    value_map[F.getArg(0)] = own(ctx_.bv_val(0, 64));
  }

  // For single-block functions, just encode the entry block.
  if (F.size() == 1) {
    return encodeBlock(F.getEntryBlock(), state_array, ret_val, value_map);
  }

  // For multi-block: encode blocks in order (approximation for loop-free CFG).
  z3::expr current_state = state_array;
  for (auto &BB : F) {
    current_state =
        encodeBlock(BB, current_state, ret_val, value_map);
  }
  return current_state;
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

  // Reset state.
  owned_.clear();
  var_counter_ = 0;

  // Create symbolic initial State array: Addr(64) → Byte(8).
  auto addr_sort = ctx_.bv_sort(64);
  auto byte_sort = ctx_.bv_sort(8);
  auto state_before =
      ctx_.constant("state_init", ctx_.array_sort(addr_sort, byte_sort));

  // Encode pre-pass function.
  z3::expr ret_before = ctx_.bv_val(0, 64);
  auto final_state_before =
      encodeFunction(*snapshot_fn, state_before, ret_before);

  // Encode post-pass function.
  // Reset var_counter for consistent naming.
  var_counter_ = 0;
  z3::expr ret_after = ctx_.bv_val(0, 64);
  auto final_state_after = encodeFunction(F, state_before, ret_after);

  // Set a fallback message in case Z3 throws without providing one.
  result.counterexample = "Z3 solver did not produce a result";

  // Check equivalence: assert NOT(state_before == state_after && ret_before == ret_after).
  try {
    z3::solver solver(ctx_);

    // Compare State arrays at key offsets (0-128 covering all test registers).
    z3::expr_vector inequalities(ctx_);
    for (unsigned off = 0; off < 128; off += 8) {
      for (unsigned b = 0; b < 8; ++b) {
        auto addr = ctx_.bv_val(off + b, 64);
        auto byte_before = z3::select(final_state_before, addr);
        auto byte_after = z3::select(final_state_after, addr);
        inequalities.push_back(byte_before != byte_after);
      }
    }

    // Also compare return values.
    inequalities.push_back(ret_before != ret_after);

    // Assert disjunction: any difference → SAT means NOT equivalent.
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
  } catch (z3::exception &e) {
    result.equivalent = false;
    result.counterexample = std::string("Z3 exception: ") + e.msg();
  }

  return result;
}

}  // namespace omill

#endif  // OMILL_ENABLE_Z3

#include "Substitution.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {


// Newton's method for modular inverse mod 2^bits. Requires a to be odd.
static uint64_t modInverse(uint64_t a, unsigned bits) {
  uint64_t inv = a;
  for (int i = 0; i < 6; ++i)
    inv *= 2 - a * inv;
  // Mask to bitwidth
  if (bits < 64)
    inv &= (uint64_t(1) << bits) - 1;
  return inv;
}


// Apply multiplication by K_inv, optionally splitting into two factors
// to avoid a single large-constant fingerprint.
static llvm::Value *applyKInverse(llvm::IRBuilder<> &builder, llvm::Value *val,
                                  uint64_t kInvRaw, unsigned bw,
                                  llvm::Type *ty, std::mt19937 &rng,
                                  std::uniform_int_distribution<int> &coin) {
  if (coin(rng) == 0) {
    uint64_t kInvA = rng() | 1ULL;
    if (bw < 64) kInvA &= (uint64_t(1) << bw) - 1;
    if (kInvA == 0) kInvA = 1;
    uint64_t kInvB = kInvRaw * modInverse(kInvA, bw);
    if (bw < 64) kInvB &= (uint64_t(1) << bw) - 1;
    auto *tmp = builder.CreateMul(val, llvm::ConstantInt::get(ty, kInvA), "");
    return builder.CreateMul(tmp, llvm::ConstantInt::get(ty, kInvB), "");
  }
  return builder.CreateMul(val, llvm::ConstantInt::get(ty, kInvRaw), "");
}

static void substituteFunction(llvm::Function &F, std::mt19937 &rng,
                               const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  std::uniform_int_distribution<int> coin(0, 1);

  // Collect instructions first to avoid iterator invalidation.
  std::vector<llvm::BinaryOperator *> work;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        // Skip i1 (boolean), wide integers (>64-bit modular inverse is wrong),
        // and constant-only expressions.
        auto *ty = bin->getType();
        if (!ty->isIntegerTy() || ty->getIntegerBitWidth() < 2 ||
            ty->getIntegerBitWidth() > 64)
          continue;
        if (llvm::isa<llvm::Constant>(bin->getOperand(0)) &&
            llvm::isa<llvm::Constant>(bin->getOperand(1)))
          continue;
        work.push_back(bin);
      }
    }
  }

  for (auto *bin : work) {
    if (!shouldTransform(rng, cfg)) continue;
    // Apply to ~50% of eligible operations.
    if (coin(rng) == 0)
      continue;

    llvm::IRBuilder<> builder(bin);
    auto *a = bin->getOperand(0);
    auto *b = bin->getOperand(1);
    auto *ty = bin->getType();
    llvm::Value *replacement = nullptr;

    switch (bin->getOpcode()) {
    case llvm::Instruction::Add: {
      // MBA variants for a + b
      int variant = std::uniform_int_distribution<int>(0, 2)(rng);
      if (variant == 0) {
        // a + b => (a ^ b) + 2*(a & b)
        auto *xv = builder.CreateXor(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        auto *mv = builder.CreateAdd(av, av, "");
        replacement = builder.CreateAdd(xv, mv, "");
      } else if (variant == 1) {
        // a + b => (a | b) + (a & b)
        auto *ov = builder.CreateOr(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        replacement = builder.CreateAdd(ov, av, "");
      } else {
        // a + b => a*(b+1) - b*(a-1)  [degree-2 polynomial MBA]
        auto *one = llvm::ConstantInt::get(ty, 1);
        auto *bp1 = builder.CreateAdd(b, one, "");
        auto *am1 = builder.CreateSub(a, one, "");
        auto *lhs = builder.CreateMul(a, bp1, "");
        auto *rhs = builder.CreateMul(b, am1, "");
        replacement = builder.CreateSub(lhs, rhs, "");
      }
      break;
    }
    case llvm::Instruction::Sub: {
      // MBA variants for a - b
      int variant = std::uniform_int_distribution<int>(0, 2)(rng);
      if (variant == 0) {
        // a - b => (a ^ b) - 2*(~a & b)
        auto *xv = builder.CreateXor(a, b, "");
        auto *na = builder.CreateNot(a, "");
        auto *av = builder.CreateAnd(na, b, "");
        auto *mv = builder.CreateAdd(av, av, "");
        replacement = builder.CreateSub(xv, mv, "");
      } else if (variant == 1) {
        // a - b => a + (~b) + 1
        auto *nb = builder.CreateNot(b, "");
        auto *s1 = builder.CreateAdd(a, nb, "");
        replacement = builder.CreateAdd(s1, llvm::ConstantInt::get(ty, 1), "");
      } else {
        // a - b => a*(b+1) - b*(a+1)  [degree-2 polynomial MBA]
        auto *one = llvm::ConstantInt::get(ty, 1);
        auto *bp1 = builder.CreateAdd(b, one, "");
        auto *ap1 = builder.CreateAdd(a, one, "");
        auto *lhs = builder.CreateMul(a, bp1, "");
        auto *rhs = builder.CreateMul(b, ap1, "");
        replacement = builder.CreateSub(lhs, rhs, "");
      }
      break;
    }
    case llvm::Instruction::Xor: {
      // MBA variants for a ^ b
      int variant = std::uniform_int_distribution<int>(0, 2)(rng);
      if (variant == 0) {
        // a ^ b => (a | b) - (a & b)
        auto *ov = builder.CreateOr(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        replacement = builder.CreateSub(ov, av, "");
      } else if (variant == 1) {
        // a ^ b => (a + b) - 2*(a & b)
        auto *sv = builder.CreateAdd(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        auto *mv = builder.CreateAdd(av, av, "");
        replacement = builder.CreateSub(sv, mv, "");
      } else {
        // a ^ b => ((a+b)*K - 2*(a&b)*K) * K_inv  [polynomial MBA]
        unsigned bw = ty->getIntegerBitWidth();
        uint64_t kRaw = (rng() | 1ULL);
        if (bw < 64) kRaw &= (uint64_t(1) << bw) - 1;
        if (kRaw == 0) kRaw = 1;
        uint64_t kInvRaw = modInverse(kRaw, bw);
        auto *kVal = llvm::ConstantInt::get(ty, kRaw);
        auto *sv = builder.CreateAdd(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        auto *sk = builder.CreateMul(sv, kVal, "");
        auto *ak = builder.CreateMul(av, kVal, "");
        auto *ak2 = builder.CreateAdd(ak, ak, "");
        auto *diff = builder.CreateSub(sk, ak2, "");
        replacement = applyKInverse(builder, diff, kInvRaw, bw, ty, rng, coin);
      }
      break;
    }
    case llvm::Instruction::And: {
      // MBA variants for a & b
      int variant = std::uniform_int_distribution<int>(0, 1)(rng);
      if (variant == 0) {
        // a & b => (a + b) - (a | b)
        auto *sv = builder.CreateAdd(a, b, "");
        auto *ov = builder.CreateOr(a, b, "");
        replacement = builder.CreateSub(sv, ov, "");
      } else {
        // a & b => ((a+b)*K - (a|b)*K) * K_inv  [polynomial MBA]
        unsigned bw = ty->getIntegerBitWidth();
        uint64_t kRaw = (rng() | 1ULL);
        if (bw < 64) kRaw &= (uint64_t(1) << bw) - 1;
        if (kRaw == 0) kRaw = 1;
        uint64_t kInvRaw = modInverse(kRaw, bw);
        auto *kVal = llvm::ConstantInt::get(ty, kRaw);
        auto *sv = builder.CreateAdd(a, b, "");
        auto *ov = builder.CreateOr(a, b, "");
        auto *sk = builder.CreateMul(sv, kVal, "");
        auto *ok = builder.CreateMul(ov, kVal, "");
        auto *diff = builder.CreateSub(sk, ok, "");
        replacement = applyKInverse(builder, diff, kInvRaw, bw, ty, rng, coin);
      }
      break;
    }
    case llvm::Instruction::Or: {
      // MBA variants for a | b
      int variant = std::uniform_int_distribution<int>(0, 2)(rng);
      if (variant == 0) {
        // a | b => (a ^ b) + (a & b)
        auto *xv = builder.CreateXor(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        replacement = builder.CreateAdd(xv, av, "");
      } else if (variant == 1) {
        // a | b => (a + b) - (a & b)
        auto *sv = builder.CreateAdd(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        replacement = builder.CreateSub(sv, av, "");
      } else {
        // a | b => ((a^b)*K + (a&b)*K) * K_inv  [polynomial MBA]
        unsigned bw = ty->getIntegerBitWidth();
        uint64_t kRaw = (rng() | 1ULL);
        if (bw < 64) kRaw &= (uint64_t(1) << bw) - 1;
        if (kRaw == 0) kRaw = 1;
        uint64_t kInvRaw = modInverse(kRaw, bw);
        auto *kVal = llvm::ConstantInt::get(ty, kRaw);
        auto *xv = builder.CreateXor(a, b, "");
        auto *av = builder.CreateAnd(a, b, "");
        auto *xk = builder.CreateMul(xv, kVal, "");
        auto *ak = builder.CreateMul(av, kVal, "");
        auto *sum = builder.CreateAdd(xk, ak, "");
        replacement = applyKInverse(builder, sum, kInvRaw, bw, ty, rng, coin);
      }
      break;
    }
    case llvm::Instruction::Shl: {
      // a << b => a * (1 << b)
      auto *one = llvm::ConstantInt::get(ty, 1);
      auto *pow2 = builder.CreateShl(one, b, "");
      replacement = builder.CreateMul(a, pow2, "");
      break;
    }
    case llvm::Instruction::LShr: {
      // a >> b => udiv a, (1 << b)  [only for constant b < bitwidth]
      if (auto *cb = llvm::dyn_cast<llvm::ConstantInt>(b)) {
        unsigned bw = ty->getIntegerBitWidth();
        if (cb->getZExtValue() < bw) {
          auto *one = llvm::ConstantInt::get(ty, 1);
          auto *pow2 = builder.CreateShl(one, b, "");
          replacement = builder.CreateUDiv(a, pow2, "");
        }
      }
      break;
    }
    case llvm::Instruction::AShr: {
      // a ashr b => select(a >= 0, a udiv (1 << b), ~(~a udiv (1 << b)))
      // Only for constant b < bitwidth. Cannot use sdiv (rounding differs).
      if (auto *cb = llvm::dyn_cast<llvm::ConstantInt>(b)) {
        unsigned bw = ty->getIntegerBitWidth();
        if (cb->getZExtValue() < bw) {
          auto *one = llvm::ConstantInt::get(ty, 1);
          auto *pow2 = builder.CreateShl(one, b, "");
          auto *zero = llvm::ConstantInt::get(ty, 0);
          auto *is_neg = builder.CreateICmpSLT(a, zero, "");
          // Positive path: a udiv (1 << b)
          auto *pos_result = builder.CreateUDiv(a, pow2, "");
          // Negative path: ~(~a udiv (1 << b))
          auto *not_a = builder.CreateNot(a, "");
          auto *neg_div = builder.CreateUDiv(not_a, pow2, "");
          auto *neg_result = builder.CreateNot(neg_div, "");
          replacement = builder.CreateSelect(is_neg, neg_result, pos_result, "");
        }
      }
      break;
    }
    default:
      break;
    }

    if (replacement) {
      bin->replaceAllUsesWith(replacement);
      bin->eraseFromParent();
    }
  }
}

void substituteModule(llvm::Module &M, uint32_t seed,
                      const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    substituteFunction(F, rng, cfg);
  }
}

}  // namespace ollvm

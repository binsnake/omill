#include "ConstantUnfolding.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

namespace {

/// Return true if operand index `idx` of `I` can safely be replaced by a
/// non-constant value.
bool isOperandReplaceable(llvm::Instruction *I, unsigned idx) {
  // Only allow operands of binary ops, icmp, and store value operand.
  if (llvm::isa<llvm::BinaryOperator>(I))
    return true;
  if (llvm::isa<llvm::ICmpInst>(I))
    return true;
  if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(I))
    return idx == 0;  // value operand only, not pointer
  return false;
}

struct UnfoldCandidate {
  llvm::Instruction *inst;
  unsigned operand_idx;
  llvm::ConstantInt *ci;
};

void unfoldConstantsFunction(llvm::Function &F, std::mt19937 &rng) {
  if (F.isDeclaration())
    return;

  // Collect candidates first to avoid iterator invalidation.
  std::vector<UnfoldCandidate> work;
  for (auto &BB : F) {
    for (auto &I : BB) {
      // Skip PHI nodes entirely.
      if (llvm::isa<llvm::PHINode>(&I))
        continue;

      for (unsigned i = 0, e = I.getNumOperands(); i < e; ++i) {
        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(I.getOperand(i));
        if (!ci)
          continue;
        // Skip i1 booleans.
        if (ci->getBitWidth() == 1)
          continue;
        // Skip small constants (0, 1, -1) — not worth unfolding.
        int64_t val = ci->getSExtValue();
        if (val == 0 || val == 1 || val == -1)
          continue;
        if (!isOperandReplaceable(&I, i))
          continue;
        work.push_back({&I, i, ci});
      }
    }
  }

  std::uniform_int_distribution<int> percent(0, 99);
  std::uniform_int_distribution<int> strategy_dist(0, 3);
  std::uniform_int_distribution<uint64_t> key_dist(1, 0xFFFF);

  for (auto &cand : work) {
    // Apply to ~40% of candidates.
    if (percent(rng) >= 40)
      continue;

    auto *ci = cand.ci;
    auto *ty = ci->getType();
    uint64_t C = ci->getZExtValue();
    unsigned bits = ci->getBitWidth();

    llvm::IRBuilder<> builder(cand.inst);
    llvm::Value *replacement = nullptr;

    int strat = strategy_dist(rng);
    uint64_t K = key_dist(rng);

    switch (strat) {
    case 0: {
      // Add/Sub: C => (C + K) - K
      auto *sum = llvm::ConstantInt::get(ty, C + K);
      auto *key = llvm::ConstantInt::get(ty, K);
      replacement = builder.CreateSub(sum, key);
      break;
    }
    case 1: {
      // XOR: C => (C ^ K) ^ K
      auto *xored = llvm::ConstantInt::get(ty, C ^ K);
      auto *key = llvm::ConstantInt::get(ty, K);
      replacement = builder.CreateXor(xored, key);
      break;
    }
    case 2: {
      // Mul/Div (power of 2): C => (C / 2^k) * 2^k
      // Only when C is divisible by 2^k.
      unsigned k = 1 + (K % std::min(bits - 1, 4u));  // shift 1..4
      uint64_t divisor = 1ULL << k;
      if (C != 0 && (C % divisor) == 0) {
        auto *divided = llvm::ConstantInt::get(ty, C / divisor);
        auto *mul_val = llvm::ConstantInt::get(ty, divisor);
        replacement = builder.CreateMul(divided, mul_val);
      } else {
        // Fall back to add/sub.
        auto *sum = llvm::ConstantInt::get(ty, C + K);
        auto *key = llvm::ConstantInt::get(ty, K);
        replacement = builder.CreateSub(sum, key);
      }
      break;
    }
    case 3: {
      // Rotate via add/sub with different key: C => (C + K1) - K1
      // (second add/sub variant with larger key range for diversity)
      uint64_t K2 = K * 257 + 13;  // different key from case 0
      auto *sum = llvm::ConstantInt::get(ty, C + K2);
      auto *key = llvm::ConstantInt::get(ty, K2);
      replacement = builder.CreateSub(sum, key);
      break;
    }
    }

    if (replacement) {
      cand.inst->setOperand(cand.operand_idx, replacement);
    }
  }
}

}  // namespace

void unfoldConstantsModule(llvm::Module &M, uint32_t seed) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    unfoldConstantsFunction(F, rng);
  }
}

}  // namespace ollvm

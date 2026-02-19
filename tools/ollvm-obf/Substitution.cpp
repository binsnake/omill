#include "Substitution.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

static void substituteFunction(llvm::Function &F, std::mt19937 &rng) {
  if (F.isDeclaration())
    return;

  std::uniform_int_distribution<int> coin(0, 1);

  // Collect instructions first to avoid iterator invalidation.
  std::vector<llvm::BinaryOperator *> work;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        // Skip i1 (boolean) and constant-only expressions.
        if (bin->getType()->isIntegerTy(1))
          continue;
        if (llvm::isa<llvm::Constant>(bin->getOperand(0)) &&
            llvm::isa<llvm::Constant>(bin->getOperand(1)))
          continue;
        work.push_back(bin);
      }
    }
  }

  for (auto *bin : work) {
    // Apply to ~50% of eligible operations.
    if (coin(rng) == 0)
      continue;

    llvm::IRBuilder<> builder(bin);
    auto *a = bin->getOperand(0);
    auto *b = bin->getOperand(1);
    auto *ty = bin->getType();
    auto *neg_one = llvm::ConstantInt::getSigned(ty, -1);
    llvm::Value *replacement = nullptr;

    switch (bin->getOpcode()) {
    case llvm::Instruction::Add: {
      // a + b => a - (~b) - 1 = a - (b ^ -1) - 1
      auto *not_b = builder.CreateXor(b, neg_one);
      auto *sub1 = builder.CreateSub(a, not_b);
      replacement = builder.CreateSub(sub1, llvm::ConstantInt::get(ty, 1));
      break;
    }
    case llvm::Instruction::Sub: {
      // a - b => a + (~b) + 1 = a + (b ^ -1) + 1
      auto *not_b = builder.CreateXor(b, neg_one);
      auto *add1 = builder.CreateAdd(a, not_b);
      replacement = builder.CreateAdd(add1, llvm::ConstantInt::get(ty, 1));
      break;
    }
    case llvm::Instruction::Xor: {
      // a ^ b => (a & ~b) | (~a & b)
      auto *not_a = builder.CreateXor(a, neg_one);
      auto *not_b = builder.CreateXor(b, neg_one);
      auto *t1 = builder.CreateAnd(a, not_b);
      auto *t2 = builder.CreateAnd(not_a, b);
      replacement = builder.CreateOr(t1, t2);
      break;
    }
    case llvm::Instruction::And: {
      // a & b => ~(~a | ~b)
      auto *not_a = builder.CreateXor(a, neg_one);
      auto *not_b = builder.CreateXor(b, neg_one);
      auto *or_val = builder.CreateOr(not_a, not_b);
      replacement = builder.CreateXor(or_val, neg_one);
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

void substituteModule(llvm::Module &M, uint32_t seed) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    substituteFunction(F, rng);
  }
}

}  // namespace ollvm

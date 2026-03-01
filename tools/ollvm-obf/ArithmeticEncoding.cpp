#include "ArithmeticEncoding.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Newton's method for modular inverse mod 2^bits. Requires a to be odd.
static uint64_t modInverse(uint64_t a, unsigned bits) {
  uint64_t inv = a;
  for (int i = 0; i < 6; ++i)
    inv *= 2 - a * inv;
  if (bits < 64)
    inv &= (uint64_t(1) << bits) - 1;
  return inv;
}

/// Check if an alloca is a candidate for encoding:
/// - In entry block, i32 or i64, not array allocation
/// - All users are non-volatile, non-atomic LoadInst or StoreInst
/// - LoadInst pointer operand == alloca
/// - StoreInst pointer operand == alloca, value type matches
static bool isCandidateAlloca(llvm::AllocaInst *AI) {
  // Must be in entry block.
  if (AI->getParent() != &AI->getFunction()->getEntryBlock())
    return false;

  // Must be scalar i32 or i64.
  auto *allocTy = AI->getAllocatedType();
  if (!allocTy->isIntegerTy(32) && !allocTy->isIntegerTy(64))
    return false;

  // Must not be array allocation.
  if (AI->isArrayAllocation())
    return false;

  for (auto *U : AI->users()) {
    if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(U)) {
      if (LI->isVolatile() || LI->isAtomic())
        return false;
      if (LI->getPointerOperand() != AI)
        return false;
    } else if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
      if (SI->isVolatile() || SI->isAtomic())
        return false;
      if (SI->getPointerOperand() != AI)
        return false;
      if (SI->getValueOperand()->getType() != allocTy)
        return false;
    } else {
      // GEP, call, bitcast, etc. — not a candidate.
      return false;
    }
  }

  return true;
}

static void encodeAllocasFunction(llvm::Function &F, std::mt19937 &rng,
                                  const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  // Collect candidate allocas from entry block.
  std::vector<llvm::AllocaInst *> candidates;
  for (auto &I : F.getEntryBlock()) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (isCandidateAlloca(AI))
        candidates.push_back(AI);
    }
  }

  for (auto *AI : candidates) {
    if (!shouldTransform(rng, cfg))
      continue;

    unsigned bits = AI->getAllocatedType()->getIntegerBitWidth();
    auto *ty = AI->getAllocatedType();

    // Pick random odd A and random B.
    uint64_t A = rng();
    A |= 1ULL;  // ensure odd
    if (bits < 64)
      A &= (uint64_t(1) << bits) - 1;
    if (A == 1) A = 3;  // avoid identity transform

    uint64_t B = rng();
    if (bits < 64)
      B &= (uint64_t(1) << bits) - 1;

    uint64_t Ainv = modInverse(A, bits);

    auto *constA = llvm::ConstantInt::get(ty, A);
    auto *constB = llvm::ConstantInt::get(ty, B);
    auto *constAinv = llvm::ConstantInt::get(ty, Ainv);

    // Collect users before mutation.
    std::vector<llvm::LoadInst *> loads;
    std::vector<llvm::StoreInst *> stores;
    for (auto *U : AI->users()) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(U))
        loads.push_back(LI);
      else if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U))
        stores.push_back(SI);
    }

    // Encode stores: val -> val * A + B
    for (auto *SI : stores) {
      llvm::IRBuilder<> builder(SI);
      auto *val = SI->getValueOperand();
      auto *mulVal = builder.CreateMul(val, constA, "");
      auto *encoded = builder.CreateAdd(mulVal, constB, "");
      SI->setOperand(0, encoded);
    }

    // Decode loads: loaded -> (loaded - B) * A_inv
    for (auto *LI : loads) {
      llvm::IRBuilder<> builder(LI->getNextNode());
      auto *subInst = llvm::cast<llvm::Instruction>(builder.CreateSub(LI, constB, ""));
      auto *decoded = builder.CreateMul(subInst, constAinv, "");
      LI->replaceAllUsesWith(decoded);
      // Fix up: replaceAllUsesWith replaced LI in subInst too.
      subInst->setOperand(0, LI);
    }
  }
}

void encodeAllocasModule(llvm::Module &M, uint32_t seed,
                         const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    encodeAllocasFunction(F, rng, cfg);
  }
}

}  // namespace ollvm

#include "OpaquePredicates.h"
#include "PassFilter.h"
#include "OpaquePredicateLib.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Obtain an integer value to use as the opaque predicate variable.
/// Prefers the first integer argument; falls back to loading from an alloca.
static llvm::Value *getPredicateInput(llvm::Function &F,
                                       llvm::IRBuilder<> &builder,
                                       llvm::AllocaInst *&fallbackAlloca) {
  // Prefer the first integer argument.
  for (auto &arg : F.args()) {
    if (arg.getType()->isIntegerTy() && arg.getType()->getIntegerBitWidth() >= 8)
      return &arg;
  }

  // No suitable argument — create a dedicated alloca in the entry block.
  if (!fallbackAlloca) {
    auto *i64Ty = llvm::Type::getInt64Ty(F.getContext());
    llvm::IRBuilder<> entryBuilder(&F.getEntryBlock(),
                                   F.getEntryBlock().begin());
    fallbackAlloca = entryBuilder.CreateAlloca(i64Ty, nullptr);
    entryBuilder.CreateStore(llvm::ConstantInt::get(i64Ty, 0), fallbackAlloca);
  }

  return builder.CreateLoad(fallbackAlloca->getAllocatedType(), fallbackAlloca);
}

/// Build an always-true condition based on the selected variant.
/// Delegates to the shared opaque predicate library.
/// ~70% MBA-based, ~30% CRC32-based.
static llvm::Value *buildOpaquePredicate(llvm::IRBuilder<> &builder,
                                          llvm::Value *x,
                                          llvm::Function &F,
                                          std::mt19937 &rng) {
  std::uniform_int_distribution<int> dist(0, 99);
  if (dist(rng) < 30) {
    return ollvm::buildCRC32Predicate(builder, F, rng());
  }
  return ollvm::generateOpaqueTrue(builder, x, rng());
}

/// Create a junk basic block that does a few harmless operations and then
/// branches unconditionally to the given target.  Uses a function argument
/// (or volatile alloca load) so the arithmetic survives constant folding.
static llvm::BasicBlock *createJunkBlock(llvm::Function &F,
                                          llvm::BasicBlock *target,
                                          std::mt19937 &rng) {
  auto &ctx = F.getContext();
  auto *junkBB = llvm::BasicBlock::Create(ctx, "", &F);
  llvm::IRBuilder<> builder(junkBB);

  auto *i32Ty = llvm::Type::getInt32Ty(ctx);
  std::uniform_int_distribution<uint32_t> valDist(1, 0xFFFF);

  // Get a non-constant base value so IRBuilder can't fold everything away.
  llvm::Value *base = nullptr;
  for (auto &arg : F.args()) {
    if (arg.getType()->isIntegerTy()) {
      // Truncate or zext to i32 for uniform arithmetic.
      if (arg.getType() == i32Ty) {
        base = &arg;
      } else if (arg.getType()->getIntegerBitWidth() > 32) {
        base = builder.CreateTrunc(&arg, i32Ty);
      } else {
        base = builder.CreateZExt(&arg, i32Ty);
      }
      break;
    }
  }
  if (!base) {
    // No integer arg — create a volatile load from an alloca.
    llvm::IRBuilder<> entryB(&F.getEntryBlock(), F.getEntryBlock().begin());
    auto *alloca = entryB.CreateAlloca(i32Ty);
    entryB.CreateStore(llvm::ConstantInt::get(i32Ty, 0), alloca);
    base = builder.CreateLoad(i32Ty, alloca, /*isVolatile=*/true);
  }

  // 3-6 arithmetic ops using the live base value + random constants.
  auto *acc = base;
  unsigned numOps = std::uniform_int_distribution<unsigned>(3, 6)(rng);
  for (unsigned i = 0; i < numOps; ++i) {
    auto *k = llvm::ConstantInt::get(i32Ty, valDist(rng));
    switch (std::uniform_int_distribution<int>(0, 3)(rng)) {
    case 0: acc = builder.CreateAdd(acc, k); break;
    case 1: acc = builder.CreateXor(acc, k); break;
    case 2: acc = builder.CreateMul(acc, k); break;
    default: acc = builder.CreateSub(acc, k); break;
    }
  }
  // Sink the result into a volatile store so it isn't DCE'd.
  auto *sinkAlloca = builder.CreateAlloca(i32Ty);
  builder.CreateStore(acc, sinkAlloca, /*isVolatile=*/true);

  builder.CreateBr(target);
  return junkBB;
}

static void insertOpaquePredicatesFunction(llvm::Function &F,
                                            std::mt19937 &rng,
                                            const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  // Skip single-block functions.
  if (F.size() <= 1)
    return;

  // Collect candidate blocks: those ending with an unconditional branch
  // and that are NOT return blocks.
  std::vector<llvm::BasicBlock *> candidates;
  for (auto &BB : F) {
    auto *term = BB.getTerminator();
    if (!term)
      continue;
    if (llvm::isa<llvm::ReturnInst>(term))
      continue;
    auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
    if (br && br->isUnconditional())
      candidates.push_back(&BB);
  }

  if (candidates.empty())
    return;

  std::uniform_int_distribution<int> coinFlip(0, 99);
  llvm::AllocaInst *fallbackAlloca = nullptr;

  for (auto *BB : candidates) {
    if (!shouldTransform(rng, cfg)) continue;
    // ~40% probability of insertion.
    if (coinFlip(rng) >= 40)
      continue;

    auto *br = llvm::cast<llvm::BranchInst>(BB->getTerminator());
    auto *originalTarget = br->getSuccessor(0);

    // Build the opaque predicate just before the branch.
    llvm::IRBuilder<> builder(br);
    auto *x = getPredicateInput(F, builder, fallbackAlloca);
    auto *cond = buildOpaquePredicate(builder, x, F, rng);

    // Create a junk block that also branches to the original target.
    auto *junkBB = createJunkBlock(F, originalTarget, rng);

    // Replace the unconditional branch with a conditional one.
    // True → original target, False → junk block.
    br->eraseFromParent();
    llvm::BranchInst::Create(originalTarget, junkBB, cond, BB);

    // Update PHI nodes in originalTarget: junkBB is a new predecessor
    // that carries the same incoming value as BB (junk path is dead).
    for (auto &inst : *originalTarget) {
      auto *phi = llvm::dyn_cast<llvm::PHINode>(&inst);
      if (!phi) break;
      auto *val = phi->getIncomingValueForBlock(BB);
      phi->addIncoming(val, junkBB);
    }
  }
}

void insertOpaquePredicatesModule(llvm::Module &M, uint32_t seed,
                                  const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    insertOpaquePredicatesFunction(F, rng, cfg);
  }
}

}  // namespace ollvm

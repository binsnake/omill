#include "CodeCloning.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

static bool callsSelf(llvm::Function &F) {
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I))
        if (CB->getCalledFunction() == &F)
          return true;
  return false;
}

static unsigned countInstructions(llvm::Function &F) {
  unsigned count = 0;
  for (auto &BB : F)
    count += static_cast<unsigned>(BB.size());
  return count;
}

static void diversifyClone(llvm::Function *Clone, std::mt19937 &rng) {
  std::uniform_int_distribution<unsigned> pct(1, 100);
  std::vector<llvm::BinaryOperator *> bins;
  for (auto &BB : *Clone)
    for (auto &I : BB)
      if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I))
        bins.push_back(bin);

  for (auto *bin : bins) {
    if (pct(rng) > 20)
      continue;  // 20% probability

    auto *ty = bin->getType();
    if (!ty->isIntegerTy())
      continue;

    llvm::IRBuilder<> builder(bin);
    auto *a = bin->getOperand(0);
    auto *b = bin->getOperand(1);

    std::uniform_int_distribution<uint64_t> kdist(1, 0xFFFF);
    uint64_t kval = kdist(rng);
    auto *K = llvm::ConstantInt::get(ty, kval);

    llvm::Value *replacement = nullptr;
    switch (bin->getOpcode()) {
    case llvm::Instruction::Add: {
      // a + b -> (a + b + K) - K
      auto *sum = builder.CreateAdd(a, b, "");
      auto *sumK = builder.CreateAdd(sum, K, "");
      replacement = builder.CreateSub(sumK, K, "");
      break;
    }
    case llvm::Instruction::Xor: {
      // a ^ b -> (a ^ b) ^ K ^ K
      auto *x1 = builder.CreateXor(a, b, "");
      auto *x2 = builder.CreateXor(x1, K, "");
      replacement = builder.CreateXor(x2, K, "");
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

void cloneFunctionsModule(llvm::Module &M, uint32_t seed,
                          const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  std::uniform_int_distribution<int> cloneCountDist(2, 3);
  std::uniform_int_distribution<unsigned> pct30(1, 100);

  // Collect candidates.
  std::vector<llvm::Function *> candidates;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.hasInternalLinkage() && !F.hasPrivateLinkage())
      continue;
    if (F.hasAddressTaken())
      continue;
    if (F.users().empty())
      continue;
    if (countInstructions(F) <= 5)
      continue;
    if (callsSelf(F))
      continue;
    if (shouldSkipFunction(F, cfg))
      continue;
    candidates.push_back(&F);
  }

  unsigned cloned = 0;
  constexpr unsigned kMaxCloned = 20;

  for (auto *F : candidates) {
    if (cloned >= kMaxCloned)
      break;
    if (!shouldTransform(rng, cfg))
      continue;
    if (pct30(rng) > 30)
      continue;  // 30% probability

    int numClones = cloneCountDist(rng);

    // Create clones.
    std::vector<llvm::Function *> variants;
    variants.push_back(F);  // original is variant 0

    for (int i = 0; i < numClones; ++i) {
      llvm::ValueToValueMapTy VMap;
      llvm::Function *Clone = llvm::CloneFunction(F, VMap);
      Clone->setLinkage(llvm::GlobalValue::InternalLinkage);
      Clone->setName("");
      diversifyClone(Clone, rng);
      variants.push_back(Clone);
    }

    // Snapshot call sites of the original function.
    std::vector<llvm::CallBase *> callSites;
    for (auto *U : F->users()) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U)) {
        if (CB->getCalledFunction() == F)
          callSites.push_back(CB);
      }
    }

    // Redirect each call site to a random variant.
    std::uniform_int_distribution<int> variantDist(0,
        static_cast<int>(variants.size()) - 1);
    for (auto *CB : callSites) {
      int pick = variantDist(rng);
      CB->setCalledFunction(variants[pick]);
    }

    ++cloned;
  }
}

}  // namespace ollvm

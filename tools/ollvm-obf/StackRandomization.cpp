#include "StackRandomization.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Return true if the alloca is fixed-size (not a dynamic VLA).
static bool isFixedSizeAlloca(const llvm::AllocaInst *AI) {
  if (!AI->isArrayAllocation())
    return true;
  return llvm::isa<llvm::ConstantInt>(AI->getArraySize());
}

/// Create a random type for a padding alloca.
static llvm::Type *randomPaddingType(llvm::LLVMContext &Ctx,
                                     std::mt19937 &rng) {
  std::uniform_int_distribution<int> pick(0, 4);
  switch (pick(rng)) {
  case 0:
    return llvm::Type::getInt8Ty(Ctx);
  case 1:
    return llvm::Type::getInt16Ty(Ctx);
  case 2:
    return llvm::Type::getInt32Ty(Ctx);
  case 3:
    return llvm::Type::getInt64Ty(Ctx);
  default: {
    std::uniform_int_distribution<unsigned> sizeDist(1, 64);
    unsigned n = sizeDist(rng);
    return llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), n);
  }
  }
}

static void randomizeStackFunction(llvm::Function &F, std::mt19937 &rng,
                                   const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;
  if (!shouldTransform(rng, cfg))
    return;

  llvm::BasicBlock &entry = F.getEntryBlock();

  // Collect fixed-size allocas from the entry block only.
  std::vector<llvm::AllocaInst *> allocas;
  for (auto &I : entry) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (isFixedSizeAlloca(AI))
        allocas.push_back(AI);
    }
  }

  // If no allocas, still insert padding (defeats stack frame fingerprinting).
  // But we need at least the entry block to have a terminator.
  if (entry.empty())
    return;

  // Generate 2-6 random padding allocas.
  std::uniform_int_distribution<int> padCountDist(2, 6);
  int padCount = padCountDist(rng);

  llvm::LLVMContext &Ctx = F.getContext();
  auto firstNonPhiIt = entry.getFirstNonPHIIt();
  if (firstNonPhiIt == entry.end())
    return;

  std::vector<llvm::AllocaInst *> paddingAllocas;
  for (int i = 0; i < padCount; ++i) {
    llvm::Type *ty = randomPaddingType(Ctx, rng);
    auto *padAI = new llvm::AllocaInst(ty, 0, "", firstNonPhiIt);
    paddingAllocas.push_back(padAI);

    // Store a random constant to prevent DCE.
    llvm::IRBuilder<> B(&entry, entry.getTerminator()->getIterator());
    if (ty->isIntegerTy()) {
      unsigned bits = ty->getIntegerBitWidth();
      std::uniform_int_distribution<uint64_t> valDist(
          0, bits < 64 ? (uint64_t(1) << bits) - 1 : ~uint64_t(0));
      auto *val = llvm::ConstantInt::get(ty, valDist(rng));
      B.CreateStore(val, padAI);
    } else {
      // Array type — store zero-initialized.
      auto *val = llvm::Constant::getNullValue(ty);
      B.CreateStore(val, padAI);
    }
  }

  // Merge real + padding allocas.
  std::vector<llvm::AllocaInst *> allAllocas;
  allAllocas.reserve(allocas.size() + paddingAllocas.size());
  allAllocas.insert(allAllocas.end(), allocas.begin(), allocas.end());
  allAllocas.insert(allAllocas.end(), paddingAllocas.begin(),
                    paddingAllocas.end());

  // Fisher-Yates shuffle.
  for (int i = static_cast<int>(allAllocas.size()) - 1; i > 0; --i) {
    std::uniform_int_distribution<int> dist(0, i);
    int j = dist(rng);
    std::swap(allAllocas[i], allAllocas[j]);
  }

  // Move all allocas to the start of the entry block in shuffled order.
  // We insert before the first instruction each time, building from last to
  // first.
  auto insertPt = entry.begin();
  // Skip PHI nodes — allocas go after them.
  while (insertPt != entry.end() &&
         llvm::isa<llvm::PHINode>(&*insertPt))
    ++insertPt;

  for (auto *AI : allAllocas) {
    AI->moveBefore(insertPt);
  }
}

void randomizeStackModule(llvm::Module &M, uint32_t seed,
                          const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M)
    randomizeStackFunction(F, rng, cfg);
}

}  // namespace ollvm

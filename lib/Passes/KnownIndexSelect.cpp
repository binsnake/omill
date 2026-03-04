#include "omill/Passes/KnownIndexSelect.h"

#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/KnownBits.h>

namespace omill {

namespace {

/// Maximum number of possible index values to enumerate before giving up.
constexpr unsigned kMaxPossibleValues = 8;

/// Enumerate all possible values from KnownBits when the number of unknown
/// bits is small.  Returns concrete APInt values for each combination of
/// unknown bits.
llvm::SmallVector<llvm::APInt> enumeratePossibleValues(
    const llvm::KnownBits &KB, unsigned maxCount) {
  llvm::SmallVector<llvm::APInt> result;
  unsigned bitWidth = KB.getBitWidth();
  llvm::APInt unknownMask = ~(KB.Zero | KB.One);

  // Collect positions of unknown bits.
  llvm::SmallVector<unsigned, 8> unknownPositions;
  for (unsigned i = 0; i < bitWidth; ++i) {
    if (unknownMask[i])
      unknownPositions.push_back(i);
  }

  unsigned numUnknown = unknownPositions.size();
  uint64_t numCombinations = 1ULL << numUnknown;
  if (numCombinations > maxCount)
    return result;

  llvm::APInt base = KB.One;  // Start with known-one bits set.
  for (uint64_t combo = 0; combo < numCombinations; ++combo) {
    llvm::APInt val = base;
    for (unsigned j = 0; j < numUnknown; ++j) {
      if (combo & (1ULL << j))
        val.setBit(unknownPositions[j]);
    }
    result.push_back(val);
  }

  return result;
}

/// Try to transform a load through a GEP with a non-constant index into a
/// select chain over the enumerated possible index values.
/// Returns true if the load was replaced.
bool tryTransformLoad(llvm::LoadInst *LI, const llvm::DataLayout &DL,
                      llvm::AssumptionCache *AC,
                      const llvm::DominatorTree *DT) {
  // Skip volatile loads.
  if (LI->isVolatile())
    return false;

  auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(LI->getPointerOperand());
  if (!GEP)
    return false;

  // Must have at least one index, and at least one must be non-constant.
  if (GEP->hasAllConstantIndices())
    return false;

  // Find the first non-constant index.
  llvm::Value *varIndex = nullptr;
  unsigned varIndexOperand = 0;
  for (auto it = GEP->idx_begin(); it != GEP->idx_end(); ++it) {
    if (!llvm::isa<llvm::ConstantInt>(it->get())) {
      if (varIndex)
        return false;  // Multiple non-constant indices — too complex.
      varIndex = it->get();
      varIndexOperand = it - GEP->idx_begin() + 1;  // +1 for pointer operand
    }
  }
  if (!varIndex)
    return false;

  // Index must be integer.
  if (!varIndex->getType()->isIntegerTy())
    return false;

  llvm::KnownBits KB =
      llvm::computeKnownBits(varIndex, DL, AC, LI, DT);

  auto possibleValues = enumeratePossibleValues(KB, kMaxPossibleValues);
  if (possibleValues.empty())
    return false;

  llvm::IRBuilder<> Builder(LI);

  if (possibleValues.size() == 1) {
    // Single possible value: replace the GEP index with a constant and load.
    llvm::SmallVector<llvm::Value *, 4> indices;
    for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
      if (i == varIndexOperand)
        indices.push_back(
            llvm::ConstantInt::get(varIndex->getType(), possibleValues[0]));
      else
        indices.push_back(GEP->getOperand(i));
    }
    auto *newGEP = Builder.CreateGEP(GEP->getSourceElementType(),
                                     GEP->getPointerOperand(), indices,
                                     GEP->getName() + ".resolved");
    if (auto *gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(newGEP))
      gepInst->setIsInBounds(GEP->isInBounds());
    auto *newLoad =
        Builder.CreateLoad(LI->getType(), newGEP, LI->getName() + ".sel");
    // Copy metadata.
    llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 4> metadata;
    LI->getAllMetadata(metadata);
    for (auto &[kind, md] : metadata) {
      if (auto *loadInst = llvm::dyn_cast<llvm::LoadInst>(newLoad))
        loadInst->setMetadata(kind, md);
    }

    LI->replaceAllUsesWith(newLoad);
    return true;
  }

  // Multiple possible values: create a concrete load for each, then build a
  // select chain.
  llvm::SmallVector<std::pair<llvm::APInt, llvm::Value *>, 8> caseLoads;
  for (auto &possVal : possibleValues) {
    llvm::SmallVector<llvm::Value *, 4> indices;
    for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
      if (i == varIndexOperand)
        indices.push_back(
            llvm::ConstantInt::get(varIndex->getType(), possVal));
      else
        indices.push_back(GEP->getOperand(i));
    }
    auto *concreteGEP = Builder.CreateGEP(GEP->getSourceElementType(),
                                          GEP->getPointerOperand(), indices,
                                          GEP->getName() + ".idx");
    if (auto *gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(concreteGEP))
      gepInst->setIsInBounds(GEP->isInBounds());
    auto *concreteLoad =
        Builder.CreateLoad(LI->getType(), concreteGEP, "val");
    caseLoads.push_back({possVal, concreteLoad});
  }

  // Build the select chain from back to front. Use the last value as default.
  llvm::Value *result = caseLoads.back().second;
  for (int i = static_cast<int>(caseLoads.size()) - 2; i >= 0; --i) {
    auto *cmpVal =
        llvm::ConstantInt::get(varIndex->getType(), caseLoads[i].first);
    auto *cmp = Builder.CreateICmpEQ(varIndex, cmpVal, "idx.cmp");
    result = Builder.CreateSelect(cmp, caseLoads[i].second, result, "idx.sel");
  }

  // Copy metadata to all created loads.
  llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 4> metadata;
  LI->getAllMetadata(metadata);
  for (auto &[kind, md] : metadata) {
    for (auto &[_, loadVal] : caseLoads) {
      if (auto *loadInst = llvm::dyn_cast<llvm::LoadInst>(loadVal))
        loadInst->setMetadata(kind, md);
    }
  }

  LI->replaceAllUsesWith(result);
  return true;
}

}  // namespace

llvm::PreservedAnalyses KnownIndexSelectPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  const auto &DL = F.getDataLayout();
  auto *DT = AM.getCachedResult<llvm::DominatorTreeAnalysis>(F);
  auto *AC = AM.getCachedResult<llvm::AssumptionAnalysis>(F);
  bool changed = false;

  // Collect loads first to avoid iterator invalidation.
  llvm::SmallVector<llvm::LoadInst *, 16> loads;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
        loads.push_back(LI);

  for (auto *LI : loads) {
    if (tryTransformLoad(LI, DL, AC, DT)) {
      LI->eraseFromParent();
      changed = true;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

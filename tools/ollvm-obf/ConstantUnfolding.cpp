#include "ConstantUnfolding.h"
#include "OpaquePredicateLib.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
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
  if (llvm::isa<llvm::BinaryOperator>(I))
    return true;
  if (llvm::isa<llvm::ICmpInst>(I))
    return true;
  if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(I))
    return idx == 0;
  return false;
}

struct UnfoldCandidate {
  llvm::Instruction *inst;
  unsigned operand_idx;
  llvm::ConstantInt *ci;
};

/// Emit a volatile load of the anchor, truncated/zext'd to `targetTy`.
llvm::Value *emitAnchorLoad(llvm::IRBuilder<> &builder,
                            llvm::GlobalVariable *anchor,
                            llvm::IntegerType *targetTy) {
  auto *i64Ty = anchor->getValueType();
  auto *load = builder.CreateLoad(i64Ty, anchor, true, "");

  unsigned targetBits = targetTy->getBitWidth();
  if (targetBits == 64)
    return load;
  if (targetBits < 64)
    return builder.CreateTrunc(load, targetTy, "");
  return builder.CreateZExt(load, targetTy, "");
}

void unfoldConstantsFunction(llvm::Function &F, std::mt19937 &rng,
                             llvm::GlobalVariable *anchor,
                             const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  std::vector<UnfoldCandidate> work;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::PHINode>(&I))
        continue;

      for (unsigned i = 0, e = I.getNumOperands(); i < e; ++i) {
        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(I.getOperand(i));
        if (!ci)
          continue;
        if (ci->getBitWidth() == 1 || ci->getBitWidth() > 64)
          continue;
        int64_t val = ci->getSExtValue();
        if (val == 0 || val == 1 || val == -1)
          continue;
        if (!isOperandReplaceable(&I, i))
          continue;
        work.push_back({&I, i, ci});
      }
    }
  }

  // Retrieve the anchor's compile-time init value for XOR compensation.
  uint64_t R = llvm::cast<llvm::ConstantInt>(anchor->getInitializer())
                   ->getZExtValue();

  // Insert an opaque store into the anchor in the entry block so that
  // constant-propagation cannot prove the global read-only.
  if (!work.empty()) {
    auto &entryBB = F.getEntryBlock();
    llvm::IRBuilder<> entryBuilder(&entryBB, entryBB.getFirstInsertionPt());
    auto *i64Ty = anchor->getValueType();
    auto *curVal = entryBuilder.CreateLoad(i64Ty, anchor, true, "");
    auto *noise = detail::buildMBAZero(entryBuilder, curVal, rng());
    auto *newVal = entryBuilder.CreateXor(curVal, noise, "");
    entryBuilder.CreateStore(newVal, anchor);
  }

  std::uniform_int_distribution<int> percent(0, 99);
  std::uniform_int_distribution<int> strategy_dist(0, 2);

  for (auto &cand : work) {
    if (!shouldTransform(rng, cfg)) continue;
    if (percent(rng) >= 40)
      continue;

    auto *ci = cand.ci;
    auto *ty = llvm::cast<llvm::IntegerType>(ci->getType());
    uint64_t C = ci->getZExtValue();

    llvm::IRBuilder<> builder(cand.inst);
    llvm::Value *replacement = nullptr;

    // Load volatile anchor (opaque to optimizer).
    llvm::Value *anchorVal = emitAnchorLoad(builder, anchor, ty);

    // Truncate R to target bitwidth for XOR compensation.
    unsigned bits = ty->getBitWidth();
    uint64_t Rtrunc = (bits < 64) ? (R & ((1ULL << bits) - 1)) : R;

    int strat = strategy_dist(rng);

    switch (strat) {
    case 0: {
      // (C ^ R_trunc) ^ anchor_load ^ mba_zero(anchor_load)
      // At runtime: (C^R) ^ R ^ 0 = C
      auto *cVal = llvm::ConstantInt::get(ty, C ^ Rtrunc);
      auto *xored = builder.CreateXor(cVal, anchorVal, "");
      auto *mbaZero = detail::buildMBAZero(builder, anchorVal, rng());
      replacement = builder.CreateXor(xored, mbaZero, "");
      break;
    }
    case 1: {
      // (C + anchor_load) - anchor_load + mba_zero(anchor_load)
      // Works for any anchor value: C + R - R + 0 = C
      auto *cVal = llvm::ConstantInt::get(ty, C);
      auto *added = builder.CreateAdd(cVal, anchorVal, "");
      auto *subbed = builder.CreateSub(added, anchorVal, "");
      auto *mbaZero = detail::buildMBAZero(builder, anchorVal, rng());
      replacement = builder.CreateAdd(subbed, mbaZero, "");
      break;
    }
    case 2: {
      // (C | anchor_load) & (C | ~anchor_load)
      // = C | (anchor_load & ~anchor_load) = C | 0 = C  (any anchor value)
      auto *cVal = llvm::ConstantInt::get(ty, C);
      auto *or1 = builder.CreateOr(cVal, anchorVal, "");
      auto *notAnc = builder.CreateNot(anchorVal, "");
      auto *or2 = builder.CreateOr(cVal, notAnc, "");
      replacement = builder.CreateAnd(or1, or2, "");
      break;
    }
    }

    if (replacement)
      cand.inst->setOperand(cand.operand_idx, replacement);
  }
}

}  // namespace

void unfoldConstantsModule(llvm::Module &M, uint32_t seed,
                           const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  auto &ctx = M.getContext();
  auto *i64Ty = llvm::Type::getInt64Ty(ctx);

  // Create 3-5 unnamed anchor globals with distinct random non-zero inits.
  unsigned numAnchors =
      std::uniform_int_distribution<unsigned>(3, 5)(rng);
  llvm::SmallVector<llvm::GlobalVariable *, 5> anchors;
  for (unsigned i = 0; i < numAnchors; ++i) {
    uint64_t initVal = rng();
    if (initVal == 0) initVal = 1;
    auto *gv = new llvm::GlobalVariable(
        M, i64Ty, false, llvm::GlobalValue::InternalLinkage,
        llvm::ConstantInt::get(i64Ty, initVal), "");
    anchors.push_back(gv);
  }

  for (auto &F : M) {
    auto *anchor =
        anchors[std::uniform_int_distribution<unsigned>(0, numAnchors - 1)(rng)];
    unfoldConstantsFunction(F, rng, anchor, cfg);
  }
}

}  // namespace ollvm

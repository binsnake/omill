#include "RegisterPressure.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Collect values defined in \p F that have uses in multiple basic blocks
/// and are integer or pointer typed.  These are candidates whose live-range
/// extension will meaningfully affect register allocation.
static std::vector<llvm::Value *>
collectAnchorValues(llvm::Function &F) {
  std::vector<llvm::Value *> anchors;

  auto isEligibleType = [](llvm::Type *T) {
    return T->isIntegerTy() || T->isPointerTy();
  };

  // Check arguments.
  for (auto &Arg : F.args()) {
    if (!isEligibleType(Arg.getType()))
      continue;
    llvm::SmallDenseSet<llvm::BasicBlock *, 4> useBlocks;
    for (auto *U : Arg.users()) {
      if (auto *I = llvm::dyn_cast<llvm::Instruction>(U))
        useBlocks.insert(I->getParent());
    }
    if (useBlocks.size() > 1)
      anchors.push_back(&Arg);
  }

  // Check instructions.
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (!isEligibleType(I.getType()))
        continue;
      llvm::SmallDenseSet<llvm::BasicBlock *, 4> useBlocks;
      for (auto *U : I.users()) {
        if (auto *UI = llvm::dyn_cast<llvm::Instruction>(U))
          useBlocks.insert(UI->getParent());
      }
      if (useBlocks.size() > 1)
        anchors.push_back(&I);
    }
  }

  return anchors;
}

/// Return true if \p BB starts with a landing pad instruction.
static bool hasLandingPad(const llvm::BasicBlock &BB) {
  if (BB.empty())
    return false;
  return llvm::isa<llvm::LandingPadInst>(&BB.front());
}

/// Insert an identity inline-asm anchor for \p val right before \p use,
/// and replace that single use with the asm result.
/// For pointer types the value is cast to i64 around the asm.
/// For integer types the asm uses the value's actual type (i8/i16/i32/i64).
static void insertAnchor(llvm::Value *val, llvm::Use &use) {
  auto *userInst = llvm::cast<llvm::Instruction>(use.getUser());
  llvm::IRBuilder<> builder(userInst);
  auto &ctx = userInst->getContext();

  llvm::Type *valTy = val->getType();
  bool isPtr = valTy->isPointerTy();

  // For pointers, use i64 as the asm register type.
  // For integers, use the value's actual type to avoid mismatches.
  llvm::Type *asmIntTy = isPtr ? llvm::Type::getInt64Ty(ctx) : valTy;

  llvm::Value *intVal = val;
  if (isPtr)
    intVal = builder.CreatePtrToInt(val, asmIntTy, "");

  auto *asmTy = llvm::FunctionType::get(asmIntTy, {asmIntTy}, false);
  auto *asmVal =
      llvm::InlineAsm::get(asmTy, "", "=r,0", /*hasSideEffects=*/true);
  auto *result = builder.CreateCall(asmTy, asmVal, {intVal}, "");

  llvm::Value *finalVal = result;
  if (isPtr)
    finalVal = builder.CreateIntToPtr(result, valTy, "");

  use.set(finalVal);
}

static void extendRegisterPressureFunction(llvm::Function &F,
                                           std::mt19937 &rng,
                                           const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  auto anchors = collectAnchorValues(F);
  if (anchors.empty())
    return;

  std::shuffle(anchors.begin(), anchors.end(), rng);

  unsigned inserted = 0;
  constexpr unsigned kMaxAnchorsPerFunction = 5;

  for (auto *val : anchors) {
    if (inserted >= kMaxAnchorsPerFunction)
      break;
    if (!shouldTransform(rng, cfg))
      continue;
    // 40% probability gate.
    if (std::uniform_int_distribution<unsigned>(1, 100)(rng) > 40)
      continue;

    // Collect uses in different basic blocks (not in the defining block).
    llvm::BasicBlock *defBB = nullptr;
    if (auto *inst = llvm::dyn_cast<llvm::Instruction>(val))
      defBB = inst->getParent();

    std::vector<llvm::Use *> crossBlockUses;
    for (auto &U : val->uses()) {
      auto *userInst = llvm::dyn_cast<llvm::Instruction>(U.getUser());
      if (!userInst)
        continue;
      // Skip PHI nodes — can't insert before them meaningfully.
      if (llvm::isa<llvm::PHINode>(userInst))
        continue;
      auto *useBB = userInst->getParent();
      if (useBB == defBB)
        continue;
      // Skip landing pad blocks.
      if (hasLandingPad(*useBB))
        continue;
      crossBlockUses.push_back(&U);
    }

    if (crossBlockUses.empty())
      continue;

    // Pick a random use.
    auto *chosen =
        crossBlockUses[std::uniform_int_distribution<size_t>(
            0, crossBlockUses.size() - 1)(rng)];

    insertAnchor(val, *chosen);
    ++inserted;
  }
}

void extendRegisterPressureModule(llvm::Module &M, uint32_t seed,
                                  const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M)
    extendRegisterPressureFunction(F, rng, cfg);
}

}  // namespace ollvm

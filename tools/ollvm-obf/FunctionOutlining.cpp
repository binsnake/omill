#include "FunctionOutlining.h"
#include "PassFilter.h"


#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Transforms/Utils/ValueMapper.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Check whether a basic block is a candidate for outlining.
static bool isOutlineCandidate(llvm::BasicBlock &BB) {
  llvm::Function *F = BB.getParent();
  // Not entry block.
  if (&BB == &F->getEntryBlock())
    return false;

  // Must have a single predecessor.
  if (!BB.getSinglePredecessor())
    return false;

  // No PHI nodes.
  if (llvm::isa<llvm::PHINode>(BB.front()))
    return false;

  // No exception handling / landingpad.
  if (BB.isLandingPad())
    return false;
  for (auto &I : BB) {
    if (llvm::isa<llvm::InvokeInst>(&I) || llvm::isa<llvm::ResumeInst>(&I))
      return false;
  }

  // Must have > 3 instructions (including terminator).
  if (BB.size() <= 3)
    return false;

  // Terminator must be unconditional branch.
  auto *term = BB.getTerminator();
  auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
  if (!br || !br->isUnconditional())
    return false;

  // Must not be a return block (already excluded by unconditional branch check,
  // but be explicit).
  if (llvm::isa<llvm::ReturnInst>(term))
    return false;

  return true;
}

/// Compute live-in values: values used by instructions in BB that are defined
/// outside BB (instructions in F or F's arguments). Constants are excluded.
static std::vector<llvm::Value *> computeLiveIn(llvm::BasicBlock &BB) {
  std::vector<llvm::Value *> liveIn;
  llvm::SmallPtrSet<llvm::Value *, 16> seen;

  for (auto &I : BB) {
    for (unsigned i = 0, e = I.getNumOperands(); i < e; ++i) {
      llvm::Value *op = I.getOperand(i);
      // Skip constants (includes ConstantInt, GlobalValue, etc.).
      if (llvm::isa<llvm::Constant>(op))
        continue;
      // Skip BasicBlock operands (branch targets).
      if (llvm::isa<llvm::BasicBlock>(op))
        continue;
      // Must be defined outside BB.
      if (auto *inst = llvm::dyn_cast<llvm::Instruction>(op)) {
        if (inst->getParent() == &BB)
          continue;
      }
      // Value is an argument of F or an instruction in another block.
      if (seen.insert(op).second)
        liveIn.push_back(op);
    }
  }
  return liveIn;
}

/// Compute live-out values: values defined in BB that are used outside BB.
static std::vector<llvm::Value *> computeLiveOut(llvm::BasicBlock &BB) {
  std::vector<llvm::Value *> liveOut;

  for (auto &I : BB) {
    // Skip terminator — it doesn't produce a meaningful value.
    if (I.isTerminator())
      continue;
    for (auto *user : I.users()) {
      if (auto *userInst = llvm::dyn_cast<llvm::Instruction>(user)) {
        if (userInst->getParent() != &BB) {
          liveOut.push_back(&I);
          break;
        }
      }
    }
  }
  return liveOut;
}

/// Outline a single basic block into a new function.
static void outlineBlock(llvm::BasicBlock &BB,
                         const std::vector<llvm::Value *> &liveIn,
                         const std::vector<llvm::Value *> &liveOut) {
  llvm::Function *F = BB.getParent();
  llvm::Module *M = F->getParent();
  llvm::LLVMContext &Ctx = M->getContext();

  // Determine return type.
  llvm::Type *retTy = nullptr;
  llvm::StructType *structTy = nullptr;
  if (liveOut.empty()) {
    retTy = llvm::Type::getVoidTy(Ctx);
  } else if (liveOut.size() == 1) {
    retTy = liveOut[0]->getType();
  } else {
    std::vector<llvm::Type *> fieldTypes;
    fieldTypes.reserve(liveOut.size());
    for (auto *v : liveOut)
      fieldTypes.push_back(v->getType());
    structTy = llvm::StructType::get(Ctx, fieldTypes);
    retTy = structTy;
  }

  // Determine argument types.
  std::vector<llvm::Type *> argTypes;
  argTypes.reserve(liveIn.size());
  for (auto *v : liveIn)
    argTypes.push_back(v->getType());

  // Create outlined function.
  auto *fnTy = llvm::FunctionType::get(retTy, argTypes, false);
  auto *G = llvm::Function::Create(fnTy, llvm::Function::InternalLinkage,
                                   "", M);

  // Create entry block in G.
  auto *gEntry = llvm::BasicBlock::Create(Ctx, "", G);

  // Build unified value map for RemapInstruction.
  llvm::ValueToValueMapTy VMap;
  for (unsigned i = 0; i < liveIn.size(); ++i)
    VMap[liveIn[i]] = G->getArg(i);

  // Collect non-terminator instructions from BB.
  std::vector<llvm::Instruction *> origInsts;
  for (auto &I : BB) {
    if (!I.isTerminator())
      origInsts.push_back(&I);
  }

  // Clone instructions into G's entry block, building the VMap as we go.
  for (auto *orig : origInsts) {
    auto *clone = orig->clone();
    clone->setName("");
    clone->insertBefore(gEntry->end());
    VMap[orig] = clone;
  }

  // Remap all cloned instructions using the unified VMap.
  // RF_IgnoreMissingLocals tolerates constants / globals not in VMap.
  for (auto &I : *gEntry) {
    llvm::RemapInstruction(&I, VMap,
                           llvm::RF_IgnoreMissingLocals |
                           llvm::RF_NoModuleLevelChanges);
  }

  // Add return instruction in G.
  llvm::IRBuilder<> gBuilder(gEntry);
  if (liveOut.empty()) {
    gBuilder.CreateRetVoid();
  } else if (liveOut.size() == 1) {
    llvm::Value *retVal = VMap.count(liveOut[0])
        ? static_cast<llvm::Value *>(VMap[liveOut[0]])
        : liveOut[0];
    gBuilder.CreateRet(retVal);
  } else {
    llvm::Value *agg = llvm::UndefValue::get(structTy);
    for (unsigned i = 0; i < liveOut.size(); ++i) {
      llvm::Value *v = VMap.count(liveOut[i])
          ? static_cast<llvm::Value *>(VMap[liveOut[i]])
          : liveOut[i];
      agg = gBuilder.CreateInsertValue(agg, v, {i}, "");
    }
    gBuilder.CreateRet(agg);
  }

  // Now replace BB's contents (except terminator) with a call to G.
  llvm::Instruction *term = BB.getTerminator();
  llvm::IRBuilder<> callBuilder(term);
  std::vector<llvm::Value *> callArgs(liveIn.begin(), liveIn.end());
  auto *call = callBuilder.CreateCall(G, callArgs, liveOut.empty() ? "" : "");

  // Replace uses of live-out values only in F (not in G).
  // Use replaceUsesWithIf to avoid touching the outlined function.
  auto inOrigFunction = [F](llvm::Use &U) {
    auto *user = llvm::dyn_cast<llvm::Instruction>(U.getUser());
    return user && user->getFunction() == F;
  };
  if (liveOut.size() == 1) {
    liveOut[0]->replaceUsesWithIf(call, inOrigFunction);
  } else if (liveOut.size() >= 2) {
    for (unsigned i = 0; i < liveOut.size(); ++i) {
      auto *ext = callBuilder.CreateExtractValue(call, {i}, "");
      liveOut[i]->replaceUsesWithIf(ext, inOrigFunction);
    }
  }

  // Erase original non-terminator instructions from BB (reverse order to
  // respect use-def chains).
  for (auto it = origInsts.rbegin(); it != origInsts.rend(); ++it) {
    (*it)->dropAllReferences();
  }
  for (auto it = origInsts.rbegin(); it != origInsts.rend(); ++it) {
    (*it)->eraseFromParent();
  }
}

static void outlineFunction(llvm::Function &F, std::mt19937 &rng,
                            const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  // Collect candidate blocks.
  std::vector<llvm::BasicBlock *> candidates;
  for (auto &BB : F) {
    if (isOutlineCandidate(BB))
      candidates.push_back(&BB);
  }

  unsigned outlined = 0;
  const unsigned maxOutlines = 3;

  for (auto *BB : candidates) {
    if (outlined >= maxOutlines)
      break;

    if (!shouldTransform(rng, cfg))
      continue;

    // 30% coin flip.
    if (std::uniform_int_distribution<unsigned>(1, 100)(rng) > 30)
      continue;

    auto liveIn = computeLiveIn(*BB);
    auto liveOut = computeLiveOut(*BB);

    outlineBlock(*BB, liveIn, liveOut);
    ++outlined;
  }
}

void outlineFunctionsModule(llvm::Module &M, uint32_t seed,
                            const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  // Collect functions first to avoid modifying the function list while
  // iterating (outlining adds new functions).
  std::vector<llvm::Function *> funcs;
  for (auto &F : M)
    funcs.push_back(&F);

  for (auto *F : funcs)
    outlineFunction(*F, rng, cfg);
}

}  // namespace ollvm

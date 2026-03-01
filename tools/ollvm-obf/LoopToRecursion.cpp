#include "LoopToRecursion.h"
#include "PassFilter.h"

#include <llvm/Analysis/LoopInfo.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/ValueMapper.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Check if a loop block contains exception-handling instructions.
static bool hasEH(const llvm::BasicBlock *BB) {
  for (auto &I : *BB) {
    if (llvm::isa<llvm::InvokeInst>(&I) || llvm::isa<llvm::LandingPadInst>(&I))
      return true;
  }
  return false;
}

/// Attempt to convert a single simple loop into a tail-recursive helper.
/// Returns true if the conversion was performed.
static bool convertLoop(llvm::Loop *L, llvm::Function &F) {
  // --- Eligibility checks ---
  if (!L->getSubLoops().empty())
    return false;

  auto *header = L->getHeader();
  auto *latch = L->getLoopLatch();
  auto *exitBB = L->getExitBlock();
  if (!header || !latch || !exitBB)
    return false;

  // Max 2 loop blocks.
  if (L->getNumBlocks() > 2)
    return false;

  // Header must have exactly 2 predecessors.
  if (header->hasNPredecessorsOrMore(3))
    return false;
  unsigned predCount = 0;
  for (auto it = llvm::pred_begin(header); it != llvm::pred_end(header); ++it)
    ++predCount;
  if (predCount != 2)
    return false;

  // Identify preheader: the predecessor of header that is NOT the latch.
  llvm::BasicBlock *preheader = nullptr;
  for (auto *pred : llvm::predecessors(header)) {
    if (pred != latch) {
      preheader = pred;
      break;
    }
  }
  if (!preheader)
    return false;

  // Check no EH in loop blocks.
  for (auto *BB : L->blocks()) {
    if (hasEH(BB))
      return false;
  }

  // Latch must end with conditional branch to header/exit.
  auto *latchBr = llvm::dyn_cast<llvm::BranchInst>(latch->getTerminator());
  if (!latchBr || !latchBr->isConditional())
    return false;

  auto *succ0 = latchBr->getSuccessor(0);
  auto *succ1 = latchBr->getSuccessor(1);
  bool backEdgeOnTrue = (succ0 == header && succ1 == exitBB);
  bool backEdgeOnFalse = (succ1 == header && succ0 == exitBB);
  if (!backEdgeOnTrue && !backEdgeOnFalse)
    return false;

  // --- Collect loop-carried PHIs at header ---
  std::vector<llvm::PHINode *> headerPhis;
  for (auto &I : *header) {
    auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
    if (!phi)
      break;
    // Must have exactly 2 incoming: preheader and latch.
    if (phi->getNumIncomingValues() != 2)
      return false;
    headerPhis.push_back(phi);
  }

  // Collect initial values (from preheader) and next values (from latch).
  std::vector<llvm::Value *> initVals;
  std::vector<llvm::Value *> nextVals;
  std::vector<llvm::Type *> argTypes;
  for (auto *phi : headerPhis) {
    initVals.push_back(phi->getIncomingValueForBlock(preheader));
    nextVals.push_back(phi->getIncomingValueForBlock(latch));
    argTypes.push_back(phi->getType());
  }

  // --- Collect exit values (PHIs at exitBB getting values from inside loop) ---
  struct ExitPhiInfo {
    llvm::PHINode *exitPhi;
    llvm::Value *valueFromLoop;  // the value coming from the loop
  };
  std::vector<ExitPhiInfo> exitPhis;
  for (auto &I : *exitBB) {
    auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
    if (!phi)
      break;
    // Find the incoming value from a loop block.
    for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
      auto *inBB = phi->getIncomingBlock(i);
      if (L->contains(inBB)) {
        exitPhis.push_back({phi, phi->getIncomingValue(i)});
        break;
      }
    }
  }


  // --- Strict eligibility: exitBB must only be reached from loop blocks ---
  // If exitBB has non-loop predecessors, PHI fixup after loop deletion is
  // unsound (preheader becomes a new predecessor that PHIs don't expect).
  for (auto *pred : llvm::predecessors(exitBB)) {
    if (!L->contains(pred))
      return false;
  }

  // All PHIs in exitBB must be captured as exit PHIs. Non-exit PHIs would
  // lose their loop-block incoming values after deletion, creating invalid IR.
  {
    unsigned numExitBBPhis = 0;
    for (auto &I : *exitBB) {
      if (!llvm::isa<llvm::PHINode>(&I))
        break;
      ++numExitBBPhis;
    }
    if (numExitBBPhis != exitPhis.size())
      return false;
  }

  // Safety: verify no loop instruction has uses outside the loop except
  // through the exit PHIs we already collected.
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      for (auto *U : I.users()) {
        auto *UI = llvm::dyn_cast<llvm::Instruction>(U);
        if (!UI) continue;
        if (L->contains(UI->getParent())) continue;
        // Must be an exit PHI we've captured.
        bool captured = false;
        for (auto &ep : exitPhis) {
          if (ep.exitPhi == UI) { captured = true; break; }
        }
        if (!captured) return false;
      }
    }
  }
  // --- Collect live-in values: values used in loop but defined outside ---
  // These must become additional arguments of the helper function G.
  llvm::SmallPtrSet<llvm::Value *, 8> loopDefSet;
  for (auto *BB : L->blocks())
    for (auto &I : *BB)
      loopDefSet.insert(&I);
  for (auto *phi : headerPhis)
    loopDefSet.insert(phi);

  std::vector<llvm::Value *> liveIns;
  llvm::SmallPtrSet<llvm::Value *, 8> liveInSet;
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      for (auto &Op : I.operands()) {
        auto *V = Op.get();
        if (llvm::isa<llvm::Constant>(V)) continue;
        if (llvm::isa<llvm::BasicBlock>(V)) continue;
        if (loopDefSet.count(V)) continue;
        if (liveInSet.insert(V).second) {
          liveIns.push_back(V);
          argTypes.push_back(V->getType());
        }
      }
    }
  }

  // --- Determine return type for helper function ---
  llvm::Type *retTy = nullptr;
  llvm::LLVMContext &Ctx = F.getContext();
  std::vector<llvm::Type *> exitTypes;
  for (auto &ep : exitPhis)
    exitTypes.push_back(ep.exitPhi->getType());

  if (exitTypes.empty()) {
    retTy = llvm::Type::getVoidTy(Ctx);
  } else if (exitTypes.size() == 1) {
    retTy = exitTypes[0];
  } else {
    retTy = llvm::StructType::get(Ctx, exitTypes);
  }

  // --- Create helper function G ---
  auto *fnTy = llvm::FunctionType::get(retTy, argTypes, false);
  auto *M = F.getParent();
  auto *G = llvm::Function::Create(fnTy, llvm::GlobalValue::InternalLinkage,
                                   "", M);

  // --- Clone loop blocks into G ---
  // We clone the blocks rather than moving them, to avoid complex dominance
  // fixup. Build a value map from old values to new.
  llvm::ValueToValueMapTy VMap;

  // Map header PHIs → function arguments of G.
  for (unsigned i = 0; i < headerPhis.size(); ++i) {
    VMap[headerPhis[i]] = G->getArg(i);
  }

  // Map live-in values → additional arguments of G.
  for (unsigned i = 0; i < liveIns.size(); ++i) {
    VMap[liveIns[i]] = G->getArg(headerPhis.size() + i);
  }

  // Collect loop blocks in order (header first).
  std::vector<llvm::BasicBlock *> loopBlocks;
  loopBlocks.push_back(header);
  for (auto *BB : L->blocks()) {
    if (BB != header)
      loopBlocks.push_back(BB);
  }

  // Create new blocks in G corresponding to loop blocks.
  std::vector<llvm::BasicBlock *> newBlocks;
  for (auto *BB : loopBlocks) {
    auto *newBB = llvm::BasicBlock::Create(Ctx, "", G);
    VMap[BB] = newBB;
    newBlocks.push_back(newBB);
  }

  // Also map the exit block to a new block in G where we return.
  auto *exitInG = llvm::BasicBlock::Create(Ctx, "", G);
  VMap[exitBB] = exitInG;

  // Clone instructions from loop blocks into corresponding new blocks.
  for (unsigned bi = 0; bi < loopBlocks.size(); ++bi) {
    auto *oldBB = loopBlocks[bi];
    auto *newBB = newBlocks[bi];
    for (auto &I : *oldBB) {
      // Skip PHI nodes in the header (already mapped to args).
      if (oldBB == header && llvm::isa<llvm::PHINode>(&I))
        continue;
      auto *newI = I.clone();
      newI->setName("");
      newI->insertBefore(newBB->end());
      VMap[&I] = newI;
    }
  }

  // Build the exit block in G: pack exit values and return.
  {
    llvm::IRBuilder<> builder(exitInG);
    if (exitTypes.empty()) {
      builder.CreateRetVoid();
    } else if (exitTypes.size() == 1) {
      // Will be remapped below.
      llvm::Value *val = exitPhis[0].valueFromLoop;
      // Look up in VMap if it's an instruction from the loop.
      if (VMap.count(val))
        val = VMap[val];
      builder.CreateRet(val);
    } else {
      llvm::Value *agg = llvm::UndefValue::get(retTy);
      for (unsigned i = 0; i < exitPhis.size(); ++i) {
        llvm::Value *val = exitPhis[i].valueFromLoop;
        if (VMap.count(val))
          val = VMap[val];
        agg = builder.CreateInsertValue(agg, val, i, "");
      }
      builder.CreateRet(agg);
    }
  }

  // Remap all operands in the cloned instructions (skip the exit block which
  // we built manually with already-remapped values).
  for (auto *newBB : newBlocks) {
    for (auto &I : *newBB) {
      llvm::RemapInstruction(&I, VMap,
                             llvm::RF_IgnoreMissingLocals |
                             llvm::RF_NoModuleLevelChanges);
    }
  }

  // --- Fix up the latch terminator in G: replace back-edge with tail call ---
  // Find the new latch block in G.
  auto *newLatch = llvm::cast<llvm::BasicBlock>(VMap[latch]);
  auto *newLatchBr = newLatch->getTerminator();

  // Collect the remapped next-iteration values.
  std::vector<llvm::Value *> callArgs;
  for (auto *nv : nextVals) {
    if (VMap.count(nv))
      callArgs.push_back(VMap[nv]);
    else
      callArgs.push_back(nv);  // Constant or external value.
  }
  // Append live-in values (passed through unchanged in recursive calls).
  for (unsigned i = 0; i < liveIns.size(); ++i)
    callArgs.push_back(G->getArg(headerPhis.size() + i));

  // Replace the conditional branch with: if (continue) musttail call + ret,
  // else goto exit.
  llvm::Value *cond = nullptr;
  {
    auto *oldBr = llvm::cast<llvm::BranchInst>(newLatchBr);
    cond = oldBr->getCondition();
  }
  newLatchBr->eraseFromParent();

  // Create two blocks: recurse block and exit-route block.
  auto *recurseBB = llvm::BasicBlock::Create(Ctx, "", G);
  {
    llvm::IRBuilder<> builder(recurseBB);
    auto *tailCall = builder.CreateCall(G, callArgs, "");
    tailCall->setTailCallKind(llvm::CallInst::TCK_MustTail);
    tailCall->setCallingConv(G->getCallingConv());
    if (retTy->isVoidTy())
      builder.CreateRetVoid();
    else
      builder.CreateRet(tailCall);
  }

  // Add conditional branch at end of newLatch.
  {
    llvm::IRBuilder<> builder(newLatch);
    if (backEdgeOnTrue) {
      // Original: br cond, header, exit → recurse on true, exit on false.
      builder.CreateCondBr(cond, recurseBB, exitInG);
    } else {
      // Original: br cond, exit, header → exit on true, recurse on false.
      builder.CreateCondBr(cond, exitInG, recurseBB);
    }
  }

  // If header != latch, the new header block branches to internal blocks.
  // The cloned header may still have the old branch targets; remapping above
  // should have handled that. But we also need to fix the entry: the new
  // header's first block should be the entry of G, which it already is.

  // --- Replace loop in F with call to G ---
  // At the preheader, replace the branch to header with a call to G.
  auto *preheaderTerm = preheader->getTerminator();
  preheaderTerm->eraseFromParent();

  {
    llvm::IRBuilder<> builder(preheader);
    // Build initial call args: PHI init values + live-in values.
    std::vector<llvm::Value *> initCallArgs(initVals.begin(), initVals.end());
    for (auto *V : liveIns)
      initCallArgs.push_back(V);
    auto *callResult = builder.CreateCall(G, initCallArgs, "");

    // Extract exit values and feed them to exit block PHIs.
    if (exitTypes.empty()) {
      // No exit values, just branch to exit.
    } else if (exitTypes.size() == 1) {
      exitPhis[0].exitPhi->replaceAllUsesWith(callResult);
    } else {
      for (unsigned i = 0; i < exitPhis.size(); ++i) {
        auto *extracted = builder.CreateExtractValue(callResult, i, "");
        exitPhis[i].exitPhi->replaceAllUsesWith(extracted);
      }
    }

    builder.CreateBr(exitBB);
  }

  // Remove exit PHIs that were RAUW'd and erase them.
  // Collect them first to avoid iterator invalidation.
  std::vector<llvm::PHINode *> deadPhis;
  for (auto &I : *exitBB) {
    auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
    if (!phi)
      break;
    // Check if this PHI was one of the exit PHIs we replaced.
    bool isExitPhi = false;
    for (auto &ep : exitPhis) {
      if (ep.exitPhi == phi) { isExitPhi = true; break; }
    }
    if (isExitPhi) {
      deadPhis.push_back(phi);
    } else {
      // Non-exit PHI: remove incoming from loop blocks.
      for (auto *BB : loopBlocks) {
        int idx = phi->getBasicBlockIndex(BB);
        if (idx >= 0)
          phi->removeIncomingValue(static_cast<unsigned>(idx), false);
      }
    }
  }
  for (auto *phi : deadPhis) {
    phi->replaceAllUsesWith(llvm::UndefValue::get(phi->getType()));
    phi->eraseFromParent();
  }

  // Delete loop blocks from F.
  // First, remove all uses of loop instructions (they should be dead now).
  for (auto it = loopBlocks.rbegin(); it != loopBlocks.rend(); ++it) {
    auto *BB = *it;
    // Drop all references from instructions in this block.
    for (auto &I : *BB)
      I.dropAllReferences();
  }
  for (auto it = loopBlocks.rbegin(); it != loopBlocks.rend(); ++it) {
    auto *BB = *it;
    // Remove from F.
    BB->eraseFromParent();
  }

  return true;
}

static void loopToRecursionFunction(llvm::Function &F, std::mt19937 &rng,
                                    const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  llvm::DominatorTree DT(F);
  llvm::LoopInfo LI(DT);

  // Limit to 1 loop conversion per function.
  for (auto *L : LI) {
    if (!shouldTransform(rng, cfg))
      continue;
    if (convertLoop(L, F))
      break;
  }
}

void loopToRecursionModule(llvm::Module &M, uint32_t seed,
                           const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  // Collect functions first to avoid iterator invalidation (new functions
  // are added to the module during transformation).
  std::vector<llvm::Function *> funcs;
  for (auto &F : M)
    funcs.push_back(&F);
  for (auto *F : funcs)
    loopToRecursionFunction(*F, rng, cfg);
}

}  // namespace ollvm

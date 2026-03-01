#include "InstructionScheduling.h"
#include "PassFilter.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Return true if \p I touches memory (load, store, call, invoke, fence, etc.).
static bool isMemoryOp(const llvm::Instruction &I) {
  return I.mayReadOrWriteMemory();
}

/// Reorder independent instructions within \p BB using randomised topological
/// sort.  PHI nodes stay at the top, the terminator stays at the bottom, and
/// all memory operations preserve their relative program order.
static void scheduleBasicBlock(llvm::BasicBlock &BB, std::mt19937 &rng) {
  // Collect non-PHI, non-terminator instructions.
  std::vector<llvm::Instruction *> work;
  for (auto &I : BB) {
    if (llvm::isa<llvm::PHINode>(&I))
      continue;
    if (I.isTerminator())
      continue;
    work.push_back(&I);
  }

  // Skip trivially small blocks.
  if (work.size() < 3)
    return;

  // --- Handle entry-block allocas: they must stay at the top in order. ---
  // Also keep landingpad instructions pinned at the front.
  std::vector<llvm::Instruction *> pinned;
  std::vector<llvm::Instruction *> schedulable;
  {
    bool inAllocaPrefix = (&BB == &BB.getParent()->getEntryBlock());
    for (auto *I : work) {
      if (llvm::isa<llvm::LandingPadInst>(I)) {
        pinned.push_back(I);
        continue;
      }
      if (inAllocaPrefix && llvm::isa<llvm::AllocaInst>(I)) {
        pinned.push_back(I);
        continue;
      }
      inAllocaPrefix = false;
      schedulable.push_back(I);
    }
  }

  if (schedulable.size() < 3)
    return;

  // Map instruction -> index for fast lookup.
  llvm::DenseMap<llvm::Instruction *, unsigned> idx;
  for (unsigned i = 0, e = static_cast<unsigned>(schedulable.size()); i < e;
       ++i)
    idx[schedulable[i]] = i;

  const unsigned n = static_cast<unsigned>(schedulable.size());

  // Build predecessor sets (adjacency list: preds[i] = instructions that must
  // come before schedulable[i]).
  std::vector<llvm::SmallVector<unsigned, 4>> preds(n);
  std::vector<unsigned> inDegree(n, 0);

  // Chain memory operations in program order.
  int lastMem = -1;
  for (unsigned i = 0; i < n; ++i) {
    if (isMemoryOp(*schedulable[i])) {
      if (lastMem >= 0) {
        preds[i].push_back(static_cast<unsigned>(lastMem));
        ++inDegree[i];
      }
      lastMem = static_cast<int>(i);
    }
  }

  // Data dependencies: if an operand is defined by another instruction in the
  // schedulable set, add an edge.
  for (unsigned i = 0; i < n; ++i) {
    llvm::Instruction *inst = schedulable[i];
    for (unsigned op = 0, oe = inst->getNumOperands(); op < oe; ++op) {
      if (auto *depInst = llvm::dyn_cast<llvm::Instruction>(inst->getOperand(op))) {
        auto it = idx.find(depInst);
        if (it != idx.end() && it->second != i) {
          preds[i].push_back(it->second);
          ++inDegree[i];
        }
      }
    }
  }

  // Kahn's algorithm with randomised tie-breaking.
  std::vector<unsigned> ready;
  for (unsigned i = 0; i < n; ++i) {
    if (inDegree[i] == 0)
      ready.push_back(i);
  }

  std::vector<llvm::Instruction *> order;
  order.reserve(n);

  while (!ready.empty()) {
    // Shuffle the ready set so the pick is uniformly random.
    std::shuffle(ready.begin(), ready.end(), rng);
    unsigned pick = ready.back();
    ready.pop_back();
    order.push_back(schedulable[pick]);

    // For every instruction that depends on `pick`, decrement in-degree.
    for (unsigned j = 0; j < n; ++j) {
      for (unsigned p : preds[j]) {
        if (p == pick) {
          if (--inDegree[j] == 0)
            ready.push_back(j);
          break;
        }
      }
    }
  }

  // Sanity: if topo-sort didn't emit everything (cycle?), bail out.
  if (order.size() != n)
    return;

  // --- Apply the new order. ---
  // Position all pinned instructions first (they're already at the top).
  // Then move schedulable instructions before the terminator in the computed
  // order.
  llvm::Instruction *term = BB.getTerminator();
  for (auto *I : order)
    I->moveBefore(term->getIterator());
}

static void scheduleFunction(llvm::Function &F, std::mt19937 &rng,
                              const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  std::uniform_int_distribution<int> coin(0, 1);

  for (auto &BB : F) {
    if (!shouldTransform(rng, cfg))
      continue;
    // Additional 50% coin flip per BB.
    if (coin(rng) == 0)
      continue;
    scheduleBasicBlock(BB, rng);
  }
}

void scheduleInstructionsModule(llvm::Module &M, uint32_t seed,
                                const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M)
    scheduleFunction(F, rng, cfg);
}

}  // namespace ollvm

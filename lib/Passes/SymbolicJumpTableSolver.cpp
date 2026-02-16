#include "omill/Passes/SymbolicJumpTableSolver.h"

#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/KnownBits.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

#include "JumpTableUtils.h"

namespace omill {

namespace {

using namespace llvm::PatternMatch;

/// Try to compute an upper bound for `idx` using ScalarEvolution.
/// Returns the exclusive upper bound, or std::nullopt.
std::optional<uint64_t> scevBound(llvm::ScalarEvolution &SE,
                                   llvm::Value *idx) {
  if (!SE.isSCEVable(idx->getType()))
    return std::nullopt;

  auto *scev = SE.getSCEV(idx);
  auto range = SE.getUnsignedRange(scev);
  if (range.isFullSet() || range.isEmptySet())
    return std::nullopt;

  auto upper = range.getUnsignedMax().getZExtValue();
  if (upper == 0 || upper > 1024)
    return std::nullopt;

  return upper + 1;  // exclusive
}

/// Try to compute an upper bound using computeKnownBits.
std::optional<uint64_t> knownBitsBound(const llvm::DataLayout &DL,
                                        llvm::Value *idx) {
  llvm::KnownBits KB = llvm::computeKnownBits(idx, DL);
  // The maximum possible value is where all unknown bits are 1.
  llvm::APInt max_val = ~KB.Zero;  // known-zero bits stay 0, rest is 1
  uint64_t upper = max_val.getZExtValue();
  if (upper == 0 || upper > 1024)
    return std::nullopt;
  return upper + 1;  // exclusive
}

/// Attempt to decompose the dispatch_jump target into a table load.
/// This is more permissive than RecoverJumpTables — it tries the
/// structured decomposition first, then falls back to evaluating
/// the pointer arithmetic symbolically.
struct TableAccess {
  llvm::LoadInst *load;
  jt::LinearAddress addr;
  uint64_t image_base;
};

std::optional<TableAccess> analyzeTarget(llvm::Value *target) {
  auto [image_base, load_val] = jt::unwrapRVAConversion(target);

  // Strip zext/sext.
  if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(load_val))
    load_val = zext->getOperand(0);
  else if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(load_val))
    load_val = sext->getOperand(0);

  auto *table_load = llvm::dyn_cast<llvm::LoadInst>(load_val);
  if (!table_load)
    return std::nullopt;

  auto addr_info = jt::decomposeTableAddress(table_load->getPointerOperand());
  if (!addr_info)
    return std::nullopt;

  return TableAccess{table_load, *addr_info, image_base};
}

}  // namespace

llvm::PreservedAnalyses SymbolicJumpTableSolverPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  auto &DL = F.getParent()->getDataLayout();

  // We request SE lazily only if needed, because not every function has
  // interesting SCEV expressions and building it has non-trivial cost.
  llvm::ScalarEvolution *SE = nullptr;
  auto getSE = [&]() -> llvm::ScalarEvolution & {
    if (!SE)
      SE = &AM.getResult<llvm::ScalarEvolutionAnalysis>(F);
    return *SE;
  };

  struct Candidate {
    llvm::CallInst *dispatch_call;
    llvm::ReturnInst *ret;
    TableAccess access;
    uint64_t num_entries;
  };

  llvm::SmallVector<Candidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->getName() != "__omill_dispatch_jump")
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *target = call->getArgOperand(1);
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      auto access = analyzeTarget(target);
      if (!access)
        continue;

      auto *idx = access->addr.index;

      // Try multiple bounding strategies, pick the tightest.
      std::optional<uint64_t> bound;

      // 1. Pattern-based (walks predecessors for icmp, AND masks, etc.)
      bound = jt::computeIndexRange(idx, call->getParent());

      // 2. SCEV-based.
      if (!bound) {
        auto scev_bound = scevBound(getSE(), idx);
        if (scev_bound)
          bound = scev_bound;
      }

      // 3. KnownBits-based.
      if (!bound) {
        auto kb_bound = knownBitsBound(DL, idx);
        if (kb_bound)
          bound = kb_bound;
      }

      if (!bound || *bound == 0 || *bound > 1024)
        continue;

      // Must be followed by ret.
      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      if (!ret)
        continue;

      candidates.push_back({call, ret, *access, *bound});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.access.addr;

    auto raw_entries =
        jt::readTableEntries(*map, addr.base, addr.stride, cand.num_entries);
    if (!raw_entries)
      continue;

    jt::applyRVAConversion(*raw_entries, cand.access.image_base, addr.stride);

    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.access.image_base,
        cand.dispatch_call, cand.ret, F, *map, lifted);

    if (result.changed)
      changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#include "omill/Passes/HashImportAnnotation.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>

#include "omill/Utils/ImportHashDB.h"

namespace omill {

/// Check if a loop (including sub-loops) contains a multiply by the FNV-1a
/// prime 0x01000193 (16777619), indicating FNV-1a hash computation.
static bool containsFNVMultiply(llvm::Loop *L) {
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!bin || bin->getOpcode() != llvm::Instruction::Mul)
        continue;
      for (auto &op : bin->operands()) {
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(op.get())) {
          if (ci->getZExtValue() == 16777619u)
            return true;
        }
      }
    }
  }
  return false;
}

/// Recursively collect candidate hash seeds from loop header phis.
/// A seed is the initial (pre-loop) constant value of a phi node, filtered
/// to values >= 0x100 to skip trivial loop counters.
static void collectSeeds(llvm::Loop *L,
                         llvm::SmallVectorImpl<uint32_t> &seeds) {
  for (auto &phi : L->getHeader()->phis()) {
    for (unsigned k = 0; k < phi.getNumIncomingValues(); ++k) {
      if (L->contains(phi.getIncomingBlock(k)))
        continue;
      auto *ci = llvm::dyn_cast<llvm::ConstantInt>(phi.getIncomingValue(k));
      if (!ci)
        continue;
      uint32_t seed = static_cast<uint32_t>(ci->getZExtValue());
      if (seed >= 0x100)
        seeds.push_back(seed);
    }
  }
  for (auto *sub : L->getSubLoops())
    collectSeeds(sub, seeds);
}

llvm::PreservedAnalyses HashImportAnnotationPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  ImportHashDB db;
  db.loadBuiltins();
  db.buildLookupTables();

  llvm::DominatorTree DT(F);
  llvm::LoopInfo LI(DT);

  bool changed = false;
  auto &Ctx = F.getContext();

  for (auto &BB : F) {
    auto *L = LI.getLoopFor(&BB);
    if (!L)
      continue;

    for (auto &I : BB) {
      auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(&I);
      if (!icmp || icmp->getPredicate() != llvm::ICmpInst::ICMP_EQ)
        continue;

      // The icmp must be used as a conditional branch condition.
      bool is_branch_cond = false;
      for (auto *user : icmp->users()) {
        if (auto *br = llvm::dyn_cast<llvm::BranchInst>(user)) {
          if (br->isConditional()) {
            is_branch_cond = true;
            break;
          }
        }
      }
      if (!is_branch_cond)
        continue;

      // Extract a 32-bit hash constant from either operand.
      // Handles i32 constants and i64 constants (sign- or zero-extended).
      uint32_t hash_value = 0;
      bool found_constant = false;
      for (unsigned i = 0; i < 2; ++i) {
        auto *CI = llvm::dyn_cast<llvm::ConstantInt>(icmp->getOperand(i));
        if (!CI)
          continue;
        uint64_t val = CI->getZExtValue();
        if (CI->getBitWidth() <= 32) {
          hash_value = static_cast<uint32_t>(val);
          found_constant = true;
          break;
        }
        // For i64: accept if upper 32 bits are zero or all-ones (sign-ext).
        uint32_t upper = static_cast<uint32_t>(val >> 32);
        if (upper == 0 || upper == 0xFFFFFFFF) {
          hash_value = static_cast<uint32_t>(val);
          found_constant = true;
          break;
        }
      }
      if (!found_constant || hash_value < 0x100)
        continue;

      // Strategy 1: Dynamic seed extraction.
      // Walk up the loop nest to find the outermost loop containing an
      // FNV-1a multiply, then try each phi seed with the legacy resolve API.
      bool resolved = false;
      llvm::Loop *fnv_loop = nullptr;
      for (auto *loop = L; loop; loop = loop->getParentLoop()) {
        if (containsFNVMultiply(loop))
          fnv_loop = loop;
      }
      if (fnv_loop) {
        llvm::SmallVector<uint32_t, 8> seeds;
        collectSeeds(fnv_loop, seeds);
        for (uint32_t seed : seeds) {
          auto result = db.resolve(seed, hash_value);
          if (result) {
            auto *mod_str = llvm::MDString::get(Ctx, result->module);
            auto *fn_str = llvm::MDString::get(Ctx, result->function);
            auto *md = llvm::MDNode::get(Ctx, {mod_str, fn_str});
            icmp->setMetadata("omill.resolved_import", md);
            changed = true;
            resolved = true;
            break;
          }
        }
      }

      // Strategy 2: Precomputed lookup tables (known algorithm/seed combos).
      if (!resolved) {
        auto result = db.tryResolve(hash_value);
        if (result) {
          auto *mod_str = llvm::MDString::get(Ctx, result->entry.module);
          auto *fn_str = llvm::MDString::get(Ctx, result->entry.function);
          auto *md = llvm::MDNode::get(Ctx, {mod_str, fn_str});
          icmp->setMetadata("omill.resolved_import", md);
          changed = true;
        }
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

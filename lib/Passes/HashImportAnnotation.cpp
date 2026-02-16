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

  /// Candidate icmp with its extracted hash value.
  struct HashCandidate {
    llvm::ICmpInst *icmp;
    uint32_t hash_value;
  };

  /// Extract a 32-bit hash constant from an icmp eq instruction.
  auto extractHashConstant =
      [](llvm::ICmpInst *icmp) -> std::optional<uint32_t> {
    for (unsigned i = 0; i < 2; ++i) {
      auto *CI = llvm::dyn_cast<llvm::ConstantInt>(icmp->getOperand(i));
      if (!CI)
        continue;
      uint64_t val = CI->getZExtValue();
      if (CI->getBitWidth() <= 32) {
        uint32_t h = static_cast<uint32_t>(val);
        if (h >= 0x100)
          return h;
        continue;
      }
      uint32_t upper = static_cast<uint32_t>(val >> 32);
      if (upper == 0 || upper == 0xFFFFFFFF) {
        uint32_t h = static_cast<uint32_t>(val);
        if (h >= 0x100)
          return h;
      }
    }
    return std::nullopt;
  };

  // All hash candidates seen in the function (for Strategy 3 pairing).
  llvm::SmallVector<HashCandidate, 8> all_candidates;
  // Unresolved candidates (subset of all_candidates).
  llvm::SmallVector<HashCandidate, 8> unresolved_candidates;

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

      auto hash_opt = extractHashConstant(icmp);
      if (!hash_opt)
        continue;
      uint32_t hash_value = *hash_opt;

      // Track all candidates for Strategy 3 pairing.
      all_candidates.push_back({icmp, hash_value});

      // Strategy 1: Dynamic seed extraction.
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
          resolved = true;
        }
      }

      // Track unresolved candidates for Strategy 3.
      if (!resolved)
        unresolved_candidates.push_back({icmp, hash_value});
    }
  }

  // Strategy 3: Paired hash resolution for CW_IMPORT.
  // Module hash (case-insensitive FNV1a32) + function hash (case-sensitive)
  // appear as two separate FNV loops in the same function.
  if (!unresolved_candidates.empty()) {
    // Try each unresolved candidate as a potential module hash.
    for (auto &cand : unresolved_candidates) {
      if (cand.icmp->getMetadata("omill.resolved_import"))
        continue;

      auto mod_name = db.resolveModuleName(cand.hash_value);
      if (!mod_name)
        continue;

      // Found a module match — scan ALL candidates (including those resolved
      // by Strategy 1/2) for a matching function hash in this module.
      for (auto &other : all_candidates) {
        if (other.icmp == cand.icmp)
          continue;

        auto func_entry = db.resolveInModule(*mod_name, other.hash_value);
        if (!func_entry)
          continue;

        // Annotate the function icmp if not already annotated.
        auto *mod_str = llvm::MDString::get(Ctx, func_entry->module);
        auto *fn_str = llvm::MDString::get(Ctx, func_entry->function);
        auto *md = llvm::MDNode::get(Ctx, {mod_str, fn_str});
        if (!other.icmp->getMetadata("omill.resolved_import")) {
          other.icmp->setMetadata("omill.resolved_import", md);
          changed = true;
        }

        // Annotate the module icmp with the module name.
        auto *mod_only_md = llvm::MDNode::get(
            Ctx, {mod_str, llvm::MDString::get(Ctx, "")});
        cand.icmp->setMetadata("omill.resolved_import", mod_only_md);
        changed = true;
        break;  // One module matches one function.
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

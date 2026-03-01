#pragma once

#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>

#include <random>


namespace ollvm {

/// Global filter configuration for all obfuscation passes.
struct FilterConfig {
  /// Minimum number of instructions in a function to be eligible for
  /// transformation.  Functions below this threshold are skipped.
  /// Default 0 means no filtering (backward-compatible).
  unsigned min_instructions = 0;

  /// Skip functions that contain inline assembly.  Obfuscation can break
  /// asm constraints and clobber lists.
  bool skip_inline_asm = false;

  /// Per-site transform probability (0–100).  Each eligible instruction /
  /// block / expression is independently rolled against this threshold.
  /// 100 = always transform (default, backward-compatible).
  /// 0   = skip all transforms (useful for testing filter wiring).
  unsigned transform_percent = 100;
};

/// Return true if \p F should be skipped by obfuscation passes.
/// Checks: declaration, availableExternally, naked attribute, instruction
/// count threshold, and inline-assembly presence.
inline bool shouldSkipFunction(const llvm::Function &F,
                               const FilterConfig &cfg) {
  if (F.isDeclaration())
    return true;

  if (F.hasFnAttribute(llvm::Attribute::Naked))
    return true;

  if (F.hasAvailableExternallyLinkage())
    return true;


  // Per-file exclusion: functions from OllvmExclude'd source files are tagged
  // with this attribute during the LTO bitcode annotation step.
  if (F.hasFnAttribute("ollvm_exclude"))
    return true;
  if (cfg.min_instructions > 0) {
    unsigned count = 0;
    for (auto &BB : F) {
      count += static_cast<unsigned>(BB.size());
      if (count >= cfg.min_instructions)
        break;
    }
    if (count < cfg.min_instructions)
      return true;
  }

  if (cfg.skip_inline_asm) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
          if (CB->isInlineAsm())
            return true;
        }
      }
    }
  }

  return false;
}

/// Per-site probability gate.  Returns true if this individual transform site
/// should be applied.  Uses the pass's own RNG for determinism.
inline bool shouldTransform(std::mt19937 &rng, const FilterConfig &cfg) {
  if (cfg.transform_percent >= 100)
    return true;
  if (cfg.transform_percent == 0)
    return false;
  return std::uniform_int_distribution<unsigned>(1, 100)(rng) <=
         cfg.transform_percent;
}

}  // namespace ollvm

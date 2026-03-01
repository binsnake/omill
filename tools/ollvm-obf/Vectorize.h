#pragma once

#include <llvm/IR/Module.h>
#include <cstdint>

#include "PassFilter.h"

namespace ollvm {

struct VectorizeOptions {
  /// Replace i32/i64 stack data flow (alloca/load/store) with lane-0 vector
  /// storage/reloads to preserve vector traffic in IR.
  bool vectorize_data = true;

  /// Lower add/sub through vector bitwise identities (xor/and/shl).
  bool vectorize_bitwise = false;

  /// Also vectorize i64 operations using <2 x i64>.  SSE2 covers add/sub/
  /// xor/and/or natively; SSE4.2 adds PCMPGTQ for 64-bit compares.
  bool vectorize_i64 = true;

  /// Percent of eligible scalar ops to vectorize (0-100).
  unsigned transform_percent = 40;
};

/// Replace eligible i32 (and optionally i64) scalar arithmetic/data flow with
/// <4 x i32> / <2 x i64> vector operations, forcing stable SSE2/SSE4.2-
/// oriented mutation.
void vectorizeModule(llvm::Module &M, uint32_t seed,
                     const VectorizeOptions &opts = VectorizeOptions{},
                     const FilterConfig &cfg = FilterConfig{});

}  // namespace ollvm

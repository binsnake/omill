#pragma once

#include <llvm/IR/Module.h>
#include <cstdint>

namespace ollvm {

struct VectorizeOptions {
  /// Replace i32 stack data flow (alloca/load/store) with lane-0 vector
  /// storage/reloads to preserve vector traffic in IR.
  bool vectorize_data = true;

  /// Lower add/sub through vector bitwise identities (xor/and/shl).
  bool vectorize_bitwise = false;

  /// Percent of eligible scalar i32 ops to vectorize.
  unsigned transform_percent = 40;
};

/// Replace eligible i32 scalar arithmetic/data flow with <4 x i32> vector
/// operations, forcing stable SSE2-oriented mutation.
void vectorizeModule(llvm::Module &M, uint32_t seed,
                     const VectorizeOptions &opts = VectorizeOptions{});

}  // namespace ollvm

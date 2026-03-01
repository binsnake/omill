#pragma once

#include <llvm/IR/Module.h>

#include <cstdint>

#include "PassFilter.h"

namespace ollvm {

/// Insert bogus control flow into all eligible functions in the module.
/// Clones basic blocks and guards them with opaque predicates (always-true
/// conditions) to create diamond-shaped CFG patterns that confuse decompilers.
void insertBogusControlFlowModule(llvm::Module &M, uint32_t seed,
                                  const FilterConfig &cfg = FilterConfig{});

}  // namespace ollvm

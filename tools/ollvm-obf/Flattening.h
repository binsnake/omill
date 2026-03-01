#pragma once

#include <llvm/IR/Module.h>
#include <cstdint>

#include "PassFilter.h"

namespace ollvm {

/// Apply control flow flattening to all eligible functions in the module.
/// Each function's basic blocks are collected into a switch-based dispatcher.
void flattenModule(llvm::Module &M, uint32_t seed,
                   const FilterConfig &cfg = FilterConfig{});

}  // namespace ollvm

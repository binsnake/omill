#pragma once

#include <llvm/IR/Module.h>

#include <cstdint>

#include "PassFilter.h"

namespace ollvm {

/// Insert opaque predicates (always-true/always-false conditional branches)
/// before unconditional branches to obscure the real control flow.
void insertOpaquePredicatesModule(llvm::Module &M, uint32_t seed,
                                  const FilterConfig &cfg = FilterConfig{});

}  // namespace ollvm

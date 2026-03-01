#pragma once

#include <llvm/IR/Module.h>
#include <cstdint>

#include "PassFilter.h"

namespace ollvm {

/// Encode integer values stored to allocas using affine transforms
/// enc(x) = A*x + B, dec(y) = (y - B) * A_inv.
void encodeAllocasModule(llvm::Module &M, uint32_t seed,
                         const FilterConfig &cfg = FilterConfig{});

}  // namespace ollvm

#pragma once

#include <llvm/IR/Module.h>
#include <cstdint>

namespace ollvm {

/// Replace ~40% of eligible integer constants with equivalent runtime
/// expressions (add/sub, xor, mul/div, shift).  After lifting, InstCombine
/// and GVN should fold them back.
void unfoldConstantsModule(llvm::Module &M, uint32_t seed);

}  // namespace ollvm

#pragma once

#include <llvm/IR/Module.h>

#include "PassFilter.h"

#include <cstdint>

namespace ollvm {

void loopToRecursionModule(llvm::Module &M, uint32_t seed,
                           const FilterConfig &cfg);

}  // namespace ollvm

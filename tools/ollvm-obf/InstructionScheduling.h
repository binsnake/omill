#pragma once

#include <llvm/IR/Module.h>

#include "PassFilter.h"

#include <cstdint>

namespace ollvm {

void scheduleInstructionsModule(llvm::Module &M, uint32_t seed,
                                const FilterConfig &cfg = FilterConfig{});

}  // namespace ollvm

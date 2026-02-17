#pragma once

#include <llvm/IR/Module.h>

namespace ollvm {

/// Apply MBA-style instruction substitution to ~50% of eligible integer
/// arithmetic operations in the module.
void substituteModule(llvm::Module &M);

}  // namespace ollvm

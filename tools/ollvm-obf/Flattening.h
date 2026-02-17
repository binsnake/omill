#pragma once

#include <llvm/IR/Module.h>

namespace ollvm {

/// Apply control flow flattening to all eligible functions in the module.
/// Each function's basic blocks are collected into a switch-based dispatcher.
void flattenModule(llvm::Module &M);

}  // namespace ollvm

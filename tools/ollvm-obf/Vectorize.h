#pragma once

#include <llvm/IR/Module.h>

namespace ollvm {

/// Replace ~40% of eligible i32 binary operations with equivalent
/// <4 x i32> vector operations, forcing SSE2 codegen.
void vectorizeModule(llvm::Module &M);

}  // namespace ollvm

#pragma once

#include <llvm/IR/Module.h>

namespace omill {

/// Repair malformed PHI nodes in a module so it can be written as valid LL.
///
/// Handles two cases:
/// 1. Incoming values from blocks that are not predecessors (stale entries).
/// 2. Missing duplicate entries for multi-edge predecessors (e.g. a switch
///    with two cases branching to the same block needs two PHI entries).
void repairMalformedPHIs(llvm::Module &M);

}  // namespace omill

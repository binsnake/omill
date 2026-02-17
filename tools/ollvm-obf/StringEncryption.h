#pragma once

#include <llvm/IR/Module.h>

namespace ollvm {

/// Apply XOR-based string encryption to global constant strings.
/// Replaces each string with an encrypted copy and inline decryption loops.
void encryptStringsModule(llvm::Module &M);

}  // namespace ollvm

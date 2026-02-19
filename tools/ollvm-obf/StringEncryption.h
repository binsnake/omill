#pragma once

#include <llvm/IR/Module.h>
#include <cstdint>

namespace ollvm {

/// Apply XOR-based string encryption to global constant strings.
/// Replaces each string with an encrypted copy and inline decryption loops.
void encryptStringsModule(llvm::Module &M, uint32_t seed);

}  // namespace ollvm

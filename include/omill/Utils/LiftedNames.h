#pragma once

#include <llvm/ADT/StringRef.h>

#include <cstdint>

namespace llvm {
class BasicBlock;
class Function;
}  // namespace llvm

namespace omill {

/// Find a basic block named "block_<hex_pc>" in F.
/// Tries multiple formatting patterns (%llx, %lx).
llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc);

/// Extract the entry virtual address from a lifted function name like
/// "sub_140001280" or "sub_140001280.1".  Returns 0 on failure.
uint64_t extractEntryVA(llvm::StringRef name);

/// Check if a function has the remill lifted signature: (ptr, i64, ptr) -> ptr,
/// is not a declaration, and doesn't have a __remill_/__omill_ prefix.
bool isLiftedFunction(const llvm::Function &F);

}  // namespace omill

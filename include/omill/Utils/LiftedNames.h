#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>

#include <cstddef>
#include <cstdint>
#include <string>

namespace llvm {
class BasicBlock;
class Function;
class Module;
class Value;
}  // namespace llvm

namespace omill {

/// Find a basic block whose name encodes the given PC as "block_<hex_pc>".
/// Handles LLVM inliner suffixes (e.g. block_140001000.i, block_140001000.2).
llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc);

/// Collect known block PCs for a lifted function.
/// Uses block_<pc> names when available, and falls back to NEXT_PC SSA
/// inference when names were destroyed by CFG simplification.
llvm::DenseMap<uint64_t, llvm::BasicBlock *> collectBlockPCMap(llvm::Function &F);

/// Try to evaluate a PC-producing SSA value to concrete PCs by substituting
/// program_counter with the function entry VA.
llvm::SmallVector<uint64_t, 8> collectPossiblePCValues(
    llvm::Value *V, llvm::Function &F, size_t max_values = 32);

/// Extract the entry virtual address from a lifted function name like
/// "sub_140001280" or "sub_140001280.1".  Returns 0 on failure.
uint64_t extractEntryVA(llvm::StringRef name);

/// Build the canonical lowercase lifted function name for a VA.
std::string liftedFunctionName(uint64_t va);

/// Build the canonical lowercase demerged handler clone name for a
/// (handler VA, incoming hash) pair.
std::string demergedHandlerCloneName(uint64_t va, uint64_t incoming_hash);

/// Build the canonical lowercase native wrapper name for a VA.
std::string nativeFunctionName(uint64_t va);

/// Check if a function has the remill lifted signature: (ptr, i64, ptr) -> ptr,
/// is not a declaration, and doesn't have a __remill_/__omill_ prefix.
bool isLiftedFunction(const llvm::Function &F);

/// Check if a function has the remill lifted signature: (ptr, i64, ptr) -> ptr.
/// Unlike isLiftedFunction, this does NOT require a body or name checks.
bool hasLiftedSignature(const llvm::Function &F);

/// Extract the block PC from a basic block name like "block_140001280".
/// Ignores trailing non-hex suffixes added by LLVM (e.g. ".i", ".123").
/// Returns 0 on failure.
uint64_t extractBlockPC(llvm::StringRef name);

/// True when the module has enabled post-closure cleanup/recovery scoping for
/// a closed generic devirtualization root slice.
bool isClosedRootSliceScopedModule(const llvm::Module &M);

/// True when a function is part of the currently selected closed root slice.
bool isClosedRootSliceFunction(const llvm::Function &F);

/// True when a function is the root entry of the currently selected closed
/// root slice.
bool isClosedRootSliceRoot(const llvm::Function &F);

}  // namespace omill

#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>

namespace llvm {
class BasicBlock;
class Function;
class Module;
class Value;
}  // namespace llvm

namespace omill {

/// Canonical project policy for unresolved control-flow dispatch.
enum class DispatchIntrinsicKind {
  kCall,
  kJump,
};

/// Find a basic block whose name encodes the given PC as "block_<hex_pc>".
/// Handles LLVM inliner suffixes (e.g. block_140001000.i, block_140001000.2).
llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc);
llvm::Function *findLiftedOrBlockFunctionByPC(llvm::Module &M, uint64_t pc);
llvm::Function *findLiftedOrCoveredFunctionByPC(llvm::Module &M, uint64_t pc);
llvm::Function *findStructuralCodeTargetFunctionByPC(llvm::Module &M,
                                                     uint64_t pc);
llvm::Function *findNearestStructuralCodeTargetFunctionByPC(
    llvm::Module &M, uint64_t pc, uint64_t max_distance = 0x20);
std::optional<uint64_t> findNearestCoveredLiftedOrBlockPC(
    llvm::Module &M, uint64_t pc, uint64_t max_distance = 0x20);

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

/// Extract a structural code-target PC from a function name such as
/// sub_<pc>, blk_<pc>, block_<pc>, omill_native_target_<pc>,
/// omill_native_boundary_<pc>, omill_executable_target_<pc>, or
/// omill_vm_enter_target_<pc>.
/// Returns 0 on failure.
uint64_t extractStructuralCodeTargetPC(llvm::StringRef name);

/// Extract a structural code-target PC from a function's attrs or name.
/// Prefers explicit ABI/devirtualization attrs over name parsing.
uint64_t extractStructuralCodeTargetPC(const llvm::Function &F);

/// Build the canonical lowercase lifted function name for a VA.
std::string liftedFunctionName(uint64_t va);

/// Build the canonical lowercase demerged handler clone name for a
/// (handler VA, incoming hash) pair.
std::string demergedHandlerCloneName(uint64_t va, uint64_t incoming_hash);

/// Return the dispatch intrinsic name that should be emitted for new IR in
/// the given module. When the module opts into raw Remill dispatch naming,
/// these return __remill_function_call / __remill_jump. Otherwise they return
/// the legacy __omill_dispatch_* compatibility names.
llvm::StringRef canonicalDispatchIntrinsicName(
    DispatchIntrinsicKind kind, const llvm::Module &M);

/// Return true when the module requests raw __remill_* dispatch names for new
/// unresolved control-flow sites.
bool prefersRawRemillDispatch(const llvm::Module &M);

/// Accept both the new raw __remill_* dispatch names and the legacy
/// __omill_dispatch_* compatibility names.
bool isDispatchCallName(llvm::StringRef name);
bool isDispatchJumpName(llvm::StringRef name);
bool isDispatchIntrinsicName(llvm::StringRef name);
bool isLegacyOmillDispatchName(llvm::StringRef name);

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

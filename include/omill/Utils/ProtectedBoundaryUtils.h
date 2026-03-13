#pragma once

#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Module.h>

#include <cstdint>
#include <optional>

namespace llvm {
class FunctionType;
}

namespace omill {

class BinaryMemoryMap;

struct ProtectedBoundaryInfo {
  uint64_t entry_va = 0;
  uint64_t canonical_target_va = 0;
  bool is_vm_entry_stub = false;
};

std::optional<uint64_t> followJumpThunk(const BinaryMemoryMap &mem,
                                        uint64_t start_va,
                                        unsigned max_depth = 8);

std::optional<ProtectedBoundaryInfo>
classifyProtectedBoundary(const BinaryMemoryMap &mem, uint64_t entry_va);

llvm::FunctionCallee getOrInsertProtectedBoundaryDecl(
    llvm::Module &module, llvm::FunctionType *fn_ty,
    const ProtectedBoundaryInfo &info,
    llvm::StringRef prefix = "vm_entry");

}  // namespace omill

#include "omill/Utils/ProtectedBoundaryUtils.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/Twine.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Type.h>
#include <llvm/Support/raw_ostream.h>

#include <cstring>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

std::optional<uint64_t> followJumpThunk(const BinaryMemoryMap &mem,
                                        uint64_t start_va,
                                        unsigned max_depth) {
  uint64_t current = start_va;
  bool followed = false;

  for (unsigned depth = 0; depth < max_depth; ++depth) {
    uint8_t buf[16];
    if (!mem.read(current, buf, sizeof(buf)))
      break;

    if (buf[0] == 0xE9) {
      int32_t rel = 0;
      std::memcpy(&rel, &buf[1], 4);
      current = current + 5 + static_cast<int64_t>(rel);
      followed = true;
      continue;
    }

    if (buf[0] == 0xEB) {
      int8_t rel = static_cast<int8_t>(buf[1]);
      current = current + 2 + rel;
      followed = true;
      continue;
    }

    break;
  }

  if (!followed)
    return std::nullopt;
  return current;
}

std::optional<ProtectedBoundaryInfo>
classifyProtectedBoundary(const BinaryMemoryMap &mem, uint64_t entry_va) {
  uint8_t buf[16];
  if (!mem.read(entry_va, buf, sizeof(buf)))
    return std::nullopt;

  ProtectedBoundaryInfo info;
  info.entry_va = entry_va;

  // VMP compact frequently uses `push imm32 ; jmp rel32/rel8` entry thunks
  // before entering the actual VM dispatcher.
  if (buf[0] != 0x68)
    return std::nullopt;

  uint64_t jump_target = 0;
  if (buf[5] == 0xE9) {
    int32_t rel = 0;
    std::memcpy(&rel, &buf[6], 4);
    jump_target = entry_va + 10 + static_cast<int64_t>(rel);
  } else if (buf[5] == 0xEB) {
    int8_t rel = static_cast<int8_t>(buf[6]);
    jump_target = entry_va + 7 + rel;
  } else {
    return std::nullopt;
  }

  if (auto resolved = followJumpThunk(mem, jump_target))
    jump_target = *resolved;

  info.canonical_target_va = jump_target;
  info.is_vm_entry_stub = true;
  return info;
}

llvm::FunctionCallee getOrInsertProtectedBoundaryDecl(
    llvm::Module &module, llvm::FunctionType *fn_ty,
    const ProtectedBoundaryInfo &info, llvm::StringRef prefix) {
  auto name = (prefix + "_" + llvm::Twine::utohexstr(info.entry_va)).str();
  auto callee = module.getOrInsertFunction(name, fn_ty);
  if (auto *fn = llvm::dyn_cast<llvm::Function>(callee.getCallee())) {
    fn->addFnAttr("omill.protection_boundary");
    fn->addFnAttr("omill.boundary_kind",
                  info.is_vm_entry_stub ? "vm_entry_stub"
                                        : "protected_boundary");
    fn->addFnAttr("omill.boundary_entry_va", llvm::utohexstr(info.entry_va));
    if (info.canonical_target_va != 0)
      fn->addFnAttr("omill.boundary_target_va",
                    llvm::utohexstr(info.canonical_target_va));
  }
  return callee;
}

}  // namespace omill

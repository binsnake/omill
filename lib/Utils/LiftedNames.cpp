#include "omill/Utils/LiftedNames.h"

#include <cstdio>

#include <llvm/IR/Function.h>

namespace omill {

llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "block_%llx", (unsigned long long)pc);
  for (auto &BB : F)
    if (BB.getName() == buf)
      return &BB;

  snprintf(buf, sizeof(buf), "block_%lx", (unsigned long)pc);
  for (auto &BB : F)
    if (BB.getName() == buf)
      return &BB;

  return nullptr;
}

uint64_t extractEntryVA(llvm::StringRef name) {
  if (!name.starts_with("sub_"))
    return 0;
  llvm::StringRef hex = name.drop_front(4);
  auto dot = hex.find('.');
  if (dot != llvm::StringRef::npos)
    hex = hex.substr(0, dot);
  uint64_t va = 0;
  if (hex.getAsInteger(16, va))
    return 0;
  return va;
}

bool isLiftedFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.getName().starts_with("__remill_"))
    return false;
  if (F.getName().starts_with("__omill_"))
    return false;
  if (F.getName().ends_with("_native"))
    return false;

  // Structural check: (ptr, i64, ptr) -> ptr
  if (F.arg_size() != 3)
    return false;
  auto *FTy = F.getFunctionType();
  if (!FTy->getReturnType()->isPointerTy())
    return false;
  if (!FTy->getParamType(0)->isPointerTy())
    return false;
  if (!FTy->getParamType(1)->isIntegerTy(64))
    return false;
  if (!FTy->getParamType(2)->isPointerTy())
    return false;

  return true;
}

}  // namespace omill

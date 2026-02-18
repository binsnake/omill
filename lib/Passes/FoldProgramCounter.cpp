#include "omill/Passes/FoldProgramCounter.h"

#include <cstdlib>

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {
namespace {

bool envDisabled(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return false;
  return (v[0] == '1' && v[1] == '\0') || (v[0] == 't' && v[1] == '\0') ||
         (v[0] == 'T' && v[1] == '\0');
}

bool isAddressOnlyValue(llvm::Value *V, llvm::DenseSet<llvm::Value *> &seen) {
  if (!seen.insert(V).second)
    return true;

  for (llvm::Use &U : V->uses()) {
    auto *I = llvm::dyn_cast<llvm::Instruction>(U.getUser());
    if (!I)
      return false;

    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(I)) {
      // Safe only when this value is used as the address, not stored data.
      if (SI->getPointerOperand() != V)
        return false;
      continue;
    }

    if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(I)) {
      if (LI->getPointerOperand() != V)
        return false;
      continue;
    }

    if (auto *RMW = llvm::dyn_cast<llvm::AtomicRMWInst>(I)) {
      if (RMW->getPointerOperand() != V)
        return false;
      continue;
    }

    if (auto *CX = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(I)) {
      if (CX->getPointerOperand() != V)
        return false;
      continue;
    }

    if (llvm::isa<llvm::BinaryOperator>(I) || llvm::isa<llvm::CastInst>(I) ||
        llvm::isa<llvm::GetElementPtrInst>(I)) {
      if (!isAddressOnlyValue(I, seen))
        return false;
      continue;
    }

    // Conservatively reject control-flow, PHI/select, calls, etc.
    return false;
  }

  return true;
}

bool isSafePCUse(llvm::Use &U) {
  auto *I = llvm::dyn_cast<llvm::Instruction>(U.getUser());
  if (!I)
    return false;

  if (!(llvm::isa<llvm::BinaryOperator>(I) || llvm::isa<llvm::CastInst>(I) ||
        llvm::isa<llvm::GetElementPtrInst>(I)))
    return false;

  llvm::DenseSet<llvm::Value *> seen;
  return isAddressOnlyValue(I, seen);
}

}  // namespace

llvm::PreservedAnalyses FoldProgramCounterPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (envDisabled("OMILL_SKIP_FOLD_PC"))
    return llvm::PreservedAnalyses::all();

  // Lifted functions have signature (ptr %state, i64 %pc, ptr %mem).
  if (F.arg_size() < 2)
    return llvm::PreservedAnalyses::all();

  auto *pc_arg = F.getArg(1);
  if (!pc_arg->getType()->isIntegerTy(64))
    return llvm::PreservedAnalyses::all();

  uint64_t entry_va = extractEntryVA(F.getName());
  if (entry_va == 0)
    return llvm::PreservedAnalyses::all();

  if (pc_arg->use_empty())
    return llvm::PreservedAnalyses::all();

  auto *constant = llvm::ConstantInt::get(pc_arg->getType(), entry_va);
  bool changed = false;
  for (llvm::Use &U : llvm::make_early_inc_range(pc_arg->uses())) {
    if (!isSafePCUse(U))
      continue;
    U.set(constant);
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

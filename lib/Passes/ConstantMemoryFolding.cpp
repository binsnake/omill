#include "omill/Passes/ConstantMemoryFolding.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

namespace {

/// Try to resolve a pointer operand to a constant integer address.
/// Handles:
///   - inttoptr(i64 <const>)  (ConstantExpr or IntToPtrInst)
///   - gep(inttoptr(i64 <const>), <const offsets>)
std::optional<uint64_t> resolveConstantAddress(llvm::Value *ptr,
                                                const llvm::DataLayout &DL) {
  // Strip pointer casts (bitcast, addrspacecast).
  ptr = ptr->stripPointerCasts();

  // Case 1: ConstantExpr inttoptr.
  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CE->getOperand(0)))
        return CI->getZExtValue();
    }
    // GEP constant expression with inttoptr base.
    if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
      auto *GEP = llvm::cast<llvm::GEPOperator>(CE);
      auto base_addr = resolveConstantAddress(GEP->getPointerOperand(), DL);
      if (!base_addr)
        return std::nullopt;
      llvm::APInt offset(DL.getPointerSizeInBits(), 0);
      if (!GEP->accumulateConstantOffset(DL, offset))
        return std::nullopt;
      return *base_addr + offset.getZExtValue();
    }
  }

  // Case 2: IntToPtrInst with constant operand.
  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(ITP->getOperand(0)))
      return CI->getZExtValue();
  }

  // Case 3: GEP instruction with resolvable base.
  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    auto base_addr = resolveConstantAddress(GEP->getPointerOperand(), DL);
    if (!base_addr)
      return std::nullopt;
    llvm::APInt offset(DL.getPointerSizeInBits(), 0);
    if (!GEP->accumulateConstantOffset(DL, offset))
      return std::nullopt;
    return *base_addr + offset.getZExtValue();
  }

  return std::nullopt;
}

}  // namespace

llvm::PreservedAnalyses ConstantMemoryFoldingPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  const auto &DL = F.getDataLayout();
  bool changed = false;

  llvm::SmallVector<llvm::LoadInst *, 16> loads;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
        loads.push_back(LI);

  for (auto *LI : loads) {
    auto addr = resolveConstantAddress(LI->getPointerOperand(), DL);
    if (!addr)
      continue;

    llvm::Type *ty = LI->getType();

    // Handle integer types.
    if (ty->isIntegerTy()) {
      unsigned bits = ty->getIntegerBitWidth();
      unsigned bytes = (bits + 7) / 8;
      if (bytes > 8)
        continue;
      auto val = map->readInt(*addr, bytes);
      if (!val)
        continue;
      // Truncate to the exact bit width.
      auto *replacement = llvm::ConstantInt::get(ty, *val);
      LI->replaceAllUsesWith(replacement);
      LI->eraseFromParent();
      changed = true;
      continue;
    }

    // Handle float types.
    if (ty->isFloatTy()) {
      auto val = map->readInt(*addr, 4);
      if (!val)
        continue;
      uint32_t bits = static_cast<uint32_t>(*val);
      float fval;
      std::memcpy(&fval, &bits, 4);
      auto *replacement =
          llvm::ConstantFP::get(ty, static_cast<double>(fval));
      LI->replaceAllUsesWith(replacement);
      LI->eraseFromParent();
      changed = true;
      continue;
    }

    if (ty->isDoubleTy()) {
      auto val = map->readInt(*addr, 8);
      if (!val)
        continue;
      double dval;
      std::memcpy(&dval, &*val, 8);
      auto *replacement = llvm::ConstantFP::get(ty, dval);
      LI->replaceAllUsesWith(replacement);
      LI->eraseFromParent();
      changed = true;
      continue;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

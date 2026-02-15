#include "omill/Passes/OutlineConstantStackData.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>

namespace omill {

namespace {

struct ConstantStoreInfo {
  llvm::StoreInst *inst;
  int64_t offset;
};

/// Recursively analyze uses of a pointer derived from an alloca.
/// Returns false if the alloca cannot be promoted to a global constant.
bool analyzeUses(llvm::Value *ptr, llvm::AllocaInst *AI,
                 const llvm::DataLayout &DL, int64_t base_offset,
                 bool offset_known,
                 llvm::SmallVectorImpl<ConstantStoreInfo> &stores,
                 llvm::SmallVectorImpl<llvm::Instruction *> &dead) {
  for (auto *U : ptr->users()) {
    if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
      llvm::APInt gep_off(64, 0);
      bool constant_gep = GEP->accumulateConstantOffset(DL, gep_off);
      int64_t new_off =
          base_offset + (constant_gep ? gep_off.getSExtValue() : 0);
      if (!analyzeUses(GEP, AI, DL, new_off, offset_known && constant_gep,
                       stores, dead))
        return false;
    } else if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
      // Storing the alloca pointer itself somewhere means it escapes.
      if (SI->getValueOperand() == ptr)
        return false;
      if (!offset_known)
        return false;
      auto *val = SI->getValueOperand();
      if (!llvm::isa<llvm::ConstantInt>(val) &&
          !llvm::isa<llvm::ConstantDataSequential>(val) &&
          !llvm::isa<llvm::ConstantAggregateZero>(val))
        return false;
      if (SI->getParent() != &AI->getFunction()->getEntryBlock())
        return false;
      stores.push_back({SI, base_offset});
    } else if (llvm::isa<llvm::LoadInst>(U)) {
      // Loads are fine — they'll read from the global after promotion.
    } else if (llvm::isa<llvm::PtrToIntInst>(U)) {
      // ptrtoint is fine — will reference the global after promotion.
    } else if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(U)) {
      auto id = II->getIntrinsicID();
      if (id == llvm::Intrinsic::lifetime_start ||
          id == llvm::Intrinsic::lifetime_end) {
        dead.push_back(II);
        continue;
      }
      return false;
    } else {
      return false;
    }
  }
  return true;
}

}  // namespace

llvm::PreservedAnalyses OutlineConstantStackDataPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  auto &DL = F.getDataLayout();
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();
  bool changed = false;

  llvm::SmallVector<llvm::AllocaInst *, 4> allocas;
  for (auto &I : F.getEntryBlock())
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I))
      allocas.push_back(AI);

  for (auto *AI : allocas) {
    if (!AI->isStaticAlloca())
      continue;
    auto alloc_size = AI->getAllocationSize(DL);
    if (!alloc_size || alloc_size->isScalable())
      continue;
    uint64_t size = alloc_size->getFixedValue();
    if (size == 0 || size > 4096)
      continue;

    llvm::SmallVector<ConstantStoreInfo, 8> stores;
    llvm::SmallVector<llvm::Instruction *, 4> dead;

    if (!analyzeUses(AI, AI, DL, 0, true, stores, dead))
      continue;
    if (stores.empty())
      continue;

    // Sort stores by instruction order so overlapping writes resolve correctly
    // (last write wins).
    llvm::sort(stores, [](const ConstantStoreInfo &a,
                          const ConstantStoreInfo &b) {
      return a.inst->comesBefore(b.inst);
    });

    // Build byte array from constant stores.
    std::vector<uint8_t> bytes(size, 0);
    for (auto &[SI, offset] : stores) {
      auto *val = SI->getValueOperand();
      unsigned store_size = DL.getTypeStoreSize(val->getType());

      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(val)) {
        llvm::APInt apval = CI->getValue();
        for (unsigned i = 0; i < store_size; ++i) {
          int64_t idx = offset + i;
          if (idx >= 0 && static_cast<uint64_t>(idx) < size)
            bytes[idx] = apval.extractBitsAsZExtValue(8, i * 8);
        }
      } else if (auto *CDS = llvm::dyn_cast<llvm::ConstantDataSequential>(val)) {
        llvm::StringRef raw = CDS->getRawDataValues();
        for (unsigned i = 0; i < raw.size() && i < store_size; ++i) {
          int64_t idx = offset + i;
          if (idx >= 0 && static_cast<uint64_t>(idx) < size)
            bytes[idx] = static_cast<uint8_t>(raw[i]);
        }
      }
      // ConstantAggregateZero: all zeros, already default in bytes array.
    }

    // Create global constant.
    auto *initializer = llvm::ConstantDataArray::get(Ctx, bytes);
    auto *GV = new llvm::GlobalVariable(
        M, initializer->getType(), /*isConstant=*/true,
        llvm::GlobalValue::PrivateLinkage, initializer, ".const_stack");
    GV->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    GV->setAlignment(AI->getAlign());

    // Delete stores and lifetime markers.
    for (auto &[SI, offset] : stores)
      SI->eraseFromParent();
    for (auto *I : dead)
      I->eraseFromParent();

    // Replace alloca with global constant pointer.
    AI->replaceAllUsesWith(GV);
    AI->eraseFromParent();
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

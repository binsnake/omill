#include "omill/Passes/RecoverStackFrameTypes.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <map>

namespace omill {

namespace {

struct FieldAccess {
  unsigned offset;
  llvm::Type *type;
  unsigned size;
};

/// Collect all constant-offset GEP users of an alloca that have load/store
/// users, recording {offset, accessed type, size}.
void collectFieldAccesses(llvm::AllocaInst *AI,
                          const llvm::DataLayout &DL,
                          std::map<unsigned, FieldAccess> &accesses) {
  for (auto *U : AI->users()) {
    auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(U);
    if (!GEP) continue;

    llvm::APInt offset_ap(64, 0);
    if (!GEP->accumulateConstantOffset(DL, offset_ap)) continue;
    unsigned offset = static_cast<unsigned>(offset_ap.getZExtValue());

    // Check GEP users for loads/stores to determine the accessed type.
    for (auto *GU : GEP->users()) {
      llvm::Type *accessed_ty = nullptr;
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(GU)) {
        accessed_ty = LI->getType();
      } else if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(GU)) {
        if (SI->getPointerOperand() == GEP) {
          accessed_ty = SI->getValueOperand()->getType();
        }
      }

      if (!accessed_ty) continue;
      unsigned size = DL.getTypeStoreSize(accessed_ty);

      auto it = accesses.find(offset);
      if (it == accesses.end()) {
        accesses[offset] = {offset, accessed_ty, size};
      } else {
        // If multiple accesses at same offset, keep the larger one.
        if (size > it->second.size) {
          it->second = {offset, accessed_ty, size};
        }
      }
    }
  }
}

/// Build a StructType from sorted field accesses, inserting padding as needed.
llvm::StructType *buildStructType(llvm::LLVMContext &Ctx,
                                  const std::map<unsigned, FieldAccess> &accesses,
                                  unsigned total_size) {
  llvm::SmallVector<llvm::Type *, 16> fields;
  // Map from field access offset → index in the struct.
  unsigned current_offset = 0;

  for (auto &[offset, access] : accesses) {
    if (offset > current_offset) {
      // Insert padding.
      unsigned pad = offset - current_offset;
      fields.push_back(llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), pad));
    } else if (offset < current_offset) {
      // Overlapping access — skip.
      continue;
    }

    fields.push_back(access.type);
    current_offset = offset + access.size;
  }

  // Trailing padding.
  if (current_offset < total_size) {
    unsigned pad = total_size - current_offset;
    fields.push_back(llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), pad));
  }

  return llvm::StructType::get(Ctx, fields, /*isPacked=*/true);
}

/// Build a mapping from byte offset → struct field index for the fields
/// that correspond to actual accesses (not padding).
void buildOffsetToFieldIndex(const std::map<unsigned, FieldAccess> &accesses,
                             unsigned total_size,
                             llvm::DenseMap<unsigned, unsigned> &offset_to_idx) {
  unsigned idx = 0;
  unsigned current_offset = 0;

  for (auto &[offset, access] : accesses) {
    if (offset > current_offset) {
      idx++;  // padding field
    } else if (offset < current_offset) {
      continue;  // overlapping, skipped
    }

    offset_to_idx[offset] = idx;
    idx++;
    current_offset = offset + access.size;
  }
}

}  // namespace

llvm::PreservedAnalyses RecoverStackFrameTypesPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.empty()) return llvm::PreservedAnalyses::all();

  auto &DL = F.getParent()->getDataLayout();
  bool changed = false;

  // Collect stack_frame allocas.
  llvm::SmallVector<llvm::AllocaInst *, 4> frame_allocas;
  for (auto &I : F.getEntryBlock()) {
    auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
    if (!AI) continue;
    if (!AI->getName().starts_with("stack_frame")) continue;

    auto *arr_ty = llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType());
    if (!arr_ty) continue;
    if (arr_ty->getElementType() != llvm::Type::getInt8Ty(F.getContext()))
      continue;

    frame_allocas.push_back(AI);
  }

  for (auto *AI : frame_allocas) {
    auto *arr_ty = llvm::cast<llvm::ArrayType>(AI->getAllocatedType());
    unsigned total_size = arr_ty->getNumElements();

    // Step 1: Collect field accesses.
    std::map<unsigned, FieldAccess> accesses;
    collectFieldAccesses(AI, DL, accesses);

    if (accesses.empty()) continue;

    // Step 2: Build struct type and offset→index mapping.
    auto *struct_ty = buildStructType(F.getContext(), accesses, total_size);

    llvm::DenseMap<unsigned, unsigned> offset_to_idx;
    buildOffsetToFieldIndex(accesses, total_size, offset_to_idx);

    // Step 3: Create new alloca with struct type.
    llvm::IRBuilder<> Builder(AI);
    auto *new_alloca = Builder.CreateAlloca(struct_ty, nullptr,
                                            AI->getName() + ".typed");

    // Step 4: Rewrite GEP users.
    llvm::SmallVector<llvm::GetElementPtrInst *, 16> geps;
    for (auto *U : AI->users()) {
      if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(U)) {
        geps.push_back(GEP);
      }
    }

    for (auto *GEP : geps) {
      llvm::APInt offset_ap(64, 0);
      if (!GEP->accumulateConstantOffset(DL, offset_ap)) continue;
      unsigned offset = static_cast<unsigned>(offset_ap.getZExtValue());

      auto it = offset_to_idx.find(offset);
      if (it == offset_to_idx.end()) continue;

      llvm::IRBuilder<> B(GEP);
      auto *zero = B.getInt32(0);
      auto *field_idx = B.getInt32(it->second);
      auto *new_gep = B.CreateGEP(struct_ty, new_alloca,
                                   {zero, field_idx},
                                   GEP->getName());

      GEP->replaceAllUsesWith(new_gep);
      GEP->eraseFromParent();
      changed = true;
    }

    // If all GEPs were rewritten, remove old alloca (if no remaining users).
    if (AI->use_empty()) {
      AI->eraseFromParent();
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

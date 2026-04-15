#pragma once

#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>

namespace omill {

/// Resolve a pointer to its constant byte offset from the State struct (arg0).
/// Walks through GEP chains and bitcasts. Returns -1 if not resolvable.
inline int64_t resolveStateOffset(llvm::Value *ptr,
                                  const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }
  return -1;
}

/// Resolve a pointer to its constant byte offset from a known base alloca.
/// Returns -1 if not resolvable.
inline int64_t resolveAllocaOffset(llvm::Value *ptr, llvm::AllocaInst *alloca,
                                   const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (base == alloca && total_offset >= 0)
    return total_offset;
  return -1;
}

}  // namespace omill

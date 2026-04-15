#include "omill/Passes/DeadStateStoreDSE.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/StateOffsetUtils.h"

namespace omill {

namespace {

/// Win64 volatile (caller-saved) GPR register names.
/// Stores to these State fields are dead at call boundaries because the callee
/// clobbers them.
static constexpr const char *kVolatileGPRs[] = {
    "RAX", "RCX", "RDX", "R8", "R9", "R10", "R11",
};

/// Win64 callee-saved registers.  Stores to these are NOT dead at call
/// boundaries — the callee preserves them.
static constexpr const char *kCalleeSavedGPRs[] = {
    "RBX", "RBP", "RDI", "RSI", "R12", "R13", "R14", "R15",
};

/// Check if a call instruction passes the State alloca (or a derived pointer)
/// as an argument.  If so, the call is "State-escaping" and we can't eliminate
/// stores before it.
bool callUsesState(llvm::CallBase *call, llvm::AllocaInst *state_alloca) {
  for (unsigned i = 0; i < call->arg_size(); ++i) {
    llvm::Value *arg = call->getArgOperand(i);
    // Walk through bitcasts/GEPs to find the base.
    llvm::Value *base = arg->stripPointerCasts();
    if (base == state_alloca)
      return true;
    // Also check GEP chains.
    while (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      base = GEP->getPointerOperand()->stripPointerCasts();
      if (base == state_alloca)
        return true;
    }
  }
  return false;
}

/// Find the State alloca in a function.  RecoverFunctionSignatures creates
/// this as `alloca %struct.State` named "state" in _native wrappers.
llvm::AllocaInst *findStateAlloca(llvm::Function &F) {
  for (auto &I : F.getEntryBlock()) {
    auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
    if (!AI)
      continue;
    auto *ty = AI->getAllocatedType();
    if (auto *ST = llvm::dyn_cast<llvm::StructType>(ty)) {
      if (ST->hasName() && ST->getName() == "struct.State")
        return AI;
    }
  }
  return nullptr;
}

/// Build the set of volatile field offsets from the State struct.
/// We use the known GPR layout: volatile regs are at specific offsets.
/// Also includes XMM0-5 as volatile (vector registers at known offsets).
llvm::DenseSet<int64_t> buildVolatileOffsets(llvm::Module &M) {
  llvm::DenseSet<int64_t> offsets;

  // Find __remill_basic_block to resolve register names → offsets.
  auto *bb_fn = M.getFunction("__remill_basic_block");
  if (!bb_fn || bb_fn->empty())
    return offsets;

  // Scan the basic block function for named GEPs.
  llvm::DenseMap<llvm::StringRef, int64_t> name_to_offset;
  auto &DL = M.getDataLayout();
  for (auto &I : bb_fn->getEntryBlock()) {
    auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
    if (!GEP || !GEP->hasName())
      continue;
    llvm::APInt ap(64, 0);
    if (GEP->accumulateConstantOffset(DL, ap))
      name_to_offset[GEP->getName()] = ap.getSExtValue();
  }

  // Mark volatile GPRs.
  for (auto *name : kVolatileGPRs) {
    auto it = name_to_offset.find(name);
    if (it != name_to_offset.end())
      offsets.insert(it->second);
  }

  // Mark XMM0-5 as volatile.  XMM registers in remill State are VectorReg
  // entries at 64-byte stride.  We mark the first 16 bytes (XMM portion)
  // of each volatile XMM register.
  for (unsigned i = 0; i < 6; ++i) {
    // XMM0-5 bases: need to find via name_to_offset or compute.
    // XMM register names might be "XMM0", "YMM0", etc.
    std::string xmm_name = "XMM" + std::to_string(i);
    auto it = name_to_offset.find(xmm_name);
    if (it != name_to_offset.end()) {
      // Mark all 16 bytes of the XMM register as volatile.
      for (int64_t off = 0; off < 16; off += 8)
        offsets.insert(it->second + off);
    }
  }

  return offsets;
}

/// Build the set of callee-saved field offsets.  Stores to these fields
/// must be preserved across calls.
llvm::DenseSet<int64_t> buildCalleeSavedOffsets(llvm::Module &M) {
  llvm::DenseSet<int64_t> offsets;

  auto *bb_fn = M.getFunction("__remill_basic_block");
  if (!bb_fn || bb_fn->empty())
    return offsets;

  auto &DL = M.getDataLayout();
  for (auto &I : bb_fn->getEntryBlock()) {
    auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
    if (!GEP || !GEP->hasName())
      continue;
    for (auto *name : kCalleeSavedGPRs) {
      if (GEP->getName() == name) {
        llvm::APInt ap(64, 0);
        if (GEP->accumulateConstantOffset(DL, ap))
          offsets.insert(ap.getSExtValue());
      }
    }
  }
  return offsets;
}

}  // namespace

llvm::PreservedAnalyses DeadStateStoreDSEPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration() || F.empty())
    return llvm::PreservedAnalyses::all();

  // Only process _native wrappers (after inlining).
  if (!F.getName().ends_with("_native"))
    return llvm::PreservedAnalyses::all();

  auto *state_alloca = findStateAlloca(F);
  if (!state_alloca)
    return llvm::PreservedAnalyses::all();

  auto &DL = F.getParent()->getDataLayout();
  auto volatile_offsets = buildVolatileOffsets(*F.getParent());
  if (volatile_offsets.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;
  llvm::SmallVector<llvm::StoreInst *, 16> to_erase;

  for (auto &BB : F) {
    // Forward scan through the basic block.
    // Track: for each volatile State field offset, the last store that
    // hasn't been read yet (candidate for elimination).
    llvm::DenseMap<int64_t, llvm::StoreInst *> last_store;

    for (auto &I : BB) {
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveAllocaOffset(SI->getPointerOperand(),
                                          state_alloca, DL);
        if (off < 0)
          continue;

        if (!volatile_offsets.count(off))
          continue;

        // If there's already a pending store to this field, the old one
        // is dead (overwritten without read).
        auto it = last_store.find(off);
        if (it != last_store.end()) {
          to_erase.push_back(it->second);
        }
        last_store[off] = SI;
        continue;
      }

      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveAllocaOffset(LI->getPointerOperand(),
                                          state_alloca, DL);
        if (off >= 0) {
          // This field is read — the pending store is NOT dead.
          last_store.erase(off);
        }
        continue;
      }

      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        if (callUsesState(CB, state_alloca)) {
          // Call passes State — the callee might read any field.
          // Can't eliminate any pending stores.
          last_store.clear();
        } else {
          // Call doesn't use State — it's a native call.
          // All volatile fields are clobbered by the call, so pending
          // stores to volatile fields are dead.
          for (auto &[off, store] : last_store) {
            to_erase.push_back(store);
          }
          last_store.clear();
        }
        continue;
      }
    }

    // At block end: for blocks with no successors (return), pending stores
    // to volatile fields are dead (no one reads them after function exit).
    auto *term = BB.getTerminator();
    if (term && llvm::isa<llvm::ReturnInst>(term)) {
      for (auto &[off, store] : last_store) {
        to_erase.push_back(store);
      }
    }
    // For blocks with successors, we conservatively keep pending stores
    // (inter-block analysis would require dataflow — not worth the complexity
    // for a pre-SROA cleanup pass).
  }

  // Erase dead stores.
  for (auto *SI : to_erase) {
    SI->eraseFromParent();
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

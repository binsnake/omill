#include "omill/Passes/PromoteStateToSSA.h"

#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

int64_t resolveStateOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
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

/// Get the State pointer (first function argument).
llvm::Value *getStatePtr(llvm::Function &F) {
  if (F.arg_size() > 0) {
    return F.getArg(0);
  }
  return nullptr;
}

/// Build a GEP to a State field at a given byte offset.
llvm::Value *buildStateFieldGEP(llvm::IRBuilder<> &Builder,
                                 llvm::Value *state_ptr,
                                 unsigned offset,
                                 llvm::Type *field_type,
                                 const llvm::DataLayout &DL) {
  // Use a raw byte-offset GEP through i8*
  auto *i8_ptr = Builder.CreateBitCast(state_ptr, Builder.getPtrTy());
  auto *gep = Builder.CreateConstGEP1_64(Builder.getInt8Ty(), i8_ptr, offset);
  return gep;
}

}  // namespace

llvm::PreservedAnalyses PromoteStateToSSAPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &DL = F.getParent()->getDataLayout();
  llvm::Value *state_ptr = getStatePtr(F);
  if (!state_ptr) {
    return llvm::PreservedAnalyses::all();
  }

  // Phase 1: Collect all State field accesses and group by offset.
  struct FieldInfo {
    unsigned offset;
    llvm::Type *type;
    unsigned max_access_size = 0;
    llvm::SmallVector<llvm::LoadInst *, 4> loads;
    llvm::SmallVector<llvm::StoreInst *, 4> stores;
    bool is_live_in = false;
  };

  llvm::DenseMap<unsigned, FieldInfo> fields;

  // Track which offsets are read before written (live-in).
  llvm::DenseSet<unsigned> written_before_read;
  llvm::DenseSet<unsigned> first_access_seen;

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off < 0) continue;

        unsigned u_off = static_cast<unsigned>(off);
        auto &info = fields[u_off];
        info.offset = u_off;
        unsigned sz = DL.getTypeStoreSize(LI->getType());
        if (sz > info.max_access_size) {
          info.max_access_size = sz;
          info.type = LI->getType();
        }
        info.loads.push_back(LI);

        if (!first_access_seen.count(u_off)) {
          first_access_seen.insert(u_off);
          info.is_live_in = true;
        }
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off < 0) continue;

        unsigned u_off = static_cast<unsigned>(off);
        auto &info = fields[u_off];
        info.offset = u_off;
        unsigned sz = DL.getTypeStoreSize(SI->getValueOperand()->getType());
        if (sz > info.max_access_size) {
          info.max_access_size = sz;
          info.type = SI->getValueOperand()->getType();
        }
        info.stores.push_back(SI);

        if (!first_access_seen.count(u_off)) {
          first_access_seen.insert(u_off);
          // First access is a store — not live-in (in entry block path)
        }
      }
    }
  }

  if (fields.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  // Phase 2: Create an alloca for each accessed field.
  llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  llvm::DenseMap<unsigned, llvm::AllocaInst *> field_allocas;

  for (auto &[offset, info] : fields) {
    auto *alloca = EntryBuilder.CreateAlloca(info.type, nullptr,
                                              "state_" + std::to_string(offset));
    field_allocas[offset] = alloca;

    // If live-in, load the initial value from the State struct.
    if (info.is_live_in) {
      llvm::IRBuilder<> Builder(alloca->getNextNode());
      auto *gep = buildStateFieldGEP(Builder, state_ptr, offset,
                                      info.type, DL);
      auto *initial = Builder.CreateLoad(info.type, gep, "state_init");
      Builder.CreateStore(initial, alloca);
    }
  }

  // Phase 3: Replace all State loads/stores with alloca loads/stores.
  for (auto &[offset, info] : fields) {
    auto *alloca = field_allocas[offset];

    for (auto *LI : info.loads) {
      llvm::IRBuilder<> Builder(LI);
      auto *new_load = Builder.CreateLoad(LI->getType(), alloca);
      LI->replaceAllUsesWith(new_load);
      LI->eraseFromParent();
    }

    for (auto *SI : info.stores) {
      llvm::IRBuilder<> Builder(SI);
      auto *val = SI->getValueOperand();
      Builder.CreateStore(val, alloca);

      // Decompose wide stores: if this store spans into other fields'
      // byte ranges, extract the overlapping sub-values and propagate
      // them.  This handles the case where a 128-bit MOVDQA writes both
      // halves of an XMM register but reads target each half individually.
      unsigned store_size = DL.getTypeStoreSize(val->getType());
      for (auto &[other_off, other_info] : fields) {
        if (other_off > offset && other_off < offset + store_size) {
          auto *other_alloca = field_allocas[other_off];
          unsigned byte_off = other_off - offset;
          auto *sub_ptr = Builder.CreateConstGEP1_64(
              Builder.getInt8Ty(), alloca, byte_off);
          auto *sub_val = Builder.CreateLoad(other_info.type, sub_ptr,
                                              "wide.sub");
          Builder.CreateStore(sub_val, other_alloca);
        }
      }

      SI->eraseFromParent();
    }
  }

  // Phase 4: Before each return-like terminator, store live-out fields
  // back to the State struct.
  for (auto &BB : F) {
    auto *term = BB.getTerminator();
    if (!term) continue;

    // Check if this block ends with a return or a tail call to a
    // control flow intrinsic (which acts as a return).
    bool is_exit = llvm::isa<llvm::ReturnInst>(term);
    if (!is_exit) {
      // Check for tail calls to __remill_function_return, etc.
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(
              BB.getTerminator()->getPrevNode())) {
        if (CI->isTailCall() || CI->isMustTailCall()) {
          is_exit = true;
        }
      }
    }

    if (!is_exit) continue;

    // Insert write-backs before the tail call (if present), not before
    // the ret.  LowerFunctionReturn inserts a new ret before the tail
    // call and then erases everything after it — so write-backs placed
    // between the tail call and the ret would be lost.
    llvm::Instruction *insert_point = term;
    if (auto *prev = term->getPrevNode()) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(prev)) {
        if (CI->isTailCall() || CI->isMustTailCall()) {
          insert_point = CI;
        }
      }
    }
    llvm::IRBuilder<> Builder(insert_point);
    for (auto &[offset, info] : fields) {
      if (info.stores.empty()) continue;  // Never written — skip write-back

      auto *alloca = field_allocas[offset];
      auto *val = Builder.CreateLoad(info.type, alloca);
      auto *gep = buildStateFieldGEP(Builder, state_ptr, offset,
                                      info.type, DL);
      Builder.CreateStore(val, gep);
    }
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

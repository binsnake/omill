#include "omill/Passes/LowerMemoryIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

namespace {

/// Get the LLVM type for a memory intrinsic's value based on its kind.
llvm::Type *getValueType(llvm::LLVMContext &Ctx, IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kReadMemory8:
    case IntrinsicKind::kWriteMemory8:
      return llvm::Type::getInt8Ty(Ctx);
    case IntrinsicKind::kReadMemory16:
    case IntrinsicKind::kWriteMemory16:
      return llvm::Type::getInt16Ty(Ctx);
    case IntrinsicKind::kReadMemory32:
    case IntrinsicKind::kWriteMemory32:
      return llvm::Type::getInt32Ty(Ctx);
    case IntrinsicKind::kReadMemory64:
    case IntrinsicKind::kWriteMemory64:
      return llvm::Type::getInt64Ty(Ctx);
    case IntrinsicKind::kReadMemoryF32:
    case IntrinsicKind::kWriteMemoryF32:
      return llvm::Type::getFloatTy(Ctx);
    case IntrinsicKind::kReadMemoryF64:
    case IntrinsicKind::kWriteMemoryF64:
      return llvm::Type::getDoubleTy(Ctx);
    case IntrinsicKind::kReadMemoryF80:
    case IntrinsicKind::kWriteMemoryF80:
      return llvm::Type::getX86_FP80Ty(Ctx);
    case IntrinsicKind::kReadMemoryF128:
    case IntrinsicKind::kWriteMemoryF128:
      return llvm::Type::getFP128Ty(Ctx);
    default:
      return nullptr;
  }
}

/// Lower a single read memory intrinsic call.
/// __remill_read_memory_N(mem, addr) -> load from inttoptr(addr)
void lowerReadMemory(llvm::CallInst *CI, IntrinsicKind kind) {
  auto &Ctx = CI->getContext();
  llvm::IRBuilder<> Builder(CI);

  llvm::Type *val_type = getValueType(Ctx, kind);
  if (!val_type) return;

  // arg0 = Memory*, arg1 = addr_t (i64)
  llvm::Value *addr = CI->getArgOperand(1);

  // f80 read is special: __remill_read_memory_f80(mem, addr, float80_t&)
  // It writes the result to the reference parameter and returns Memory*.
  if (kind == IntrinsicKind::kReadMemoryF80) {
    llvm::Value *out_ref = CI->getArgOperand(2);
    llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
    llvm::Value *loaded = Builder.CreateLoad(val_type, ptr);
    Builder.CreateStore(loaded, out_ref);

    // Replace Memory* return with input Memory*
    CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
    return;
  }

  // Standard read: convert addr to pointer, load value
  llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
  llvm::Value *loaded = Builder.CreateLoad(val_type, ptr);

  CI->replaceAllUsesWith(loaded);
  CI->eraseFromParent();
}

/// Lower a single write memory intrinsic call.
/// __remill_write_memory_N(mem, addr, val) -> store to inttoptr(addr)
void lowerWriteMemory(llvm::CallInst *CI, IntrinsicKind kind) {
  auto &Ctx = CI->getContext();
  llvm::IRBuilder<> Builder(CI);

  llvm::Type *val_type = getValueType(Ctx, kind);
  if (!val_type) return;

  // arg0 = Memory*, arg1 = addr_t, arg2 = value
  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *val = CI->getArgOperand(2);

  // f80 write is special: __remill_write_memory_f80(mem, addr, const float80_t&)
  // The value is passed by reference
  if (kind == IntrinsicKind::kWriteMemoryF80) {
    llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
    llvm::Value *loaded_val = Builder.CreateLoad(val_type, val);
    Builder.CreateStore(loaded_val, ptr);

    // Replace returned Memory* with input Memory*
    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();
    return;
  }

  // Standard write: convert addr to pointer, store value
  llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
  Builder.CreateStore(val, ptr);

  // The intrinsic returns a new Memory* — replace all uses with input Memory*
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

}  // namespace

llvm::PreservedAnalyses LowerMemoryIntrinsicsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  // Collect calls first, since we'll be modifying the IR.
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 32> pending;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      auto kind = table.classifyCall(CI);
      auto cat = IntrinsicTable::categoryOf(kind);
      if (cat == IntrinsicCategory::kMemoryRead ||
          cat == IntrinsicCategory::kMemoryWrite) {
        pending.push_back({CI, kind});
      }
    }
  }

  if (pending.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto &[CI, kind] : pending) {
    auto cat = IntrinsicTable::categoryOf(kind);
    if (cat == IntrinsicCategory::kMemoryRead) {
      lowerReadMemory(CI, kind);
    } else {
      lowerWriteMemory(CI, kind);
    }
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

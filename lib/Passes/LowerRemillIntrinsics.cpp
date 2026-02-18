#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/IntrinsicTable.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

// ===----------------------------------------------------------------------===
// Category 1: Flags — replace flag computation/comparison calls with arg0
// ===----------------------------------------------------------------------===

bool lowerFlagIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 32> to_lower;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto cat = IntrinsicTable::categoryOf(table.classifyCall(CI));
        if (cat == IntrinsicCategory::kFlag ||
            cat == IntrinsicCategory::kComparison)
          to_lower.push_back(CI);
      }

  if (to_lower.empty())
    return false;

  for (auto *CI : to_lower) {
    CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 2: Barriers — remove volatile inline asm and barrier intrinsics
// ===----------------------------------------------------------------------===

bool removeBarriers(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 32> to_remove;

  for (auto &BB : F)
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;

      if (CI->isInlineAsm()) {
        if (auto *IA = llvm::dyn_cast<llvm::InlineAsm>(CI->getCalledOperand()))
          if (IA->getAsmString().empty() && IA->hasSideEffects())
            to_remove.push_back(CI);
        continue;
      }

      auto kind = table.classifyCall(CI);
      switch (kind) {
        case IntrinsicKind::kBarrierLoadLoad:
        case IntrinsicKind::kBarrierLoadStore:
        case IntrinsicKind::kBarrierStoreLoad:
        case IntrinsicKind::kBarrierStoreStore:
        case IntrinsicKind::kDelaySlotBegin:
        case IntrinsicKind::kDelaySlotEnd:
          to_remove.push_back(CI);
          break;
        default:
          break;
      }
    }

  if (to_remove.empty())
    return false;

  for (auto *CI : to_remove) {
    if (!CI->getType()->isVoidTy() && CI->arg_size() > 0)
      CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 3: Memory — lower read/write memory intrinsics to load/store
// ===----------------------------------------------------------------------===

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

void lowerReadMemory(llvm::CallInst *CI, IntrinsicKind kind) {
  auto &Ctx = CI->getContext();
  llvm::IRBuilder<> Builder(CI);

  llvm::Type *val_type = getValueType(Ctx, kind);
  if (!val_type)
    return;

  llvm::Value *addr = CI->getArgOperand(1);

  if (kind == IntrinsicKind::kReadMemoryF80) {
    llvm::Value *out_ref = CI->getArgOperand(2);
    llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
    llvm::Value *loaded = Builder.CreateLoad(val_type, ptr);
    Builder.CreateStore(loaded, out_ref);
    CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
    return;
  }

  llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
  llvm::Value *loaded = Builder.CreateLoad(val_type, ptr);
  CI->replaceAllUsesWith(loaded);
  CI->eraseFromParent();
}

void lowerWriteMemory(llvm::CallInst *CI, IntrinsicKind kind) {
  auto &Ctx = CI->getContext();
  llvm::IRBuilder<> Builder(CI);

  llvm::Type *val_type = getValueType(Ctx, kind);
  if (!val_type)
    return;

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *val = CI->getArgOperand(2);

  if (kind == IntrinsicKind::kWriteMemoryF80) {
    llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
    llvm::Value *loaded_val = Builder.CreateLoad(val_type, val);
    Builder.CreateStore(loaded_val, ptr);
    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();
    return;
  }

  llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
  Builder.CreateStore(val, ptr);
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

bool lowerMemoryIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 32> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kMemoryRead ||
            cat == IntrinsicCategory::kMemoryWrite)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  for (auto &[CI, kind] : pending) {
    if (IntrinsicTable::categoryOf(kind) == IntrinsicCategory::kMemoryRead)
      lowerReadMemory(CI, kind);
    else
      lowerWriteMemory(CI, kind);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 4: Atomics — lower atomic operations
// ===----------------------------------------------------------------------===

unsigned getAtomicBitWidth(IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kCompareExchange8:
    case IntrinsicKind::kFetchAndAdd8:
    case IntrinsicKind::kFetchAndSub8:
    case IntrinsicKind::kFetchAndAnd8:
    case IntrinsicKind::kFetchAndOr8:
    case IntrinsicKind::kFetchAndXor8:
    case IntrinsicKind::kFetchAndNand8:
      return 8;
    case IntrinsicKind::kCompareExchange16:
    case IntrinsicKind::kFetchAndAdd16:
    case IntrinsicKind::kFetchAndSub16:
    case IntrinsicKind::kFetchAndAnd16:
    case IntrinsicKind::kFetchAndOr16:
    case IntrinsicKind::kFetchAndXor16:
    case IntrinsicKind::kFetchAndNand16:
      return 16;
    case IntrinsicKind::kCompareExchange32:
    case IntrinsicKind::kFetchAndAdd32:
    case IntrinsicKind::kFetchAndSub32:
    case IntrinsicKind::kFetchAndAnd32:
    case IntrinsicKind::kFetchAndOr32:
    case IntrinsicKind::kFetchAndXor32:
    case IntrinsicKind::kFetchAndNand32:
      return 32;
    case IntrinsicKind::kCompareExchange64:
    case IntrinsicKind::kFetchAndAdd64:
    case IntrinsicKind::kFetchAndSub64:
    case IntrinsicKind::kFetchAndAnd64:
    case IntrinsicKind::kFetchAndOr64:
    case IntrinsicKind::kFetchAndXor64:
    case IntrinsicKind::kFetchAndNand64:
      return 64;
    case IntrinsicKind::kCompareExchange128:
      return 128;
    default:
      return 0;
  }
}

llvm::AtomicRMWInst::BinOp getFetchAndOp(IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kFetchAndAdd8:
    case IntrinsicKind::kFetchAndAdd16:
    case IntrinsicKind::kFetchAndAdd32:
    case IntrinsicKind::kFetchAndAdd64:
      return llvm::AtomicRMWInst::Add;
    case IntrinsicKind::kFetchAndSub8:
    case IntrinsicKind::kFetchAndSub16:
    case IntrinsicKind::kFetchAndSub32:
    case IntrinsicKind::kFetchAndSub64:
      return llvm::AtomicRMWInst::Sub;
    case IntrinsicKind::kFetchAndAnd8:
    case IntrinsicKind::kFetchAndAnd16:
    case IntrinsicKind::kFetchAndAnd32:
    case IntrinsicKind::kFetchAndAnd64:
      return llvm::AtomicRMWInst::And;
    case IntrinsicKind::kFetchAndOr8:
    case IntrinsicKind::kFetchAndOr16:
    case IntrinsicKind::kFetchAndOr32:
    case IntrinsicKind::kFetchAndOr64:
      return llvm::AtomicRMWInst::Or;
    case IntrinsicKind::kFetchAndXor8:
    case IntrinsicKind::kFetchAndXor16:
    case IntrinsicKind::kFetchAndXor32:
    case IntrinsicKind::kFetchAndXor64:
      return llvm::AtomicRMWInst::Xor;
    case IntrinsicKind::kFetchAndNand8:
    case IntrinsicKind::kFetchAndNand16:
    case IntrinsicKind::kFetchAndNand32:
    case IntrinsicKind::kFetchAndNand64:
      return llvm::AtomicRMWInst::Nand;
    default:
      return llvm::AtomicRMWInst::BAD_BINOP;
  }
}

void lowerCompareExchange(llvm::CallInst *CI, unsigned bit_width) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *expected_ref = CI->getArgOperand(2);
  llvm::Value *desired = CI->getArgOperand(3);

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());

  llvm::Value *expected = Builder.CreateLoad(int_ty, expected_ref);

  if (bit_width == 128)
    desired = Builder.CreateLoad(int_ty, desired);

  auto *cmpxchg = Builder.CreateAtomicCmpXchg(
      ptr, expected, desired, llvm::MaybeAlign(),
      llvm::AtomicOrdering::SequentiallyConsistent,
      llvm::AtomicOrdering::SequentiallyConsistent);

  auto *old_val = Builder.CreateExtractValue(cmpxchg, 0);
  Builder.CreateStore(old_val, expected_ref);

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void lowerFetchAndOp(llvm::CallInst *CI, IntrinsicKind kind,
                     unsigned bit_width) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *value_ref = CI->getArgOperand(2);

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());

  llvm::Value *value = Builder.CreateLoad(int_ty, value_ref);

  auto binop = getFetchAndOp(kind);

  auto *result = Builder.CreateAtomicRMW(
      binop, ptr, value, llvm::MaybeAlign(),
      llvm::AtomicOrdering::SequentiallyConsistent);

  Builder.CreateStore(result, value_ref);

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

bool lowerAtomicIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 16> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kAtomic ||
            cat == IntrinsicCategory::kFetchAndOp)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  for (auto &[CI, kind] : pending) {
    switch (kind) {
      case IntrinsicKind::kAtomicBegin:
      case IntrinsicKind::kAtomicEnd:
        CI->replaceAllUsesWith(CI->getArgOperand(0));
        CI->eraseFromParent();
        break;
      case IntrinsicKind::kCompareExchange8:
      case IntrinsicKind::kCompareExchange16:
      case IntrinsicKind::kCompareExchange32:
      case IntrinsicKind::kCompareExchange64:
      case IntrinsicKind::kCompareExchange128:
        lowerCompareExchange(CI, getAtomicBitWidth(kind));
        break;
      default:
        if (IntrinsicTable::categoryOf(kind) == IntrinsicCategory::kFetchAndOp)
          lowerFetchAndOp(CI, kind, getAtomicBitWidth(kind));
        break;
    }
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 5: HyperCalls — CPUID, RDTSC, async, IO, FPU, x86-specific
// ===----------------------------------------------------------------------===

llvm::FunctionCallee getOrDeclareHelper(llvm::Module &M, llvm::StringRef name,
                                         llvm::FunctionType *FT) {
  if (auto *F = M.getFunction(name))
    return F;
  return M.getOrInsertFunction(name, FT);
}

enum SyncHyperCallID : uint32_t {
  kX86CPUID = 258,
  kX86ReadTSC = 259,
  kX86ReadTSCP = 260,
};

enum StateGPROffset : uint64_t {
  kRAX = 2216,
  kRBX = 2232,
  kRCX = 2248,
  kRDX = 2264,
};

llvm::Value *stateFieldPtr(llvm::IRBuilder<> &B, llvm::Value *state,
                            uint64_t byte_offset) {
  return B.CreateInBoundsGEP(llvm::Type::getInt8Ty(B.getContext()), state,
                              B.getInt64(byte_offset));
}

void emitCPUID(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *eax_ptr = stateFieldPtr(B, state, kRAX);
  auto *ecx_ptr = stateFieldPtr(B, state, kRCX);
  auto *leaf = B.CreateLoad(i32_ty, eax_ptr, "cpuid.leaf");
  auto *subleaf = B.CreateLoad(i32_ty, ecx_ptr, "cpuid.subleaf");

  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty, i32_ty, i32_ty),
      {i32_ty, i32_ty}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "cpuid",
      "={eax},={ebx},={ecx},={edx},{eax},{ecx},~{dirflag},~{fpsr},~{flags}",
      true);
  auto *result = B.CreateCall(asm_ty, ia, {leaf, subleaf}, "cpuid");

  B.CreateStore(B.CreateExtractValue(result, 0), stateFieldPtr(B, state, kRAX));
  B.CreateStore(B.CreateExtractValue(result, 1), stateFieldPtr(B, state, kRBX));
  B.CreateStore(B.CreateExtractValue(result, 2), stateFieldPtr(B, state, kRCX));
  B.CreateStore(B.CreateExtractValue(result, 3), stateFieldPtr(B, state, kRDX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void emitRDTSC(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *rdtsc_fn = llvm::Intrinsic::getOrInsertDeclaration(
      CI->getModule(), llvm::Intrinsic::readcyclecounter);
  auto *tsc = B.CreateCall(rdtsc_fn, {}, "rdtsc");

  auto *lo = B.CreateTrunc(tsc, i32_ty, "rdtsc.lo");
  auto *hi = B.CreateTrunc(
      B.CreateLShr(tsc, llvm::ConstantInt::get(i64_ty, 32)),
      i32_ty, "rdtsc.hi");

  B.CreateStore(lo, stateFieldPtr(B, state, kRAX));
  B.CreateStore(hi, stateFieldPtr(B, state, kRDX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void emitRDTSCP(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty, i32_ty), {}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "rdtscp",
      "={eax},={edx},={ecx},~{dirflag},~{fpsr},~{flags}", true);
  auto *result = B.CreateCall(asm_ty, ia, {}, "rdtscp");

  B.CreateStore(B.CreateExtractValue(result, 0), stateFieldPtr(B, state, kRAX));
  B.CreateStore(B.CreateExtractValue(result, 1), stateFieldPtr(B, state, kRDX));
  B.CreateStore(B.CreateExtractValue(result, 2), stateFieldPtr(B, state, kRCX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void emitGenericSyncStub(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();

  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);
  llvm::Value *hyper_call_id = CI->getArgOperand(2);

  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());
  auto *i32_ty = llvm::Type::getInt32Ty(CI->getContext());
  auto *FT = llvm::FunctionType::get(void_ty, {state->getType(), i32_ty}, false);
  auto callee = getOrDeclareHelper(M, "__omill_sync_hyper_call", FT);

  Builder.CreateCall(callee, {state, hyper_call_id});
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void lowerSyncHyperCall(llvm::CallInst *CI) {
  auto *id = CI->getArgOperand(2);
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(id);
  if (!ci) {
    emitGenericSyncStub(CI);
    return;
  }

  switch (ci->getZExtValue()) {
    case kX86CPUID:
      emitCPUID(CI);
      break;
    case kX86ReadTSC:
      emitRDTSC(CI);
      break;
    case kX86ReadTSCP:
      emitRDTSCP(CI);
      break;
    default:
      emitGenericSyncStub(CI);
      break;
  }
}

void lowerAsyncHyperCall(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();

  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *ret_addr = CI->getArgOperand(1);
  llvm::Value *mem = CI->getArgOperand(2);

  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());
  auto *i64_ty = llvm::Type::getInt64Ty(CI->getContext());
  auto *FT = llvm::FunctionType::get(void_ty, {state->getType(), i64_ty}, false);
  auto callee = getOrDeclareHelper(M, "__omill_async_hyper_call", FT);

  Builder.CreateCall(callee, {state, ret_addr});
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void lowerIOPort(llvm::CallInst *CI, IntrinsicKind kind) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();
  auto &Ctx = CI->getContext();

  bool is_read = (kind == IntrinsicKind::kReadIOPort8 ||
                  kind == IntrinsicKind::kReadIOPort16 ||
                  kind == IntrinsicKind::kReadIOPort32);

  unsigned bit_width;
  switch (kind) {
    case IntrinsicKind::kReadIOPort8:
    case IntrinsicKind::kWriteIOPort8:
      bit_width = 8;
      break;
    case IntrinsicKind::kReadIOPort16:
    case IntrinsicKind::kWriteIOPort16:
      bit_width = 16;
      break;
    default:
      bit_width = 32;
      break;
  }

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  if (is_read) {
    auto *FT = llvm::FunctionType::get(int_ty, {i64_ty}, false);
    std::string name = "__omill_read_io_port_" + std::to_string(bit_width);
    auto callee = getOrDeclareHelper(M, name, FT);
    auto *result = Builder.CreateCall(callee, {CI->getArgOperand(1)});
    CI->replaceAllUsesWith(result);
  } else {
    auto *void_ty = llvm::Type::getVoidTy(Ctx);
    auto *FT = llvm::FunctionType::get(void_ty, {i64_ty, int_ty}, false);
    std::string name = "__omill_write_io_port_" + std::to_string(bit_width);
    auto callee = getOrDeclareHelper(M, name, FT);
    Builder.CreateCall(callee, {CI->getArgOperand(1), CI->getArgOperand(2)});
    CI->replaceAllUsesWith(CI->getArgOperand(0));
  }
  CI->eraseFromParent();
}

void lowerFPUOp(llvm::CallInst *CI, IntrinsicKind kind) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);

  switch (kind) {
    case IntrinsicKind::kFPUExceptionTest: {
      auto *FT = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
      auto callee = getOrDeclareHelper(M, "fetestexcept", FT);
      auto *result = Builder.CreateCall(callee, {CI->getArgOperand(0)});
      CI->replaceAllUsesWith(result);
      break;
    }
    case IntrinsicKind::kFPUExceptionClear: {
      auto *FT = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
      auto callee = getOrDeclareHelper(M, "feclearexcept", FT);
      Builder.CreateCall(callee, {CI->getArgOperand(0)});
      break;
    }
    case IntrinsicKind::kFPUExceptionRaise: {
      auto *FT = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
      auto callee = getOrDeclareHelper(M, "feraiseexcept", FT);
      Builder.CreateCall(callee, {CI->getArgOperand(0)});
      break;
    }
    case IntrinsicKind::kFPUSetRounding: {
      auto *FT = llvm::FunctionType::get(i32_ty, {i32_ty}, false);
      auto callee = getOrDeclareHelper(M, "fesetround", FT);
      Builder.CreateCall(callee, {CI->getArgOperand(0)});
      break;
    }
    case IntrinsicKind::kFPUGetRounding: {
      auto *FT = llvm::FunctionType::get(i32_ty, {}, false);
      auto callee = getOrDeclareHelper(M, "fegetround", FT);
      auto *result = Builder.CreateCall(callee, {});
      CI->replaceAllUsesWith(result);
      break;
    }
    default:
      return;
  }
  CI->eraseFromParent();
}

void lowerX86Specific(llvm::CallInst *CI) {
  CI->replaceAllUsesWith(CI->getArgOperand(0));
  CI->eraseFromParent();
}

bool lowerHyperCalls(llvm::Function &F, IntrinsicTable &table) {
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 16> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kHyperCall ||
            cat == IntrinsicCategory::kIOPort ||
            cat == IntrinsicCategory::kFPU ||
            cat == IntrinsicCategory::kX86Specific)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  for (auto &[CI, kind] : pending) {
    auto cat = IntrinsicTable::categoryOf(kind);
    switch (cat) {
      case IntrinsicCategory::kHyperCall:
        if (kind == IntrinsicKind::kSyncHyperCall)
          lowerSyncHyperCall(CI);
        else
          lowerAsyncHyperCall(CI);
        break;
      case IntrinsicCategory::kIOPort:
        lowerIOPort(CI, kind);
        break;
      case IntrinsicCategory::kFPU:
        lowerFPUOp(CI, kind);
        break;
      case IntrinsicCategory::kX86Specific:
        lowerX86Specific(CI);
        break;
      default:
        break;
    }
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 6: ErrorMissing — lower error/missing block handlers
// ===----------------------------------------------------------------------===

bool lowerErrorAndMissing(llvm::Function &F, IntrinsicTable &table) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 4> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        if (kind == IntrinsicKind::kError ||
            kind == IntrinsicKind::kMissingBlock)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *handler_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);

  auto error_handler =
      M.getOrInsertFunction("__omill_error_handler", handler_ty);
  auto missing_handler =
      M.getOrInsertFunction("__omill_missing_block_handler", handler_ty);

  for (auto &[CI, kind] : pending) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Value *pc = CI->getArgOperand(1);
    if (kind == IntrinsicKind::kError)
      Builder.CreateCall(error_handler, {pc});
    else
      Builder.CreateCall(missing_handler, {pc});

    auto *new_term =
        Builder.CreateRet(llvm::PoisonValue::get(F.getReturnType()));

    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 7: Return — lower __remill_function_return to ret
// ===----------------------------------------------------------------------===

bool lowerFunctionReturn(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 4> return_calls;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (table.classifyCall(CI) == IntrinsicKind::kFunctionReturn)
          return_calls.push_back(CI);

  if (return_calls.empty())
    return false;

  for (auto *CI : return_calls) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Instruction *new_term;
    if (F.getReturnType()->isVoidTy())
      new_term = Builder.CreateRetVoid();
    else
      new_term = Builder.CreateRet(CI->getArgOperand(2));

    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 8: Call — lower __remill_function_call
// ===----------------------------------------------------------------------===

bool lowerFunctionCall(llvm::Function &F, IntrinsicTable &table,
                       const LiftedFunctionMap *lifted) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  llvm::SmallVector<llvm::CallInst *, 8> call_intrinsics;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (table.classifyCall(CI) == IntrinsicKind::kFunctionCall)
          call_intrinsics.push_back(CI);

  if (call_intrinsics.empty())
    return false;

  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty = llvm::FunctionType::get(
      mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);

  for (auto *CI : call_intrinsics) {
    llvm::IRBuilder<> Builder(CI);
    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::Value *result = nullptr;

    if (auto *const_pc = llvm::dyn_cast<llvm::ConstantInt>(target_pc)) {
      auto *target_fn = lifted ? lifted->lookup(const_pc->getZExtValue())
                               : nullptr;
      if (target_fn)
        result = Builder.CreateCall(target_fn, {state, target_pc, mem});
    }

    if (!result) {
      auto dispatcher =
          M.getOrInsertFunction("__omill_dispatch_call", lifted_fn_ty);
      result = Builder.CreateCall(dispatcher, {state, target_pc, mem});
    }

    CI->replaceAllUsesWith(result);
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 9: Jump — lower __remill_jump
// ===----------------------------------------------------------------------===

bool lowerJump(llvm::Function &F, IntrinsicTable &table,
               const LiftedFunctionMap *lifted) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  llvm::SmallVector<llvm::CallInst *, 8> jump_calls;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (table.classifyCall(CI) == IntrinsicKind::kJump)
          jump_calls.push_back(CI);

  if (jump_calls.empty())
    return false;

  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty = llvm::FunctionType::get(
      mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);

  for (auto *CI : jump_calls) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::Instruction *new_term = nullptr;

    if (auto *const_pc = llvm::dyn_cast<llvm::ConstantInt>(target_pc)) {
      uint64_t pc_val = const_pc->getZExtValue();

      if (auto *target_bb = findBlockForPC(F, pc_val))
        new_term = Builder.CreateBr(target_bb);

      if (!new_term) {
        auto *target_fn = lifted ? lifted->lookup(pc_val) : nullptr;
        if (target_fn) {
          auto *tail_call =
              Builder.CreateCall(target_fn, {state, target_pc, mem});
          tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
          new_term = Builder.CreateRet(tail_call);
        }
      }
    }

    if (!new_term) {
      auto dispatcher =
          M.getOrInsertFunction("__omill_dispatch_jump", lifted_fn_ty);
      auto *result =
          Builder.CreateCall(dispatcher, {state, target_pc, mem});
      new_term = Builder.CreateRet(result);
    }

    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
        successors(BB).begin(), successors(BB).end());
    for (auto *old_succ : old_succs)
      if (!new_succs.count(old_succ))
        old_succ->removePredecessor(BB);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 10: Undefined — replace with freeze(poison)
// ===----------------------------------------------------------------------===

bool lowerUndefinedIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 16> to_lower;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (IntrinsicTable::categoryOf(table.classifyCall(CI)) ==
            IntrinsicCategory::kUndefined)
          to_lower.push_back(CI);

  if (to_lower.empty())
    return false;

  for (auto *CI : to_lower) {
    llvm::IRBuilder<> Builder(CI);
    auto *frozen = Builder.CreateFreeze(llvm::PoisonValue::get(CI->getType()));
    CI->replaceAllUsesWith(frozen);
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 11: ResolvedDispatch — lower dispatch_call(ptrtoint(@import))
//   to native Win64 calls
// ===----------------------------------------------------------------------===

static constexpr uint64_t kRCXOffset = 2248;
static constexpr uint64_t kRDXOffset = 2264;
static constexpr uint64_t kR8Offset = 2344;
static constexpr uint64_t kR9Offset = 2360;
static constexpr uint64_t kRAXOffset = 2216;

llvm::Value *buildStateLoad(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                            uint64_t offset, const llvm::Twine &name) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  return Builder.CreateLoad(Builder.getInt64Ty(), gep, name);
}

void buildStateStore(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                     uint64_t offset, llvm::Value *val) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  Builder.CreateStore(val, gep);
}

bool lowerResolvedDispatchCalls(llvm::Function &F) {
  if (F.arg_size() == 0)
    return false;

  llvm::SmallVector<llvm::CallInst *, 4> to_lower;

  for (auto &BB : F)
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->getName() != "__omill_dispatch_call")
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *ptoi =
          llvm::dyn_cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
      if (!ptoi)
        continue;
      auto *target_fn =
          llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
      if (!target_fn)
        continue;
      if (target_fn->getDLLStorageClass() !=
          llvm::GlobalValue::DLLImportStorageClass)
        continue;

      to_lower.push_back(call);
    }

  if (to_lower.empty())
    return false;

  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *native_ft = llvm::FunctionType::get(
      i64_ty, {i64_ty, i64_ty, i64_ty, i64_ty}, false);

  for (auto *call : to_lower) {
    auto *ptoi =
        llvm::cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
    auto *target_fn =
        llvm::cast<llvm::Function>(ptoi->getPointerOperand());
    auto *state_ptr = call->getArgOperand(0);

    llvm::IRBuilder<> Builder(call);

    auto *rcx = buildStateLoad(Builder, state_ptr, kRCXOffset, "rcx");
    auto *rdx = buildStateLoad(Builder, state_ptr, kRDXOffset, "rdx");
    auto *r8 = buildStateLoad(Builder, state_ptr, kR8Offset, "r8");
    auto *r9 = buildStateLoad(Builder, state_ptr, kR9Offset, "r9");

    auto *result = Builder.CreateCall(
        native_ft, target_fn, {rcx, rdx, r8, r9},
        target_fn->getName().str() + ".result");

    buildStateStore(Builder, state_ptr, kRAXOffset, result);

    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    call->eraseFromParent();
  }
  return true;
}

}  // namespace

// ===----------------------------------------------------------------------===
// Main pass entry point
// ===----------------------------------------------------------------------===

llvm::PreservedAnalyses LowerRemillIntrinsicsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());
  bool changed = false;

  // Fetch LiftedFunctionAnalysis lazily (only for Call/Jump categories).
  const LiftedFunctionMap *lifted = nullptr;
  if (categories_ & (LowerCategories::Call | LowerCategories::Jump)) {
    auto &MAMProxy =
        AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
    lifted =
        MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());
  }

  // Process in correct order matching pipeline semantics.
  if (categories_ & LowerCategories::Flags)
    changed |= lowerFlagIntrinsics(F, table);
  if (categories_ & LowerCategories::Barriers)
    changed |= removeBarriers(F, table);
  if (categories_ & LowerCategories::Memory)
    changed |= lowerMemoryIntrinsics(F, table);
  if (categories_ & LowerCategories::Atomics)
    changed |= lowerAtomicIntrinsics(F, table);
  if (categories_ & LowerCategories::HyperCalls)
    changed |= lowerHyperCalls(F, table);
  if (categories_ & LowerCategories::ErrorMissing)
    changed |= lowerErrorAndMissing(F, table);
  if (categories_ & LowerCategories::Return)
    changed |= lowerFunctionReturn(F, table);
  if (categories_ & LowerCategories::Call)
    changed |= lowerFunctionCall(F, table, lifted);
  if (categories_ & LowerCategories::Jump)
    changed |= lowerJump(F, table, lifted);
  if (categories_ & LowerCategories::Undefined)
    changed |= lowerUndefinedIntrinsics(F, table);
  if (categories_ & LowerCategories::ResolvedDispatch)
    changed |= lowerResolvedDispatchCalls(F);

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

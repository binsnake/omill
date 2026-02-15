#include "omill/Passes/LowerHyperCalls.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

namespace {

/// Create or get a declaration for an external runtime helper function.
llvm::FunctionCallee getOrDeclareHelper(llvm::Module &M, llvm::StringRef name,
                                         llvm::FunctionType *FT) {
  if (auto *F = M.getFunction(name)) {
    return F;
  }
  return M.getOrInsertFunction(name, FT);
}

// Remill SyncHyperCall IDs for x86-64.
enum SyncHyperCallID : uint32_t {
  kX86CPUID = 258,
  kX86ReadTSC = 259,
  kX86ReadTSCP = 260,
};

// State struct x86-64 GPR offsets (each Reg is 16 bytes with 8-byte padding).
// GPR section starts at offset 2208; named register is at +8 within each Reg.
enum StateGPROffset : uint64_t {
  kRAX = 2216,
  kRBX = 2232,
  kRCX = 2248,
  kRDX = 2264,
};

/// GEP into State at a byte offset and return a pointer typed for `ty`.
llvm::Value *stateFieldPtr(llvm::IRBuilder<> &B, llvm::Value *state,
                            uint64_t byte_offset, llvm::Type *ty) {
  auto *i8_ty = llvm::Type::getInt8Ty(B.getContext());
  auto *gep = B.CreateInBoundsGEP(i8_ty, state, B.getInt64(byte_offset));
  return gep;
}

/// Emit inline CPUID: read EAX/ECX leaf from State, execute cpuid, write
/// EAX/EBX/ECX/EDX results back to State.
void emitCPUID(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  // Read leaf (EAX) and subleaf (ECX) from State.
  auto *eax_ptr = stateFieldPtr(B, state, kRAX, i32_ty);
  auto *ecx_ptr = stateFieldPtr(B, state, kRCX, i32_ty);
  auto *leaf = B.CreateLoad(i32_ty, eax_ptr, "cpuid.leaf");
  auto *subleaf = B.CreateLoad(i32_ty, ecx_ptr, "cpuid.subleaf");

  // Inline asm: cpuid
  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty, i32_ty, i32_ty),
      {i32_ty, i32_ty}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "cpuid",
      "={eax},={ebx},={ecx},={edx},{eax},{ecx},~{dirflag},~{fpsr},~{flags}",
      /*hasSideEffects=*/true);
  auto *result = B.CreateCall(asm_ty, ia, {leaf, subleaf}, "cpuid");

  // Extract and write results.
  auto *out_eax = B.CreateExtractValue(result, 0);
  auto *out_ebx = B.CreateExtractValue(result, 1);
  auto *out_ecx = B.CreateExtractValue(result, 2);
  auto *out_edx = B.CreateExtractValue(result, 3);

  B.CreateStore(out_eax, stateFieldPtr(B, state, kRAX, i32_ty));
  B.CreateStore(out_ebx, stateFieldPtr(B, state, kRBX, i32_ty));
  B.CreateStore(out_ecx, stateFieldPtr(B, state, kRCX, i32_ty));
  B.CreateStore(out_edx, stateFieldPtr(B, state, kRDX, i32_ty));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Emit inline RDTSC: readcyclecounter → split into EDX:EAX in State.
void emitRDTSC(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  // llvm.readcyclecounter() → i64
  auto *rdtsc_fn = llvm::Intrinsic::getOrInsertDeclaration(
      CI->getModule(), llvm::Intrinsic::readcyclecounter);
  auto *tsc = B.CreateCall(rdtsc_fn, {}, "rdtsc");

  // Low 32 → EAX, high 32 → EDX
  auto *lo = B.CreateTrunc(tsc, i32_ty, "rdtsc.lo");
  auto *hi = B.CreateTrunc(B.CreateLShr(tsc, llvm::ConstantInt::get(i64_ty, 32)),
                            i32_ty, "rdtsc.hi");

  B.CreateStore(lo, stateFieldPtr(B, state, kRAX, i32_ty));
  B.CreateStore(hi, stateFieldPtr(B, state, kRDX, i32_ty));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Emit inline RDTSCP: rdtscp asm → write EAX, EDX, ECX to State.
void emitRDTSCP(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty, i32_ty), {}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "rdtscp", "={eax},={edx},={ecx},~{dirflag},~{fpsr},~{flags}",
      /*hasSideEffects=*/true);
  auto *result = B.CreateCall(asm_ty, ia, {}, "rdtscp");

  auto *out_eax = B.CreateExtractValue(result, 0);
  auto *out_edx = B.CreateExtractValue(result, 1);
  auto *out_ecx = B.CreateExtractValue(result, 2);

  B.CreateStore(out_eax, stateFieldPtr(B, state, kRAX, i32_ty));
  B.CreateStore(out_edx, stateFieldPtr(B, state, kRDX, i32_ty));
  B.CreateStore(out_ecx, stateFieldPtr(B, state, kRCX, i32_ty));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Emit a generic fallback stub call for unknown sync hyper calls.
void emitGenericSyncStub(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();

  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);
  llvm::Value *hyper_call_id = CI->getArgOperand(2);

  auto *state_ptr_ty = state->getType();
  auto *i32_ty = llvm::Type::getInt32Ty(CI->getContext());
  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());

  auto *FT = llvm::FunctionType::get(void_ty, {state_ptr_ty, i32_ty}, false);
  auto callee = getOrDeclareHelper(M, "__omill_sync_hyper_call", FT);

  Builder.CreateCall(callee, {state, hyper_call_id});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower __remill_sync_hyper_call(State&, Memory*, SyncHyperCall::Name)
/// Dispatches to typed inline lowering for known IDs, falls back to stub.
void lowerSyncHyperCall(llvm::CallInst *CI) {
  // arg0 = State&, arg1 = Memory*, arg2 = SyncHyperCall::Name (i32)
  auto *id = CI->getArgOperand(2);
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(id);
  if (!ci) {
    emitGenericSyncStub(CI);
    return;
  }

  switch (ci->getZExtValue()) {
    case kX86CPUID:   emitCPUID(CI); break;
    case kX86ReadTSC: emitRDTSC(CI); break;
    case kX86ReadTSCP: emitRDTSCP(CI); break;
    default:          emitGenericSyncStub(CI); break;
  }
}

/// Lower __remill_async_hyper_call(State&, addr_t, Memory*)
/// This handles interrupts, syscalls. Replace with runtime stub.
void lowerAsyncHyperCall(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();

  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *ret_addr = CI->getArgOperand(1);
  llvm::Value *mem = CI->getArgOperand(2);

  auto *state_ptr_ty = state->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(CI->getContext());
  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());

  auto *FT =
      llvm::FunctionType::get(void_ty, {state_ptr_ty, i64_ty}, false);
  auto callee = getOrDeclareHelper(M, "__omill_async_hyper_call", FT);

  Builder.CreateCall(callee, {state, ret_addr});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower I/O port intrinsics to runtime stubs.
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
    // __remill_read_io_port_N(mem, addr) -> value
    // Replace with __omill_read_io_port(addr, bitwidth) -> value
    auto *FT = llvm::FunctionType::get(int_ty, {i64_ty}, false);
    std::string name =
        "__omill_read_io_port_" + std::to_string(bit_width);
    auto callee = getOrDeclareHelper(M, name, FT);

    llvm::Value *addr = CI->getArgOperand(1);
    auto *result = Builder.CreateCall(callee, {addr});
    CI->replaceAllUsesWith(result);
  } else {
    // __remill_write_io_port_N(mem, addr, val) -> Memory*
    auto *void_ty = llvm::Type::getVoidTy(Ctx);
    auto *FT = llvm::FunctionType::get(void_ty, {i64_ty, int_ty}, false);
    std::string name =
        "__omill_write_io_port_" + std::to_string(bit_width);
    auto callee = getOrDeclareHelper(M, name, FT);

    llvm::Value *addr = CI->getArgOperand(1);
    llvm::Value *val = CI->getArgOperand(2);
    Builder.CreateCall(callee, {addr, val});

    CI->replaceAllUsesWith(CI->getArgOperand(0));
  }

  CI->eraseFromParent();
}

/// Lower FPU intrinsics to C runtime calls.
void lowerFPUOp(llvm::CallInst *CI, IntrinsicKind kind) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

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

/// Lower x86-specific segment/control/debug register setters to stubs.
void lowerX86Specific(llvm::CallInst *CI, IntrinsicKind kind) {
  llvm::IRBuilder<> Builder(CI);

  // These all take Memory* and return Memory*.
  // Just pass through the Memory* for now — segment/control register
  // modifications are handled by the runtime.
  CI->replaceAllUsesWith(CI->getArgOperand(0));
  CI->eraseFromParent();
}

}  // namespace

llvm::PreservedAnalyses LowerHyperCallsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 16> pending;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      auto kind = table.classifyCall(CI);
      auto cat = IntrinsicTable::categoryOf(kind);
      if (cat == IntrinsicCategory::kHyperCall ||
          cat == IntrinsicCategory::kIOPort ||
          cat == IntrinsicCategory::kFPU ||
          cat == IntrinsicCategory::kX86Specific) {
        pending.push_back({CI, kind});
      }
    }
  }

  if (pending.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto &[CI, kind] : pending) {
    auto cat = IntrinsicTable::categoryOf(kind);
    switch (cat) {
      case IntrinsicCategory::kHyperCall:
        if (kind == IntrinsicKind::kSyncHyperCall) {
          lowerSyncHyperCall(CI);
        } else {
          lowerAsyncHyperCall(CI);
        }
        break;
      case IntrinsicCategory::kIOPort:
        lowerIOPort(CI, kind);
        break;
      case IntrinsicCategory::kFPU:
        lowerFPUOp(CI, kind);
        break;
      case IntrinsicCategory::kX86Specific:
        lowerX86Specific(CI, kind);
        break;
      default:
        break;
    }
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

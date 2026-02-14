#include "omill/Passes/LowerHyperCalls.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
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

/// Lower __remill_sync_hyper_call(State&, Memory*, SyncHyperCall::Name)
/// This dispatches to different handlers based on the hyper call name.
/// For now, we replace with calls to external runtime stubs.
void lowerSyncHyperCall(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();

  // arg0 = State&, arg1 = Memory*, arg2 = SyncHyperCall::Name (i32)
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);
  llvm::Value *hyper_call_id = CI->getArgOperand(2);

  // Create a generic external call: __omill_sync_hyper_call(State*, i32)
  // The runtime can implement this to handle CPUID, RDTSC, etc.
  auto *state_ptr_ty = state->getType();
  auto *i32_ty = llvm::Type::getInt32Ty(CI->getContext());
  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());

  auto *FT = llvm::FunctionType::get(void_ty, {state_ptr_ty, i32_ty}, false);
  auto callee = getOrDeclareHelper(M, "__omill_sync_hyper_call", FT);

  Builder.CreateCall(callee, {state, hyper_call_id});

  // Replace Memory* return with input Memory*
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
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

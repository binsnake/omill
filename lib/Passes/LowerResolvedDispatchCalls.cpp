#include "omill/Passes/LowerResolvedDispatchCalls.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>

namespace omill {

namespace {

// x86-64 State struct offsets (Win64 ABI parameter registers).
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

}  // namespace

llvm::PreservedAnalyses LowerResolvedDispatchCallsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.arg_size() == 0)
    return llvm::PreservedAnalyses::all();

  // Collect lowerable dispatch calls (avoid iterator invalidation).
  llvm::SmallVector<llvm::CallInst *, 4> to_lower;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->getName() != "__omill_dispatch_call")
        continue;
      if (call->arg_size() < 3)
        continue;

      // Check if target_pc (arg1) is ptrtoint(@dllimport_func).
      auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
      if (!ptoi)
        continue;
      auto *target_fn = llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
      if (!target_fn)
        continue;
      if (target_fn->getDLLStorageClass() != llvm::GlobalValue::DLLImportStorageClass)
        continue;

      to_lower.push_back(call);
    }
  }

  if (to_lower.empty())
    return llvm::PreservedAnalyses::all();

  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Native call type: i64 (i64, i64, i64, i64)
  auto *native_ft = llvm::FunctionType::get(
      i64_ty, {i64_ty, i64_ty, i64_ty, i64_ty}, false);

  for (auto *call : to_lower) {
    auto *ptoi = llvm::cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
    auto *target_fn = llvm::cast<llvm::Function>(ptoi->getPointerOperand());
    auto *state_ptr = call->getArgOperand(0);

    llvm::IRBuilder<> Builder(call);

    // Load Win64 parameter registers from State.
    auto *rcx = buildStateLoad(Builder, state_ptr, kRCXOffset, "rcx");
    auto *rdx = buildStateLoad(Builder, state_ptr, kRDXOffset, "rdx");
    auto *r8 = buildStateLoad(Builder, state_ptr, kR8Offset, "r8");
    auto *r9 = buildStateLoad(Builder, state_ptr, kR9Offset, "r9");

    // Call the import with native Win64 signature.
    auto *result = Builder.CreateCall(native_ft, target_fn, {rcx, rdx, r8, r9},
                                      target_fn->getName().str() + ".result");

    // Store result to State+RAX.
    buildStateStore(Builder, state_ptr, kRAXOffset, result);

    // Replace uses of the dispatch_call (Memory* token) with poison.
    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    call->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

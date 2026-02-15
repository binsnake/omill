#include "omill/Passes/LowerFunctionCall.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::PreservedAnalyses LowerFunctionCallPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *lifted = MAMProxy.getCachedResult<LiftedFunctionAnalysis>(M);

  llvm::SmallVector<llvm::CallInst *, 8> call_intrinsics;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      if (table.classifyCall(CI) == IntrinsicKind::kFunctionCall) {
        call_intrinsics.push_back(CI);
      }
    }
  }

  if (call_intrinsics.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  // Declare a dispatcher for indirect calls
  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();

  auto *lifted_fn_ty =
      llvm::FunctionType::get(mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);

  for (auto *CI : call_intrinsics) {
    llvm::IRBuilder<> Builder(CI);

    // __remill_function_call(State&, addr_t target_pc, Memory*)
    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::Value *result = nullptr;

    // Case 1: constant target PC — emit direct call
    if (auto *const_pc = llvm::dyn_cast<llvm::ConstantInt>(target_pc)) {
      uint64_t pc_val = const_pc->getZExtValue();
      llvm::Function *target_fn =
          lifted ? lifted->lookup(pc_val) : nullptr;
      if (target_fn) {
        result = Builder.CreateCall(target_fn, {state, target_pc, mem});
      }
    }

    // Case 2: dynamic target or target not found — emit dispatcher call
    if (!result) {
      auto dispatcher = M.getOrInsertFunction(
          "__omill_dispatch_call", lifted_fn_ty);
      result = Builder.CreateCall(dispatcher, {state, target_pc, mem});
    }

    CI->replaceAllUsesWith(result);
    CI->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill

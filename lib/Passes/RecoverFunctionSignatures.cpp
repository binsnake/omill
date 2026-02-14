#include "omill/Passes/RecoverFunctionSignatures.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

/// Build a native function type from recovered ABI info.
llvm::FunctionType *buildNativeType(const FunctionABI &abi,
                                     llvm::LLVMContext &Ctx) {
  llvm::Type *ret_ty;
  if (abi.ret.has_value()) {
    // Return i64 for GPR returns (RAX).
    ret_ty = llvm::Type::getInt64Ty(Ctx);
  } else {
    ret_ty = llvm::Type::getVoidTy(Ctx);
  }

  llvm::SmallVector<llvm::Type *, 6> param_types;
  for (unsigned i = 0; i < abi.numParams(); ++i) {
    // All GPR params are i64.
    param_types.push_back(llvm::Type::getInt64Ty(Ctx));
  }

  return llvm::FunctionType::get(ret_ty, param_types, false);
}

/// Build a GEP to a State field at a given byte offset using i8 arithmetic.
llvm::Value *buildStateGEP(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                            unsigned offset) {
  auto *gep = Builder.CreateConstGEP1_64(Builder.getInt8Ty(), state_ptr, offset);
  return gep;
}

/// Create a native wrapper function that:
/// 1. Allocates a local State struct
/// 2. Stores parameters into the appropriate State fields
/// 3. Calls the original lifted function
/// 4. Loads the return value from the appropriate State field
llvm::Function *createNativeWrapper(llvm::Function *lifted_fn,
                                     const FunctionABI &abi,
                                     const StateFieldMap &field_map) {
  auto &M = *lifted_fn->getParent();
  auto &Ctx = M.getContext();

  auto *native_ty = buildNativeType(abi, Ctx);

  // Name: lifted function name + "_native"
  std::string native_name = lifted_fn->getName().str() + "_native";
  auto *native_fn = llvm::Function::Create(
      native_ty, llvm::Function::ExternalLinkage, native_name, M);
  native_fn->addFnAttr(llvm::Attribute::MustProgress);
  native_fn->addFnAttr(llvm::Attribute::NoUnwind);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_fn);
  llvm::IRBuilder<> Builder(entry);

  // Find the State struct type.
  llvm::StructType *state_ty = nullptr;
  for (auto *ST : M.getIdentifiedStructTypes()) {
    if (ST->getName() == "struct.State") {
      state_ty = ST;
      break;
    }
  }

  // If we can't find the State type, create a raw byte allocation.
  llvm::Value *state_alloca;
  if (state_ty) {
    state_alloca = Builder.CreateAlloca(state_ty, nullptr, "state");
    // Zero-init the state
    auto state_size = M.getDataLayout().getTypeAllocSize(state_ty);
    Builder.CreateMemSet(state_alloca, Builder.getInt8(0), state_size,
                          llvm::MaybeAlign(16));
  } else {
    // Fallback: allocate raw bytes (4096 is generous for x86_64 State).
    auto *raw_ty = llvm::ArrayType::get(Builder.getInt8Ty(), 4096);
    state_alloca = Builder.CreateAlloca(raw_ty, nullptr, "state_raw");
    Builder.CreateMemSet(state_alloca, Builder.getInt8(0), 4096,
                          llvm::MaybeAlign(16));
  }

  // Store parameters into State fields.
  for (unsigned i = 0; i < abi.numParams(); ++i) {
    auto *param = native_fn->getArg(i);
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     abi.params[i].state_offset);
    Builder.CreateStore(param, field_ptr);
  }

  // Build arguments for the lifted function call.
  // Lifted functions have signature: (State*, i64, Memory*) -> Memory*
  auto *lifted_ty = lifted_fn->getFunctionType();
  llvm::SmallVector<llvm::Value *, 3> call_args;

  // Arg 0: State pointer
  call_args.push_back(state_alloca);

  // Arg 1: PC (pass 0 — not meaningful in the wrapper)
  if (lifted_ty->getNumParams() > 1) {
    call_args.push_back(Builder.getInt64(0));
  }

  // Arg 2: Memory pointer (pass null/poison — already lowered)
  if (lifted_ty->getNumParams() > 2) {
    call_args.push_back(
        llvm::PoisonValue::get(lifted_ty->getParamType(2)));
  }

  Builder.CreateCall(lifted_fn, call_args);

  // Load return value from State.
  if (abi.ret.has_value()) {
    auto *ret_ptr = buildStateGEP(Builder, state_alloca,
                                   abi.ret->state_offset);
    auto *ret_val = Builder.CreateLoad(Builder.getInt64Ty(), ret_ptr, "retval");
    Builder.CreateRet(ret_val);
  } else {
    Builder.CreateRetVoid();
  }

  return native_fn;
}

}  // namespace

llvm::PreservedAnalyses RecoverFunctionSignaturesPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &cc_info = MAM.getResult<CallingConventionAnalysis>(M);
  StateFieldMap field_map(M);

  bool changed = false;

  // Collect lifted functions to process (avoid iterator invalidation).
  // Lifted functions have the remill signature: (ptr, i64, ptr) -> ptr
  llvm::SmallVector<llvm::Function *, 16> functions;
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    if (F.getName().starts_with("__remill_")) continue;
    if (F.getName().starts_with("__omill_")) continue;
    if (F.getName().ends_with("_native")) continue;
    if (F.arg_size() != 3) continue;
    auto *FTy = F.getFunctionType();
    if (!FTy->getReturnType()->isPointerTy()) continue;
    if (!FTy->getParamType(0)->isPointerTy()) continue;
    if (!FTy->getParamType(1)->isIntegerTy(64)) continue;
    if (!FTy->getParamType(2)->isPointerTy()) continue;
    functions.push_back(&F);
  }

  for (auto *F : functions) {
    auto *abi = cc_info.getABI(F);
    if (!abi) continue;
    if (abi->cc == DetectedCC::kUnknown) continue;

    createNativeWrapper(F, *abi, field_map);
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

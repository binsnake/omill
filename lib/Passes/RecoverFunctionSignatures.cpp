#include "omill/Passes/RecoverFunctionSignatures.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

static constexpr unsigned kWin64PublicRootParamCount = 2;

bool isPublicOutputRoot(const llvm::Function *F) {
  return F && F->hasFnAttribute("omill.output_root") &&
         !F->hasFnAttribute("omill.vm_wrapper");
}

unsigned exportedRootGPRParamCount(const FunctionABI &abi,
                                   bool is_public_output_root) {
  if (!is_public_output_root)
    return abi.numParams();
  if (abi.cc == DetectedCC::kWin64)
    return std::min(kWin64PublicRootParamCount, abi.numParams());
  return abi.numParams();
}

/// Build a native function type from recovered ABI info.
llvm::FunctionType *buildNativeType(const FunctionABI &abi,
                                     llvm::LLVMContext &Ctx,
                                     bool suppress_extra_gpr_returns = false,
                                     unsigned gpr_param_count = 0,
                                     bool suppress_non_standard_params = false,
                                     bool expose_public_root_ptr_params = false) {
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *xmm_ty = llvm::FixedVectorType::get(i64_ty, 2);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // --- Return type ---
  // If the function clobbers callee-saved GPRs, we pack the primary return
  // value (RAX/XMM0/void) together with the clobbered register values into a
  // struct return.  At call sites the caller extracts and stores each field
  // back into its own State so that interprocedural register flow is kept.
  llvm::Type *primary_ret_ty;
  if (abi.ret.has_value()) {
    primary_ret_ty =
        abi.ret->is_vector ? static_cast<llvm::Type *>(xmm_ty) : i64_ty;
  } else {
    primary_ret_ty = nullptr;  // void
  }

  llvm::Type *ret_ty;
  bool use_struct_return =
      abi.hasStructReturn() && !suppress_extra_gpr_returns;
  if (use_struct_return) {
    llvm::SmallVector<llvm::Type *, 10> fields;
    if (primary_ret_ty)
      fields.push_back(primary_ret_ty);
    for (unsigned i = 0; i < abi.numExtraGPRReturns(); ++i)
      fields.push_back(i64_ty);
    ret_ty = llvm::StructType::get(Ctx, fields);
  } else if (primary_ret_ty) {
    ret_ty = primary_ret_ty;
  } else {
    ret_ty = llvm::Type::getVoidTy(Ctx);
  }

  // --- Parameters ---
  llvm::SmallVector<llvm::Type *, 10> param_types;

  // GPR params (i64).
  if (gpr_param_count == 0)
    gpr_param_count = abi.numParams();
  for (unsigned i = 0; i < gpr_param_count; ++i)
    param_types.push_back(
        expose_public_root_ptr_params
            ? static_cast<llvm::Type *>(ptr_ty)
            : static_cast<llvm::Type *>(i64_ty));

  if (suppress_non_standard_params)
    return llvm::FunctionType::get(ret_ty, param_types, false);

  // Stack-passed params (i64 each).
  for (unsigned i = 0; i < abi.numStackParams(); ++i)
    param_types.push_back(i64_ty);

  // XMM live-ins (<2 x i64>).
  for (unsigned i = 0; i < abi.numXMMParams(); ++i)
    param_types.push_back(xmm_ty);

  // Extra GPR live-ins (i64).
  for (unsigned i = 0; i < abi.numExtraGPRParams(); ++i)
    param_types.push_back(i64_ty);

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
                                     const StateFieldMap &field_map,
                                     llvm::StructType *state_ty) {
  auto &M = *lifted_fn->getParent();
  auto &Ctx = M.getContext();

  bool is_public_output_root = isPublicOutputRoot(lifted_fn);
  FunctionABI wrapper_abi = abi;
  if (is_public_output_root && !wrapper_abi.ret.has_value()) {
    if (auto rax = field_map.fieldByName("RAX"); rax.has_value()) {
      wrapper_abi.ret = RecoveredReturn{
          "RAX",
          rax->offset,
          8,
          false,
      };
    } else if (auto x0 = field_map.fieldByName("X0"); x0.has_value()) {
      wrapper_abi.ret = RecoveredReturn{
          "X0",
          x0->offset,
          8,
          false,
      };
    }
  }
  unsigned gpr_param_count =
      exportedRootGPRParamCount(wrapper_abi, is_public_output_root);
  auto *native_ty = buildNativeType(wrapper_abi, Ctx, is_public_output_root,
                                    gpr_param_count, is_public_output_root,
                                    is_public_output_root);

  // Name: lifted function name + "_native"
  std::string native_name = lifted_fn->getName().str() + "_native";
  auto *native_fn = llvm::Function::Create(
      native_ty, llvm::Function::ExternalLinkage, native_name, M);
  native_fn->addFnAttr(llvm::Attribute::MustProgress);
  native_fn->addFnAttr(llvm::Attribute::NoUnwind);
  // Propagate VM handler metadata so downstream passes preserve exact richardvm
  // identity across ABI wrapper generation.
  if (lifted_fn->hasFnAttribute("omill.vm_handler"))
    native_fn->addFnAttr("omill.vm_handler");
  if (lifted_fn->hasFnAttribute("omill.vm_wrapper"))
    native_fn->addFnAttr("omill.vm_wrapper");
  auto propagateStringAttr = [&](llvm::StringRef name) {
    auto attr = lifted_fn->getFnAttribute(name);
    if (attr.isValid() && attr.isStringAttribute())
      native_fn->addFnAttr(name, attr.getValueAsString());
  };
  propagateStringAttr("omill.vm_trace_in_hash");
  propagateStringAttr("omill.vm_demerged_clone");
  propagateStringAttr("omill.vm_outlined_virtual_call");
  propagateStringAttr("omill.vm_helper_hash");
  propagateStringAttr("omill.vm_helper_caller");
  propagateStringAttr("omill.vm_virtual_callee_kind");
  propagateStringAttr("omill.vm_virtual_callee_base");
  propagateStringAttr("omill.vm_virtual_callee_round");
  propagateStringAttr("omill.vm_handler_va");
  propagateStringAttr("omill.vm_trace_hash");
  propagateStringAttr("omill.trace_native_target");
  if (native_fn->getFnAttribute("omill.vm_demerged_clone").isValid() ||
      native_fn->getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
      native_fn->getFnAttribute("omill.trace_native_target").isValid()) {
    native_fn->addFnAttr(llvm::Attribute::NoInline);
  }
  if (lifted_fn->hasFnAttribute("omill.vm_entry_seed"))
    native_fn->addFnAttr("omill.vm_entry_seed");
  if (lifted_fn->hasFnAttribute("omill.output_root"))
    native_fn->addFnAttr("omill.output_root");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_fn);
  llvm::IRBuilder<> Builder(entry);

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

  // Seed a synthetic native stack so lifted prologues don't run with SP=0.
  // Keeping SP as a dynamic pointer avoids constant-folding stack math into
  // degenerate infinite loops in flattened dispatchers.
  constexpr uint64_t kSyntheticStackSize = 1ull << 16;  // 64 KiB
  // Extra room above SP for caller-frame reads (e.g. RSP+456 in
  // sub_1402d4b7e).  Without this, positive SP-relative loads fall
  // outside the alloca → OOB UB → optimizer folds body to unreachable.
  constexpr uint64_t kCallerFrameRoom = 0x1000;  // 4 KiB
  constexpr uint64_t kTotalStackSize = kSyntheticStackSize + kCallerFrameRoom;
  auto *stack_ty =
      llvm::ArrayType::get(Builder.getInt8Ty(), kTotalStackSize);
  auto *stack_alloca = Builder.CreateAlloca(stack_ty, nullptr, "native_stack");
  // Fill with 0xCC so reads from caller-frame offsets yield a definite
  // non-null/non-zero value instead of undef.  inttoptr(0xCC..CC) is not
  // UB, so the optimizer won't collapse the function body to unreachable.
  Builder.CreateMemSet(stack_alloca, Builder.getInt8(0xCC),
                        kTotalStackSize, llvm::MaybeAlign(16));
  auto *stack_top = Builder.CreateConstGEP1_64(
      Builder.getInt8Ty(), stack_alloca, kSyntheticStackSize - 0x20);
  auto *stack_top_i64 = Builder.CreatePtrToInt(stack_top, Builder.getInt64Ty());
  // Seed the stack pointer register (RSP for x86-64, sp for AArch64).
  for (const char *sp_name : {"RSP", "SP", "sp"}) {
    if (auto sp = field_map.fieldByName(sp_name); sp.has_value()) {
      auto *sp_ptr = buildStateGEP(Builder, state_alloca, sp->offset);
      Builder.CreateStore(stack_top_i64, sp_ptr);
      break;
    }
  }
  // Seed the frame pointer register (RBP for x86-64, x29 for AArch64).
  for (const char *fp_name : {"RBP", "FP", "x29", "X29"}) {
    if (auto fp = field_map.fieldByName(fp_name); fp.has_value()) {
      auto *fp_ptr = buildStateGEP(Builder, state_alloca, fp->offset);
      Builder.CreateStore(stack_top_i64, fp_ptr);
      break;
    }
  }

  if (is_public_output_root) {
    // Hidden VM-only GPR live-ins on exported roots are internal scaffolding,
    // not part of the public ABI. Seed them from the synthetic stack so
    // inlined VM bookkeeping does not collapse into inttoptr(low-constant)
    // artifacts like inttoptr(400).
    for (unsigned off : abi.extra_gpr_live_ins) {
      auto *field_ptr = buildStateGEP(Builder, state_alloca, off);
      Builder.CreateStore(stack_top_i64, field_ptr);
    }
  }

  // Store GPR parameters into State fields.
  for (unsigned i = 0; i < gpr_param_count; ++i) {
    auto *param = native_fn->getArg(i);
    llvm::Value *param_i64 = param;
    if (param->getType()->isPointerTy()) {
      param_i64 = Builder.CreatePtrToInt(param, Builder.getInt64Ty(),
                                         param->getName() + ".i64");
    }
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.params[i].state_offset);
    Builder.CreateStore(param_i64, field_ptr);
  }

  // Store stack-passed parameters to the caller's stack area.
  // In the native wrapper, we need to store them at the appropriate
  // SP-relative offsets so the lifted function can read them.
  auto sp_field = field_map.fieldByName("RSP");
  if (!sp_field) sp_field = field_map.fieldByName("SP");
  if (!sp_field) sp_field = field_map.fieldByName("sp");
  if (!is_public_output_root && sp_field.has_value()) {
    auto rsp = sp_field;
    for (unsigned i = 0; i < wrapper_abi.numStackParams(); ++i) {
      unsigned arg_idx = gpr_param_count + i;
      auto *param = native_fn->getArg(arg_idx);
      // Store at RSP + stack_offset (the callee will load from there).
      auto *rsp_ptr = buildStateGEP(Builder, state_alloca, rsp->offset);
      auto *rsp_val = Builder.CreateLoad(Builder.getInt64Ty(), rsp_ptr, "rsp");
      auto *addr = Builder.CreateAdd(
          rsp_val, Builder.getInt64(wrapper_abi.stack_params[i].stack_offset));
      auto *ptr = Builder.CreateIntToPtr(addr,
          llvm::PointerType::get(Builder.getContext(), 0));
      Builder.CreateStore(param, ptr);
    }
  }

  // Store XMM parameters into State vector register slots.
  for (unsigned i = 0; !is_public_output_root && i < wrapper_abi.numXMMParams();
       ++i) {
    unsigned arg_idx = gpr_param_count + wrapper_abi.numStackParams() + i;
    auto *param = native_fn->getArg(arg_idx);
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.xmm_live_ins[i]);
    Builder.CreateStore(param, field_ptr);
  }

  // Store extra GPR parameters into State fields.
  for (unsigned i = 0;
       !is_public_output_root && i < wrapper_abi.numExtraGPRParams(); ++i) {
    unsigned arg_idx = gpr_param_count + wrapper_abi.numStackParams() +
                       wrapper_abi.numXMMParams() + i;
    auto *param = native_fn->getArg(arg_idx);
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.extra_gpr_live_ins[i]);
    Builder.CreateStore(param, field_ptr);
  }

  // Store param-to-State-offset metadata so per-callsite clone logic
  // can map native function params back to emulator GPR indices.
  {
    std::string offsets_str;
    for (unsigned i = 0; i < gpr_param_count; ++i)
      offsets_str += std::to_string(wrapper_abi.params[i].state_offset) + ",";
    for (unsigned i = 0; !is_public_output_root &&
                         i < wrapper_abi.numStackParams(); ++i)
      offsets_str += "stack,";  // Stack params don't map to GPRs.
    for (unsigned i = 0; !is_public_output_root &&
                         i < wrapper_abi.numXMMParams(); ++i)
      offsets_str += "xmm,";   // XMM params don't map to GPRs.
    for (unsigned i = 0; !is_public_output_root &&
                         i < wrapper_abi.numExtraGPRParams(); ++i)
      offsets_str += std::to_string(wrapper_abi.extra_gpr_live_ins[i]) + ",";
    if (!offsets_str.empty())
      offsets_str.pop_back();
    native_fn->addFnAttr("omill.param_state_offsets", offsets_str);
  }

  // Build arguments for the lifted function call.
  // Lifted functions have signature: (State*, i64, Memory*) -> Memory*
  auto *lifted_ty = lifted_fn->getFunctionType();
  llvm::SmallVector<llvm::Value *, 3> call_args;
  // Arg 0: State pointer.
  call_args.push_back(state_alloca);

  // Arg 1: Entry PC from the lifted symbol name (e.g. sub_401000).
  // Passing 0 here can trap unresolved dispatchers in synthetic loops.
  if (lifted_ty->getNumParams() > 1) {
    uint64_t entry_va = extractEntryVA(lifted_fn->getName());
    call_args.push_back(Builder.getInt64(entry_va));
  }

  // Arg 2: Memory pointer. Use null (not poison) to avoid injecting UB.
  if (lifted_ty->getNumParams() > 2) {
    call_args.push_back(
        llvm::Constant::getNullValue(lifted_ty->getParamType(2)));
  }

  Builder.CreateCall(lifted_fn, call_args);

  // Load return value(s) from State.
  if (wrapper_abi.hasStructReturn() && !is_public_output_root) {
    // Build a struct containing the primary return + clobbered callee-saved.
    auto *struct_ty = llvm::cast<llvm::StructType>(native_fn->getReturnType());
    llvm::Value *agg = llvm::PoisonValue::get(struct_ty);
    unsigned idx = 0;

    // Primary return value (RAX or XMM0), if present.
    if (wrapper_abi.ret.has_value()) {
      llvm::Type *load_ty = wrapper_abi.ret->is_vector
          ? static_cast<llvm::Type *>(
                llvm::FixedVectorType::get(Builder.getInt64Ty(), 2))
          : static_cast<llvm::Type *>(Builder.getInt64Ty());
      auto *ret_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.ret->state_offset);
      auto *primary = Builder.CreateLoad(load_ty, ret_ptr, "retval");
      agg = Builder.CreateInsertValue(agg, primary, idx++);
    }

    // Extra clobbered callee-saved values (i64 each).
    for (unsigned off : wrapper_abi.extra_gpr_live_outs) {
      auto *ptr = buildStateGEP(Builder, state_alloca, off);
      auto *val = Builder.CreateLoad(Builder.getInt64Ty(), ptr,
                                     "clobbered." + llvm::Twine(off));
      agg = Builder.CreateInsertValue(agg, val, idx++);
    }

    Builder.CreateRet(agg);
  } else if (wrapper_abi.ret.has_value()) {
    auto *ret_ptr = buildStateGEP(Builder, state_alloca,
                                   wrapper_abi.ret->state_offset);
    llvm::Type *load_ty;
    if (wrapper_abi.ret->is_vector) {
      load_ty = llvm::FixedVectorType::get(Builder.getInt64Ty(), 2);
    } else {
      load_ty = Builder.getInt64Ty();
    }
    auto *ret_val = Builder.CreateLoad(load_ty, ret_ptr, "retval");
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
    if (!isLiftedFunction(F)) continue;
    functions.push_back(&F);
  }

  // Look up the State struct type once (getIdentifiedStructTypes is expensive).
  llvm::StructType *state_ty = llvm::StructType::getTypeByName(
      M.getContext(), "struct.State");

  for (auto *F : functions) {
    auto *abi = cc_info.getABI(F);
    if (!abi) {
      if (getenv("OMILL_DEBUG_REWRITE"))
        llvm::errs() << "[Sigs] No ABI for " << F->getName() << "\n";
      continue;
    }
    if (getenv("OMILL_DEBUG_REWRITE"))
      llvm::errs() << "[Sigs] Creating wrapper for " << F->getName()
                    << " params=" << abi->numParams()
                    << " ret=" << abi->ret.has_value() << "\n";
    createNativeWrapper(F, *abi, field_map, state_ty);
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

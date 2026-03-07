#include "omill/Passes/RewriteLiftedCallsToNative.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>
#include <memory>
#include <optional>

namespace {

class RewriteLiftedCallsToNativeTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::FunctionType *liftedFnTy() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  std::unique_ptr<llvm::Module> createBaseModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // State type
    auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
    auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
    state_ty->setBody({arr_ty});

    // __remill_basic_block with register GEPs (using real offsets).
    auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);
    auto *bb_state = bb_fn->getArg(0);

    struct RegDef { const char *name; unsigned offset; };
    RegDef regs[] = {
        {"RAX", 2216}, {"RBX", 2232}, {"RCX", 2248}, {"RDX", 2264},
        {"RSI", 2280}, {"RDI", 2296}, {"RSP", 2312}, {"RBP", 2328},
        {"R8", 2344}, {"R9", 2360}, {"RIP", 2368},
    };
    for (auto &reg : regs) {
      // Use i64 element type so StateFieldMap sees size=8 for GPR fields.
      auto *gep = BBB.CreateGEP(BBB.getInt64Ty(), bb_state,
                                BBB.getInt64(reg.offset / 8));
      gep->setName(reg.name);
    }
    BBB.CreateRet(bb_fn->getArg(2));

    return M;
  }

  llvm::PreservedAnalyses runPass(
      llvm::Module &M,
      std::optional<omill::BinaryMemoryMap> memory_map = std::nullopt) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
    MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });
    std::shared_ptr<omill::BinaryMemoryMap> memory_map_holder =
        std::make_shared<omill::BinaryMemoryMap>(
            memory_map.has_value() ? std::move(*memory_map)
                                   : omill::BinaryMemoryMap());
    MAM.registerPass([memory_map_holder] {
      return omill::BinaryMemoryAnalysis(*memory_map_holder);
    });

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::RewriteLiftedCallsToNativePass());
    return MPM.run(M, MAM);
  }
};

TEST_F(RewriteLiftedCallsToNativeTest, StaticCallRewritten) {
  auto M = createBaseModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Create callee: sub_402000 (non-leaf — it contains a dispatch call).
  auto *callee = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", callee);
    llvm::IRBuilder<> B(entry);
    auto *state = callee->getArg(0);
    // Read RCX to make it non-trivial.
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2248);
    auto *val = B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216);
    B.CreateStore(val, rax_gep);
    // Make it non-leaf by calling dispatch.
    auto *dispatch = M->getOrInsertFunction(
        "__omill_dispatch_call", liftedFnTy()).getCallee();
    auto *result = B.CreateCall(liftedFnTy(),
        dispatch, {state, B.getInt64(0x999000), callee->getArg(2)});
    B.CreateRet(result);
  }

  // Create sub_402000_native wrapper: i64(i64)
  auto *native_fn_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *native_fn = llvm::Function::Create(
      native_fn_ty, llvm::Function::ExternalLinkage, "sub_402000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(native_fn->getArg(0));
  }

  // Create caller: sub_401000 that calls sub_402000 directly.
  auto *caller = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *result = B.CreateCall(callee,
        {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(result);
  }

  runPass(*M);

  // After: caller should call sub_402000_native instead of sub_402000.
  bool calls_native = false;
  std::string call_targets;
  for (auto &BB : *caller)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() == native_fn)
          calls_native = true;
        if (CI->getCalledFunction())
          call_targets += CI->getCalledFunction()->getName().str() + " ";
        else
          call_targets += "<indirect> ";
      }

  EXPECT_TRUE(calls_native) << "Call targets in caller: " << call_targets;
}

TEST_F(RewriteLiftedCallsToNativeTest, DynamicDispatchEmitsIndirectCall) {
  auto M = createBaseModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Create callee sub_402000 with a body + native wrapper.
  auto *callee = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", callee);
    llvm::IRBuilder<> B(entry);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), callee->getArg(0), 2248);
    auto *val = B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), callee->getArg(0), 2216);
    B.CreateStore(val, rax_gep);
    B.CreateRet(callee->getArg(2));
  }
  auto *native_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *native_fn = llvm::Function::Create(
      native_ty, llvm::Function::ExternalLinkage, "sub_402000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(native_fn->getArg(0));
  }

  // Create caller with __omill_dispatch_call using a dynamic target.
  auto *dispatch = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);
  auto *caller = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    // Dynamic target — load from State.
    auto *dynamic_pc = B.CreateLoad(i64_ty, caller->getArg(0), "dyn_pc");
    auto *result = B.CreateCall(dispatch,
        {caller->getArg(0), dynamic_pc, caller->getArg(2)});
    B.CreateRet(result);
  }

  runPass(*M);

  // After: should NOT have __omill_native_dispatch; instead the caller
  // should contain an indirect call (CallInst with null getCalledFunction()).
  auto *native_dispatch = M->getFunction("__omill_native_dispatch");
  EXPECT_EQ(native_dispatch, nullptr);

  bool has_indirect_call = false;
  for (auto &BB : *caller)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (!CI->getCalledFunction())
          has_indirect_call = true;

  EXPECT_TRUE(has_indirect_call);
}

TEST_F(RewriteLiftedCallsToNativeTest, LeafWithNativeRewrittenToNative) {
  auto M = createBaseModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Create a leaf function (no calls to other lifted functions or dispatch).
  auto *leaf = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), leaf->getArg(0), 2248);
    auto *val = B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), leaf->getArg(0), 2216);
    B.CreateStore(val, rax_gep);
    B.CreateRet(leaf->getArg(2));
  }

  // Create native wrapper — WILL be used since leaf+native → rewrite to native.
  auto *native_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *native_fn = llvm::Function::Create(
      native_ty, llvm::Function::ExternalLinkage, "sub_402000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(native_fn->getArg(0));
  }

  // Caller calls the leaf directly.
  auto *caller = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *result = B.CreateCall(leaf,
        {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(result);
  }

  runPass(*M);

  // After: caller should call sub_402000_native (preserving call boundary),
  // not the original leaf (which would be inlined by AlwaysInlinerPass).
  bool calls_leaf = false;
  bool calls_native = false;
  for (auto &BB : *caller)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() == leaf)
          calls_leaf = true;
        if (CI->getCalledFunction() == native_fn)
          calls_native = true;
      }

  EXPECT_FALSE(calls_leaf);
  EXPECT_TRUE(calls_native);
}

TEST_F(RewriteLiftedCallsToNativeTest, LeafWithoutNativeNotRewritten) {
  auto M = createBaseModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Create a leaf function WITHOUT a _native wrapper.
  auto *leaf = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), leaf->getArg(0), 2248);
    auto *val = B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), leaf->getArg(0), 2216);
    B.CreateStore(val, rax_gep);
    B.CreateRet(leaf->getArg(2));
  }

  // No sub_402000_native — leaf stays as leaf.

  // Caller calls the leaf directly.
  auto *caller = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *result = B.CreateCall(leaf,
        {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(result);
  }

  runPass(*M);

  // After: caller should still call sub_402000 (no native wrapper, keep leaf).
  bool calls_leaf = false;
  for (auto &BB : *caller)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (CI->getCalledFunction() == leaf)
          calls_leaf = true;

  EXPECT_TRUE(calls_leaf);
}

TEST_F(RewriteLiftedCallsToNativeTest, NativeDispatchJumpMaterializesRAX) {
  auto M = createBaseModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *dispatch_jump = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "__omill_dispatch_jump",
      *M);

  // Native wrapper-shaped function with a dynamic dispatch_jump.
  auto *native_wrapper = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_wrapper);
    llvm::IRBuilder<> B(entry);
    auto *state = native_wrapper->getArg(0);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 2216);
    auto *dyn_pc = B.CreateLoad(i64_ty, rax_gep, "dyn_pc");
    B.CreateCall(dispatch_jump, {state, dyn_pc, native_wrapper->getArg(2)});
    B.CreateRet(native_wrapper->getArg(2));
  }

  runPass(*M);

  bool has_dispatch_jump_call = false;
  bool has_rax_store = false;
  for (auto &BB : *native_wrapper) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() == dispatch_jump) {
          has_dispatch_jump_call = true;
        }
      }
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI) {
        continue;
      }
      auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(SI->getPointerOperand());
      if (!GEP || GEP->getNumOperands() < 2) {
        continue;
      }
      if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1))) {
        if (C->getZExtValue() == 2216) {
          has_rax_store = true;
        }
      }
    }
  }

  EXPECT_FALSE(has_dispatch_jump_call);
  EXPECT_TRUE(has_rax_store);
}

TEST_F(RewriteLiftedCallsToNativeTest,
       NativeDispatchJumpCanonicalizesSkewedImageTarget) {
  auto M = createBaseModule();

  auto *dispatch_jump = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "__omill_dispatch_jump",
      *M);

  auto *native_wrapper = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_wrapper);
    llvm::IRBuilder<> B(entry);
    auto *state = native_wrapper->getArg(0);
    B.CreateCall(dispatch_jump,
                 {state, B.getInt64(0x100001A6AULL), native_wrapper->getArg(2)});
    B.CreateRet(native_wrapper->getArg(2));
  }

  omill::BinaryMemoryMap map;
  map.setImageBase(0x140000000ULL);
  map.setImageSize(0x300000ULL);
  runPass(*M, map);

  bool saw_rax_store = false;
  bool saw_expected_target = false;
  for (auto &BB : *native_wrapper) {
    for (auto &I : BB) {
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI)
        continue;
      auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(SI->getPointerOperand());
      if (!GEP || GEP->getNumOperands() < 2)
        continue;
      auto *off = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
      if (!off || off->getZExtValue() != 2216)
        continue;
      saw_rax_store = true;
      if (auto *v = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand())) {
        if (v->getZExtValue() == 0x140001A6AULL)
          saw_expected_target = true;
      }
    }
  }

  EXPECT_TRUE(saw_rax_store);
  EXPECT_TRUE(saw_expected_target);
}

}  // namespace

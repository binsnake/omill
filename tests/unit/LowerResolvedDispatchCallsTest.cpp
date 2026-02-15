#include "omill/Passes/LowerResolvedDispatchCalls.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerResolvedDispatchCallsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerResolvedDispatchCallsPass());

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

    FPM.run(*F, FAM);
  }

  /// Create __omill_dispatch_call declaration.
  llvm::Function *createDispatchDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_call", M);
  }

  /// Create a dllimport function declaration.
  llvm::Function *createDLLImport(llvm::Module &M, llvm::StringRef name) {
    auto *void_ty = llvm::Type::getVoidTy(Ctx);
    auto *ft = llvm::FunctionType::get(void_ty, false);
    auto *fn = llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                       name, M);
    fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
    return fn;
  }

  unsigned countCallsTo(llvm::Function *F, llvm::StringRef callee_name) {
    unsigned count = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = llvm::dyn_cast<llvm::Function>(
                  CI->getCalledOperand()))
            if (callee->getName() == callee_name)
              count++;
    return count;
  }
};

TEST_F(LowerResolvedDispatchCallsTest, LowersResolvedCall) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);
  auto *import_fn = createDLLImport(*M, "VirtualAlloc");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Create ptrtoint(@VirtualAlloc) as dispatch target.
  auto *target = B.CreatePtrToInt(import_fn, i64_ty, "target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  EXPECT_EQ(countCallsTo(F, "__omill_dispatch_call"), 1u);

  runPass(F);

  // dispatch_call should be gone, replaced with native call to VirtualAlloc.
  EXPECT_EQ(countCallsTo(F, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCallsTo(F, "VirtualAlloc"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(LowerResolvedDispatchCallsTest, SkipsUnresolvedCall) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Unresolved: target is just a dynamic i64 value, not ptrtoint.
  auto *target = B.getInt64(0xDEADBEEF);
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  runPass(F);

  // dispatch_call should remain (not lowerable).
  EXPECT_EQ(countCallsTo(F, "__omill_dispatch_call"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(LowerResolvedDispatchCallsTest, SkipsNonDLLImport) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  // Non-dllimport function.
  auto *local_fn = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false),
      llvm::Function::ExternalLinkage, "local_func", *M);
  // Explicitly NOT setting DLLImportStorageClass.

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *target = B.CreatePtrToInt(local_fn, i64_ty, "target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  runPass(F);

  // dispatch_call should remain — target is not a DLL import.
  EXPECT_EQ(countCallsTo(F, "__omill_dispatch_call"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(LowerResolvedDispatchCallsTest, MultipleCalls) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);
  auto *import1 = createDLLImport(*M, "VirtualAlloc");
  auto *import2 = createDLLImport(*M, "VirtualFree");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Two resolved calls + one unresolved.
  auto *t1 = B.CreatePtrToInt(import1, i64_ty);
  B.CreateCall(dispatch, {state, t1, mem});

  auto *t2 = B.CreatePtrToInt(import2, i64_ty);
  B.CreateCall(dispatch, {state, t2, mem});

  auto *t3 = B.getInt64(0x12345678);
  B.CreateCall(dispatch, {state, t3, mem});

  B.CreateRet(mem);

  EXPECT_EQ(countCallsTo(F, "__omill_dispatch_call"), 3u);

  runPass(F);

  // Only two resolved ones lowered; one unresolved remains.
  EXPECT_EQ(countCallsTo(F, "__omill_dispatch_call"), 1u);
  EXPECT_EQ(countCallsTo(F, "VirtualAlloc"), 1u);
  EXPECT_EQ(countCallsTo(F, "VirtualFree"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(LowerResolvedDispatchCallsTest, StateFieldExtraction) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);
  auto *import_fn = createDLLImport(*M, "GetProcAddress");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *target = B.CreatePtrToInt(import_fn, i64_ty, "target");
  auto *result = B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(result);

  runPass(F);

  // Verify the lowered code loads RCX/RDX/R8/R9 from correct offsets
  // and stores result to RAX offset.
  static constexpr uint64_t kRCXOffset = 2248;
  static constexpr uint64_t kRDXOffset = 2264;
  static constexpr uint64_t kR8Offset = 2344;
  static constexpr uint64_t kR9Offset = 2360;
  static constexpr uint64_t kRAXOffset = 2216;

  bool found_rcx = false, found_rdx = false, found_r8 = false, found_r9 = false;
  bool found_rax_store = false;

  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        // Check for GEP + load with correct offsets.
        if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(
                LI->getPointerOperand())) {
          if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1))) {
            uint64_t off = CI->getZExtValue();
            if (off == kRCXOffset) found_rcx = true;
            if (off == kRDXOffset) found_rdx = true;
            if (off == kR8Offset) found_r8 = true;
            if (off == kR9Offset) found_r9 = true;
          }
        }
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(
                SI->getPointerOperand())) {
          if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1))) {
            if (CI->getZExtValue() == kRAXOffset)
              found_rax_store = true;
          }
        }
      }
    }
  }

  EXPECT_TRUE(found_rcx) << "RCX load not found at offset 2248";
  EXPECT_TRUE(found_rdx) << "RDX load not found at offset 2264";
  EXPECT_TRUE(found_r8) << "R8 load not found at offset 2344";
  EXPECT_TRUE(found_r9) << "R9 load not found at offset 2360";
  EXPECT_TRUE(found_rax_store) << "RAX store not found at offset 2216";
  EXPECT_EQ(countCallsTo(F, "GetProcAddress"), 1u);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

#include "omill/Passes/ResolveIATCalls.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"

#include <gtest/gtest.h>

namespace {

class ResolveIATCallsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create __omill_dispatch_call declaration.
  llvm::Function *createDispatchDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_call", M);
  }

  void runPass(llvm::Module *M, omill::BinaryMemoryMap map) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    // Register the BinaryMemoryAnalysis with the pre-built map.
    MAM.registerPass(
        [&]() { return omill::BinaryMemoryAnalysis(std::move(map)); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    // Pre-cache the BinaryMemoryAnalysis so getCachedResult finds it.
    (void)MAM.getResult<omill::BinaryMemoryAnalysis>(*M);

    // Use a ModulePassManager with function-to-module adaptor so that
    // the ModuleAnalysisManagerFunctionProxy is properly available.
    llvm::ModulePassManager MPM;
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(
        omill::ResolveIATCallsPass()));
    MPM.run(*M, MAM);
  }

  bool hasResolvedTarget(llvm::Function *F) {
    // Check if any dispatch_call arg[1] is now a ptrtoint of a function.
    // Use PtrToIntOperator to handle both instruction and ConstantExpr forms.
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI) continue;
        auto *callee = CI->getCalledFunction();
        if (!callee || callee->getName() != "__omill_dispatch_call") continue;
        if (CI->arg_size() < 2) continue;
        if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(
                CI->getArgOperand(1)))
          if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
            return true;
      }
    }
    return false;
  }
};

TEST_F(ResolveIATCallsTest, ResolvesDirectIATLoad) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Load target from IAT at address 0x140002000.
  auto *iat_ptr = B.CreateIntToPtr(B.getInt64(0x140002000), ptr_ty);
  auto *target = B.CreateLoad(i64_ty, iat_ptr, "iat_target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  // Build a memory map with an IAT entry at 0x140002000.
  omill::BinaryMemoryMap map;
  map.addImport(0x140002000, "kernel32", "VirtualAlloc");

  EXPECT_FALSE(hasResolvedTarget(F));

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasResolvedTarget(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveIATCallsTest, ResolvesPCRelativeAddress) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  // Entry VA = 0x140001000
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *pc = F->getArg(1);
  auto *mem = F->getArg(2);

  // RIP-relative: addr = pc + 0x1000 = 0x140001000 + 0x1000 = 0x140002000
  auto *iat_addr = B.CreateAdd(pc, B.getInt64(0x1000), "iat_addr");
  auto *iat_ptr = B.CreateIntToPtr(iat_addr, ptr_ty, "iat_ptr");
  auto *target = B.CreateLoad(i64_ty, iat_ptr, "iat_target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  omill::BinaryMemoryMap map;
  map.addImport(0x140002000, "kernel32", "VirtualAlloc");

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasResolvedTarget(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveIATCallsTest, SkipsUnmappedAddress) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Load from an unmapped IAT address.
  auto *iat_ptr = B.CreateIntToPtr(B.getInt64(0x140009999), ptr_ty);
  auto *target = B.CreateLoad(i64_ty, iat_ptr, "iat_target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  // Map has a DIFFERENT address.
  omill::BinaryMemoryMap map;
  map.addImport(0x140002000, "kernel32", "VirtualAlloc");

  runPass(M.get(), std::move(map));

  EXPECT_FALSE(hasResolvedTarget(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveIATCallsTest, SkipsAmbiguousSelect) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1_ty = llvm::Type::getInt1Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Create a select between two different IAT addresses.
  auto *cond_alloca = B.CreateAlloca(i1_ty);
  auto *cond = B.CreateLoad(i1_ty, cond_alloca, "cond");
  auto *addr = B.CreateSelect(cond, B.getInt64(0x140002000),
                               B.getInt64(0x140003000), "iat_sel");
  auto *iat_ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, iat_ptr, "iat_target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  // Both addresses map to DIFFERENT imports.
  omill::BinaryMemoryMap map;
  map.addImport(0x140002000, "kernel32", "VirtualAlloc");
  map.addImport(0x140003000, "kernel32", "VirtualFree");

  runPass(M.get(), std::move(map));

  // Should NOT be resolved — ambiguous.
  EXPECT_FALSE(hasResolvedTarget(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveIATCallsTest, SelectWithSameImportResolved) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1_ty = llvm::Type::getInt1Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // select(cond, 0x140002000, 0x140002000) → both arms same IAT entry.
  auto *cond_alloca = B.CreateAlloca(i1_ty);
  auto *cond = B.CreateLoad(i1_ty, cond_alloca, "cond");
  auto *addr = B.CreateSelect(cond, B.getInt64(0x140002000),
                               B.getInt64(0x140002000), "same_iat");
  auto *iat_ptr = B.CreateIntToPtr(addr, ptr_ty);
  auto *target = B.CreateLoad(i64_ty, iat_ptr, "iat_target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  omill::BinaryMemoryMap map;
  map.addImport(0x140002000, "kernel32", "VirtualAlloc");

  runPass(M.get(), std::move(map));

  EXPECT_TRUE(hasResolvedTarget(F));
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveIATCallsTest, DLLStorageClassSet) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "sub_140001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  auto *iat_ptr = B.CreateIntToPtr(B.getInt64(0x140002000), ptr_ty);
  auto *target = B.CreateLoad(i64_ty, iat_ptr, "iat_target");
  B.CreateCall(dispatch, {state, target, mem});
  B.CreateRet(mem);

  omill::BinaryMemoryMap map;
  map.addImport(0x140002000, "kernel32", "CreateFileW");

  runPass(M.get(), std::move(map));

  // Verify the created function has DLLImportStorageClass.
  auto *import_fn = M->getFunction("CreateFileW");
  ASSERT_NE(import_fn, nullptr);
  EXPECT_EQ(import_fn->getDLLStorageClass(),
            llvm::GlobalValue::DLLImportStorageClass);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

#include "omill/Passes/RecoverFunctionSignatures.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/CallingConventionAnalysis.h"

#include <gtest/gtest.h>

namespace {

class RecoverFunctionSignaturesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
};

TEST_F(RecoverFunctionSignaturesTest, CreatesNativeWrapper) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Create the State struct type
  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  // Create __remill_basic_block with register GEPs
  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);

  auto *bb_state = bb_fn->getArg(0);
  // Win64 ABI registers
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 0, "RAX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 16, "RCX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 24, "RDX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 64, "R8");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 72, "R9");
  BBB.CreateRet(bb_fn->getArg(2));

  // Create lifted function sub_401000 that reads RCX, RDX and writes RAX
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);

  auto *state = test_fn->getArg(0);
  auto *mem = test_fn->getArg(2);

  // Read RCX (offset 16) and RDX (offset 24)
  auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
  auto *rcx_val = B.CreateLoad(i64_ty, rcx_gep, "rcx_val");

  auto *rdx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 24);
  auto *rdx_val = B.CreateLoad(i64_ty, rdx_gep, "rdx_val");

  // Compute result and write to RAX (offset 0)
  auto *sum = B.CreateAdd(rcx_val, rdx_val, "sum");
  auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
  B.CreateStore(sum, rax_gep);

  B.CreateRet(mem);

  // Run the module pass
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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  // Verify sub_401000_native was created
  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);

  // Verify native function has i64(i64, i64) signature
  auto *native_ty = native_fn->getFunctionType();
  EXPECT_EQ(native_ty->getNumParams(), 2u);
  EXPECT_TRUE(native_ty->getParamType(0)->isIntegerTy(64));
  EXPECT_TRUE(native_ty->getParamType(1)->isIntegerTy(64));
  EXPECT_TRUE(native_ty->getReturnType()->isIntegerTy(64));

  // Verify the native wrapper has a body (not just a declaration)
  EXPECT_FALSE(native_fn->isDeclaration());

  // Verify wrapper calls the lifted entry with correct PC and null memory.
  llvm::CallInst *lifted_call = nullptr;
  for (auto &BB : *native_fn) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;
      if (CI->getCalledFunction() == test_fn) {
        lifted_call = CI;
        break;
      }
    }
    if (lifted_call) break;
  }
  ASSERT_NE(lifted_call, nullptr);
  auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(lifted_call->getArgOperand(1));
  ASSERT_NE(pc_arg, nullptr);
  EXPECT_EQ(pc_arg->getZExtValue(), 0x401000u);
  auto *mem_arg = llvm::dyn_cast<llvm::Constant>(lifted_call->getArgOperand(2));
  ASSERT_NE(mem_arg, nullptr);
  EXPECT_TRUE(mem_arg->isNullValue());
}

TEST_F(RecoverFunctionSignaturesTest, VoidReturnWrapper) {
  // Function that doesn't write RAX → void return type.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 0, "RAX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 16, "RCX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 24, "RDX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 64, "R8");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 72, "R9");
  BBB.CreateRet(bb_fn->getArg(2));

  // Lifted function that reads RCX but does NOT write RAX.
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), test_fn->getArg(0), 16);
  B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
  B.CreateRet(test_fn->getArg(2));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);

  // Void return: native wrapper returns void.
  EXPECT_TRUE(native_fn->getReturnType()->isVoidTy());
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 1u);
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootDropsForcedConstantLeadingGPRParam) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *helper = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    auto *rcx = B.CreateLoad(i64_ty, rcx_gep);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(rcx, rax_gep);
    B.CreateRet(helper->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    B.CreateStore(B.getInt64(0), rcx_gep);
    auto *ret_mem = B.CreateCall(helper, {state, root->getArg(1), root->getArg(2)});
    B.CreateRet(ret_mem);
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_TRUE(native_fn->getReturnType()->isIntegerTy(64));
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 0u);
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootKeepsAllRecoveredWin64GprParams) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 24, "RDX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 64, "R8");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    auto *rdx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 24);
    auto *r8_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 64);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    auto *rcx = B.CreateLoad(i64_ty, rcx_gep);
    auto *rdx = B.CreateLoad(i64_ty, rdx_gep);
    auto *r8 = B.CreateLoad(i64_ty, r8_gep);
    auto *sum = B.CreateAdd(B.CreateAdd(rcx, rdx), r8);
    B.CreateStore(sum, rax_gep);
    B.CreateRet(root->getArg(2));
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_TRUE(native_fn->getReturnType()->isIntegerTy(64));
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 3u);
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(0)->isIntegerTy(64));
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(1)->isIntegerTy(64));
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(2)->isIntegerTy(64));
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootWithoutEntryParamReadsDefaultsToZeroParams) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 24, "RDX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 64, "R8");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 72, "R9");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(1), rax_gep);
    B.CreateRet(root->getArg(2));
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 0u);
  EXPECT_TRUE(native_fn->getReturnType()->isIntegerTy(64));
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootWithoutEntryReadsUsesCallsiteEvidenceForParams) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 24, "RDX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 64, "R8");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 72, "R9");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(7), rax_gep);
    B.CreateRet(root->getArg(2));
  }

  auto *caller = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *state = caller->getArg(0);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    auto *rdx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 24);
    auto *r8_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 64);
    B.CreateStore(B.getInt64(11), rcx_gep);
    B.CreateStore(B.getInt64(22), rdx_gep);
    B.CreateStore(B.getInt64(33), r8_gep);
    auto *ret_mem =
        B.CreateCall(root, {state, caller->getArg(1), caller->getArg(2)});
    B.CreateRet(ret_mem);
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 3u);
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(0)->isIntegerTy(64));
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(1)->isIntegerTy(64));
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(2)->isIntegerTy(64));
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootUsesDriverProvidedExportCallsiteParamOverride) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 24, "RDX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 64, "R8");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 72, "R9");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.export_callsite_win64_gpr_count", "3");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateStore(B.getInt64(7), rax_gep);
    B.CreateRet(root->getArg(2));
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 3u);
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(0)->isIntegerTy(64));
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(1)->isIntegerTy(64));
  EXPECT_TRUE(native_fn->getFunctionType()->getParamType(2)->isIntegerTy(64));
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootPathSensitiveFallbackSkipsWrittenR9) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 24, "RDX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 64, "R8");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 72, "R9");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *body = llvm::BasicBlock::Create(Ctx, "body", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *r9_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 72);
    B.CreateStore(B.getInt64(0), r9_gep);
    B.CreateBr(body);

    B.SetInsertPoint(body);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    auto *rdx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 24);
    auto *r8_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 64);
    auto *r9_gep_body = B.CreateConstGEP1_64(B.getInt8Ty(), state, 72);
    auto *rcx = B.CreateLoad(i64_ty, rcx_gep);
    auto *rdx = B.CreateLoad(i64_ty, rdx_gep);
    auto *r8 = B.CreateLoad(i64_ty, r8_gep);
    auto *r9 = B.CreateLoad(i64_ty, r9_gep_body);
    auto *sum = B.CreateAdd(B.CreateAdd(B.CreateAdd(rcx, rdx), r8), r9);
    B.CreateStore(sum, rax_gep);
    B.CreateRet(root->getArg(2));
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 3u);
}

TEST_F(RecoverFunctionSignaturesTest,
       PublicOutputRootSeedsHiddenNonParamGPRConstants) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    auto *bb_state = bb_fn->getArg(0);
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 0, "RAX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 8, "RBX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 16, "RCX");
    B.CreateConstGEP1_64(B.getInt8Ty(), bb_state, 32, "RBP");
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *root = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *pc = root->getArg(1);

    auto *rbx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 8);
    auto *rbp_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 32);
    auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);

    auto *pc_seed = B.CreateAdd(pc, B.getInt64(0x321));
    B.CreateStore(pc_seed, rbx_gep);
    B.CreateStore(B.getInt64(0x123456789abcdef0ULL), rbp_gep);

    auto *rcx = B.CreateLoad(i64_ty, rcx_gep);
    auto *rbx = B.CreateLoad(i64_ty, rbx_gep);
    auto *rbp = B.CreateLoad(i64_ty, rbp_gep);
    auto *sum = B.CreateAdd(B.CreateAdd(rcx, rbx), rbp);
    B.CreateStore(sum, rax_gep);
    B.CreateRet(root->getArg(2));
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_EQ(native_fn->getFunctionType()->getNumParams(), 1u);

  bool saw_pc_relative_seed = false;
  bool saw_constant_seed = false;
  for (auto &BB : *native_fn) {
    for (auto &I : BB) {
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI)
        continue;
      auto *CI = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand());
      if (!CI)
        continue;
      if (CI->getZExtValue() == 0x401321ULL)
        saw_pc_relative_seed = true;
      if (CI->getZExtValue() == 0x123456789abcdef0ULL)
        saw_constant_seed = true;
    }
  }

  EXPECT_TRUE(saw_pc_relative_seed);
  EXPECT_TRUE(saw_constant_seed);
}

TEST_F(RecoverFunctionSignaturesTest,
       ClosedRootSliceScopeSkipsUnmarkedLiftedFunctions) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope",
                   1u);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 0, "RAX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 16, "RCX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 24, "RDX");
  BBB.CreateRet(bb_fn->getArg(2));

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *closed_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  closed_fn->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", closed_fn);
    llvm::IRBuilder<> B(entry);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), closed_fn->getArg(0), 0);
    B.CreateStore(B.getInt64(1), rax_gep);
    B.CreateRet(closed_fn->getArg(2));
  }

  auto *other_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", other_fn);
    llvm::IRBuilder<> B(entry);
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), other_fn->getArg(0), 0);
    B.CreateStore(B.getInt64(2), rax_gep);
    B.CreateRet(other_fn->getArg(2));
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *closed_native = M->getFunction("sub_401000_native");
  ASSERT_NE(closed_native, nullptr);
  EXPECT_TRUE(closed_native->hasFnAttribute("omill.closed_root_slice"));
  EXPECT_EQ(M->getFunction("sub_402000_native"), nullptr);
}

TEST_F(RecoverFunctionSignaturesTest,
       SkipsTerminalMissingBlockStubInClosedRootSliceScope) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(bb_fn->getArg(2));
  }

  auto *missing = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_missing_block", *M);

  auto *stub = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "blk_ffffffffac9b1737", *M);
  stub->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", stub);
    llvm::IRBuilder<> B(entry);
    auto *pc_gep = B.CreateConstGEP1_64(B.getInt8Ty(), stub->getArg(0), 2472);
    B.CreateStore(stub->getArg(1), pc_gep);
    auto *result = B.CreateCall(
        missing, {stub->getArg(0), stub->getArg(1), stub->getArg(2)});
    B.CreateRet(result);
  }

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  EXPECT_EQ(M->getFunction("blk_ffffffffac9b1737_native"), nullptr);
}

TEST_F(RecoverFunctionSignaturesTest, PropagatesDemergedVmAttributesToNativeWrapper) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 0, "RAX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 16, "RCX");
  BBB.CreateRet(bb_fn->getArg(2));

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000__vm_abcdef", *M);
  test_fn->addFnAttr("omill.vm_handler");
  test_fn->addFnAttr("omill.vm_demerged_clone", "1");
  test_fn->addFnAttr("omill.vm_outlined_virtual_call", "1");
  test_fn->addFnAttr("omill.vm_trace_in_hash", "abcdef");
  test_fn->addFnAttr("omill.vm_helper_hash", "abcdef");
  test_fn->addFnAttr("omill.vm_handler_va", "401000");
  test_fn->addFnAttr("omill.vm_trace_hash", "abcdef");
  test_fn->addFnAttr("omill.vm_helper_caller", "caller_native");
  test_fn->addFnAttr("omill.vm_virtual_callee_kind", "hash_resolved");
  test_fn->addFnAttr("omill.vm_virtual_callee_base", "sub_401000_native");
  test_fn->addFnAttr("omill.vm_virtual_callee_round", "2");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(test_fn->getArg(2));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  auto *native_fn = M->getFunction("sub_401000__vm_abcdef_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_TRUE(native_fn->hasFnAttribute("omill.vm_handler"));
  EXPECT_TRUE(native_fn->getFnAttribute("omill.vm_demerged_clone").isValid());
  EXPECT_TRUE(
      native_fn->getFnAttribute("omill.vm_outlined_virtual_call").isValid());
  EXPECT_TRUE(native_fn->hasFnAttribute(llvm::Attribute::NoInline));
  auto hash_attr = native_fn->getFnAttribute("omill.vm_trace_in_hash");
  ASSERT_TRUE(hash_attr.isValid());
  EXPECT_EQ(hash_attr.getValueAsString(), "abcdef");
  auto helper_hash_attr = native_fn->getFnAttribute("omill.vm_helper_hash");
  ASSERT_TRUE(helper_hash_attr.isValid());
  EXPECT_EQ(helper_hash_attr.getValueAsString(), "abcdef");
  auto helper_caller_attr = native_fn->getFnAttribute("omill.vm_helper_caller");
  ASSERT_TRUE(helper_caller_attr.isValid());
  EXPECT_EQ(helper_caller_attr.getValueAsString(), "caller_native");
  auto kind_attr = native_fn->getFnAttribute("omill.vm_virtual_callee_kind");
  ASSERT_TRUE(kind_attr.isValid());
  EXPECT_EQ(kind_attr.getValueAsString(), "hash_resolved");
  auto base_attr = native_fn->getFnAttribute("omill.vm_virtual_callee_base");
  ASSERT_TRUE(base_attr.isValid());
  EXPECT_EQ(base_attr.getValueAsString(), "sub_401000_native");
  auto round_attr = native_fn->getFnAttribute("omill.vm_virtual_callee_round");
  ASSERT_TRUE(round_attr.isValid());
  EXPECT_EQ(round_attr.getValueAsString(), "2");
  auto handler_va_attr = native_fn->getFnAttribute("omill.vm_handler_va");
  ASSERT_TRUE(handler_va_attr.isValid());
  EXPECT_EQ(handler_va_attr.getValueAsString(), "401000");
  auto trace_hash_attr = native_fn->getFnAttribute("omill.vm_trace_hash");
  ASSERT_TRUE(trace_hash_attr.isValid());
  EXPECT_EQ(trace_hash_attr.getValueAsString(), "abcdef");
}

TEST_F(RecoverFunctionSignaturesTest, SkipsFunctionsWithExistingNativeWrapper) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 0, "RAX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 16, "RCX");
  BBB.CreateRet(bb_fn->getArg(2));

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *lifted_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted_fn);
  llvm::IRBuilder<> B(entry);
  auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), lifted_fn->getArg(0), 16);
  auto *rcx_val = B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
  auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), lifted_fn->getArg(0), 0);
  B.CreateStore(rcx_val, rax_gep);
  B.CreateRet(lifted_fn->getArg(2));

  auto *existing_native = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {i64_ty}, false),
      llvm::Function::ExternalLinkage, "sub_401000_native", *M);
  auto *native_entry = llvm::BasicBlock::Create(Ctx, "entry", existing_native);
  llvm::IRBuilder<> NB(native_entry);
  NB.CreateRet(existing_native->getArg(0));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::RecoverFunctionSignaturesPass());
  MPM.run(*M, MAM);

  EXPECT_EQ(M->getFunction("sub_401000_native"), existing_native);
  EXPECT_EQ(M->getFunction("sub_401000_native.1"), nullptr);
}


}  // namespace

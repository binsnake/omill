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
}

}  // namespace

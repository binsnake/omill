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

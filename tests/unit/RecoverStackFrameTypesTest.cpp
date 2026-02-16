#include "omill/Passes/RecoverStackFrameTypes.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class RecoverStackFrameTypesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");
    return M;
  }

  llvm::Function *createFnWithStackFrame(llvm::Module &M, unsigned frame_size,
                                          const char *name = "test_func") {
    auto *void_ty = llvm::Type::getVoidTy(Ctx);
    auto *fn_ty = llvm::FunctionType::get(void_ty, {}, false);
    auto *fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(entry);

    auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
    auto *frame_ty = llvm::ArrayType::get(i8_ty, frame_size);
    B.CreateAlloca(frame_ty, nullptr, "stack_frame");

    return fn;
  }

  void runPass(llvm::Function &F) {
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

    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::RecoverStackFrameTypesPass());
    FPM.run(F, FAM);
  }
};

TEST_F(RecoverStackFrameTypesTest, SingleI64AtOffset0) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {}, false);
  auto *fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *frame_ty = llvm::ArrayType::get(i8_ty, 8);
  auto *alloca = B.CreateAlloca(frame_ty, nullptr, "stack_frame");

  auto *gep = B.CreateConstGEP1_64(i8_ty, alloca, 0, "field0");
  auto *load = B.CreateLoad(B.getInt64Ty(), gep, "val");
  auto *store_gep = B.CreateConstGEP1_64(i8_ty, alloca, 0, "field0_store");
  B.CreateStore(load, store_gep);
  B.CreateRetVoid();

  EXPECT_FALSE(llvm::verifyFunction(*fn, &llvm::errs()));

  runPass(*fn);

  EXPECT_FALSE(llvm::verifyFunction(*fn, &llvm::errs()));

  // Check that a typed alloca exists.
  bool found_typed = false;
  for (auto &I : fn->getEntryBlock()) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (auto *ST = llvm::dyn_cast<llvm::StructType>(AI->getAllocatedType())) {
        found_typed = true;
        EXPECT_GE(ST->getNumElements(), 1u);
        EXPECT_EQ(ST->getElementType(0), llvm::Type::getInt64Ty(Ctx));
      }
    }
  }
  EXPECT_TRUE(found_typed);
}

TEST_F(RecoverStackFrameTypesTest, MultipleFieldsWithPadding) {
  auto M = createModule();
  auto *fn = createFnWithStackFrame(*M, 24);
  auto *entry = &fn->getEntryBlock();
  auto *alloca = &*entry->begin();

  llvm::IRBuilder<> B(entry);
  B.CreateRetVoid();
  B.SetInsertPoint(entry->getTerminator());

  // i64 at offset 0
  auto *gep0 = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 0);
  B.CreateLoad(B.getInt64Ty(), gep0);

  // i32 at offset 8
  auto *gep8 = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 8);
  B.CreateLoad(B.getInt32Ty(), gep8);

  // i64 at offset 16
  auto *gep16 = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, 16);
  B.CreateLoad(B.getInt64Ty(), gep16);

  runPass(*fn);
  EXPECT_FALSE(llvm::verifyFunction(*fn, &llvm::errs()));

  // Check struct layout: {i64, i32, [4 x i8], i64}
  for (auto &I : fn->getEntryBlock()) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (auto *ST = llvm::dyn_cast<llvm::StructType>(AI->getAllocatedType())) {
        ASSERT_GE(ST->getNumElements(), 3u);
        EXPECT_EQ(ST->getElementType(0), llvm::Type::getInt64Ty(Ctx));
        EXPECT_EQ(ST->getElementType(1), llvm::Type::getInt32Ty(Ctx));
        // Element 2 is padding [4 x i8].
        auto *pad = llvm::dyn_cast<llvm::ArrayType>(ST->getElementType(2));
        ASSERT_NE(pad, nullptr);
        EXPECT_EQ(pad->getNumElements(), 4u);
        EXPECT_EQ(ST->getElementType(3), llvm::Type::getInt64Ty(Ctx));
        break;
      }
    }
  }
}

TEST_F(RecoverStackFrameTypesTest, NoAccessesUnchanged) {
  auto M = createModule();
  auto *fn = createFnWithStackFrame(*M, 32);
  auto *entry = &fn->getEntryBlock();
  llvm::IRBuilder<> B(entry);
  B.CreateRetVoid();

  runPass(*fn);

  // Original [N x i8] alloca should remain.
  bool found_array = false;
  for (auto &I : fn->getEntryBlock()) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (llvm::isa<llvm::ArrayType>(AI->getAllocatedType())) {
        found_array = true;
      }
    }
  }
  EXPECT_TRUE(found_array);
}

TEST_F(RecoverStackFrameTypesTest, NotNamedStackFrameSkipped) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, {}, false);
  auto *fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *frame_ty = llvm::ArrayType::get(i8_ty, 16);
  auto *alloca = B.CreateAlloca(frame_ty, nullptr, "local_buffer");

  // Add a load at offset 0.
  auto *gep = B.CreateConstGEP1_64(i8_ty, alloca, 0);
  B.CreateLoad(B.getInt64Ty(), gep);
  B.CreateRetVoid();

  runPass(*fn);

  // Should NOT be converted — name doesn't start with "stack_frame".
  bool found_struct = false;
  for (auto &I : fn->getEntryBlock()) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
      if (llvm::isa<llvm::StructType>(AI->getAllocatedType())) {
        found_struct = true;
      }
    }
  }
  EXPECT_FALSE(found_struct);
}

}  // namespace

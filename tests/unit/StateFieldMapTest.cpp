#include "omill/Utils/StateFieldMap.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include <gtest/gtest.h>

namespace {

class StateFieldMapTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
};

TEST_F(StateFieldMapTest, FindsRegistersFromBasicBlock) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> B(bb_entry);

  B.CreateConstGEP1_64(B.getInt8Ty(), bb_fn->getArg(0), 0, "RAX");
  B.CreateConstGEP1_64(B.getInt8Ty(), bb_fn->getArg(0), 16, "RCX");
  B.CreateConstGEP1_64(B.getInt8Ty(), bb_fn->getArg(0), 40, "RDI");
  B.CreateConstGEP1_64(B.getInt8Ty(), bb_fn->getArg(0), 48, "RSP");
  B.CreateRet(bb_fn->getArg(2));

  omill::StateFieldMap field_map(*M);

  auto rax = field_map.fieldByName("RAX");
  ASSERT_TRUE(rax.has_value()) << "RAX not found";
  EXPECT_EQ(rax->offset, 0u);
  EXPECT_EQ(rax->category, omill::StateFieldCategory::kGPR);

  auto rcx = field_map.fieldByName("RCX");
  ASSERT_TRUE(rcx.has_value()) << "RCX not found";
  EXPECT_EQ(rcx->offset, 16u);

  auto rdi = field_map.fieldByName("RDI");
  ASSERT_TRUE(rdi.has_value()) << "RDI not found";
  EXPECT_EQ(rdi->offset, 40u);

  auto rsp = field_map.fieldByName("RSP");
  ASSERT_TRUE(rsp.has_value()) << "RSP not found";
  EXPECT_EQ(rsp->offset, 48u);

  auto at_40 = field_map.fieldAtOffset(40);
  ASSERT_TRUE(at_40.has_value());
  EXPECT_EQ(at_40->name, "RDI");
}

}  // namespace

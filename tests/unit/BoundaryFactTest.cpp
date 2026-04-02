#include "omill/Devirtualization/BoundaryFact.h"

#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

namespace {

TEST(BoundaryFactTest, RoundTripsCallAttrs) {
  llvm::LLVMContext ctx;
  llvm::Module module("boundary_call", ctx);
  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *fn = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                    "sub_401000", module);
  auto *callee = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "omill_native_target_401120",
      module);
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", fn);
  llvm::IRBuilder<> b(entry);
  auto *call = b.CreateCall(callee, {fn->getArg(0), fn->getArg(1), fn->getArg(2)});
  b.CreateRet(fn->getArg(2));

  omill::BoundaryFact fact;
  fact.boundary_pc = 0x401100;
  fact.native_target_pc = 0x401120;
  fact.continuation_pc = 0x401130;
  fact.continuation_vip_pc = 0x401130;
  fact.continuation_slot_id = 7;
  fact.continuation_stack_cell_id = 11;
  fact.continuation_owner_id = 7;
  fact.continuation_owner_kind = omill::VirtualStackOwnerKind::kFramePointerLike;
  fact.kind = omill::BoundaryKind::kNativeBoundary;
  fact.exit_disposition = omill::BoundaryDisposition::kVmExitNativeCallReenter;
  fact.is_partial_exit = true;
  fact.reenters_vm = true;

  omill::writeBoundaryFact(*call, fact);
  auto roundtrip = omill::readBoundaryFact(*call);
  ASSERT_TRUE(roundtrip.has_value());
  EXPECT_EQ(*roundtrip, fact);
}

TEST(BoundaryFactTest, RoundTripsFunctionAttrs) {
  llvm::LLVMContext ctx;
  llvm::Module module("boundary_fn", ctx);
  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *fn = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "omill_vm_enter_target_401220",
      module);

  omill::BoundaryFact fact;
  fact.boundary_pc = 0x401220;
  fact.continuation_vip_pc = 0x401280;
  fact.continuation_slot_id = 3;
  fact.continuation_owner_id = 3;
  fact.continuation_owner_kind = omill::VirtualStackOwnerKind::kVmStackRootSlot;
  fact.kind = omill::BoundaryKind::kNestedVmEnterBoundary;
  fact.exit_disposition = omill::BoundaryDisposition::kNestedVmEnter;
  fact.is_nested_vm_enter = true;

  omill::writeBoundaryFact(*fn, fact);
  auto roundtrip = omill::readBoundaryFact(*fn);
  ASSERT_TRUE(roundtrip.has_value());
  EXPECT_EQ(*roundtrip, fact);
}

}  // namespace

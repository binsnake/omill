#include "omill/Devirtualization/OutputRootClosure.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include <gtest/gtest.h>

namespace {

TEST(OutputRootClosureTest, CanIncludeDefinedDispatchTargetsForPatchOnlyPasses) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(lifted_ty, llvm::GlobalValue::ExternalLinkage,
                                      "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__remill_function_call",
      module);
  auto *defined_target = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_180001000", module);
  llvm::BasicBlock::Create(ctx, "entry", defined_target);

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  auto *call = builder.CreateCall(
      dispatch, {state, llvm::ConstantInt::get(i64_ty, 0x180001000), memory});
  builder.CreateRet(call);

  auto collect_targets = [&](bool include_defined_targets) {
    return omill::collectOutputRootClosureTargets(
        module,
        [&](uint64_t target) {
          return target >= 0x180001000 && target < 0x180002000;
        },
        [&](uint64_t target) { return target == 0x180001000; },
        [&](uint64_t target) { return target; }, include_defined_targets);
  };

  auto unresolved_only = collect_targets(false);
  EXPECT_TRUE(unresolved_only.constant_code_targets.empty());

  auto patchable = collect_targets(true);
  ASSERT_EQ(patchable.constant_code_targets.size(), 1u);
  EXPECT_EQ(patchable.constant_code_targets.front(), 0x180001000u);
}

TEST(OutputRootClosureTest, IncludesDefinedRemillJumpTargetsForPatchOnlyPasses) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(lifted_ty, llvm::GlobalValue::ExternalLinkage,
                                      "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *jump = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__remill_jump", module);
  auto *defined_target = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_180001020", module);
  llvm::BasicBlock::Create(ctx, "entry", defined_target);

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  auto *call = builder.CreateCall(
      jump, {state, llvm::ConstantInt::get(i64_ty, 0x180001020), memory});
  builder.CreateRet(call);

  auto unresolved_only = omill::collectOutputRootClosureTargets(
      module,
      [&](uint64_t target) { return target >= 0x180001000 && target < 0x180002000; },
      [&](uint64_t target) { return target == 0x180001020; },
      [&](uint64_t target) { return target; }, false);
  EXPECT_TRUE(unresolved_only.constant_code_targets.empty());

  auto patchable = omill::collectOutputRootClosureTargets(
      module,
      [&](uint64_t target) { return target >= 0x180001000 && target < 0x180002000; },
      [&](uint64_t target) { return target == 0x180001020; },
      [&](uint64_t target) { return target; }, true);
  ASSERT_EQ(patchable.constant_code_targets.size(), 1u);
  EXPECT_EQ(patchable.constant_code_targets.front(), 0x180001020u);
}

TEST(OutputRootClosureTest, ProducesTypedWorkItemsForConstantJumpTargets) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(lifted_ty, llvm::GlobalValue::ExternalLinkage,
                                      "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *jump = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__remill_jump", module);

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  auto *call = builder.CreateCall(
      jump, {state, llvm::ConstantInt::get(i64_ty, 0x180001020), memory});
  call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_exec_unknown_return"));
  builder.CreateRet(call);

  auto items = omill::collectOutputRootClosureWorkItems(
      module,
      [&](uint64_t target) { return target >= 0x180001000 && target < 0x180002000; },
      [&](uint64_t) { return false; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  ASSERT_FALSE(items.empty());
  auto it = std::find_if(items.begin(), items.end(),
                         [](const omill::OutputRootClosureWorkItem &item) {
                           return item.target_pc == 0x180001020u &&
                                  item.source_kind ==
                                      omill::OutputRootClosureSourceKind::kConstantCodeTarget &&
                                  item.exit_disposition ==
                                      omill::VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
                         });
  ASSERT_NE(it, items.end());
  EXPECT_EQ(it->owner_function, "sub_180001850");
  EXPECT_FALSE(it->identity.empty());
}

TEST(OutputRootClosureTest, IncludesBlkDeclarationCalleesAsClosureTargets) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(lifted_ty, llvm::GlobalValue::ExternalLinkage,
                                      "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *blk_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_180001145", module);

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  auto *call = builder.CreateCall(
      blk_decl, {state, llvm::ConstantInt::get(i64_ty, 0x180001145), memory});
  builder.CreateRet(call);

  auto items = omill::collectOutputRootClosureWorkItems(
      module,
      [&](uint64_t target) { return target >= 0x180001000 && target < 0x180002000; },
      [&](uint64_t) { return false; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  auto it = std::find_if(items.begin(), items.end(),
                         [](const omill::OutputRootClosureWorkItem &item) {
                           return item.target_pc == 0x180001145u &&
                                  item.source_kind ==
                                      omill::OutputRootClosureSourceKind::kConstantCodeTarget;
                         });
  ASSERT_NE(it, items.end());
  EXPECT_EQ(it->owner_function, "sub_180001850");
}

TEST(OutputRootClosureTest,
     IncludesAbiNativeBoundaryDeclarationBoundaryPcAsClosureTarget) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *boundary_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage,
      "omill_native_boundary_1801F7733", module);
  boundary_decl->addFnAttr("omill.native_boundary_pc", "1801F7733");

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  builder.CreateCall(
      boundary_decl, {state, llvm::ConstantInt::get(i64_ty, 0x1801F7733), memory});
  builder.CreateRet(memory);

  auto items = omill::collectOutputRootClosureWorkItems(
      module,
      [&](uint64_t target) { return target >= 0x180000000 && target < 0x180200000; },
      [&](uint64_t) { return false; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  auto it = std::find_if(items.begin(), items.end(),
                         [](const omill::OutputRootClosureWorkItem &item) {
                           return item.target_pc == 0x1801F7733u &&
                                  item.source_kind ==
                                      omill::OutputRootClosureSourceKind::kConstantCodeTarget;
                         });
  ASSERT_NE(it, items.end());
}

TEST(OutputRootClosureTest,
     PrefersAbiNativeDirectTargetAttributeForClosureTargets) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *boundary_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage,
      "omill_native_target_1801311A7", module);
  boundary_decl->addFnAttr("omill.native_boundary_pc", "1800B9D48");
  boundary_decl->addFnAttr("omill.native_direct_target_pc", "1801311A7");

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  builder.CreateCall(
      boundary_decl, {state, llvm::ConstantInt::get(i64_ty, 0x1800B9D48), memory});
  builder.CreateRet(memory);

  auto targets = omill::collectOutputRootClosureTargets(
      module,
      [&](uint64_t target) { return target >= 0x180000000 && target < 0x180200000; },
      [&](uint64_t) { return false; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  ASSERT_EQ(targets.constant_code_targets.size(), 1u);
  EXPECT_EQ(targets.constant_code_targets.front(), 0x1801311A7u);
}

TEST(OutputRootClosureTest,
     IncludesAbiExecutableTargetAttributeForClosureTargets) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *executable_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage,
      "omill_executable_target_1801F7733", module);
  executable_decl->addFnAttr("omill.executable_target_pc", "1801F7733");

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  builder.CreateCall(
      executable_decl,
      {state, llvm::ConstantInt::get(i64_ty, 0x1801F7733), memory});
  builder.CreateRet(memory);

  auto items = omill::collectOutputRootClosureWorkItems(
      module,
      [&](uint64_t target) {
        return target >= 0x180000000 && target < 0x180200000;
      },
      [&](uint64_t) { return false; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  auto it = std::find_if(items.begin(), items.end(),
                         [](const omill::OutputRootClosureWorkItem &item) {
                           return item.target_pc == 0x1801F7733u &&
                                  item.source_kind ==
                                      omill::OutputRootClosureSourceKind::kConstantCodeTarget;
                         });
  ASSERT_NE(it, items.end());
}

TEST(OutputRootClosureTest,
     IncludesAbiVmEnterTargetAttributeAndDispositionForClosureTargets) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *vm_enter_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage,
      "omill_vm_enter_target_1801F7733", module);
  vm_enter_decl->addFnAttr("omill.vm_enter_target_pc", "1801F7733");
  vm_enter_decl->addFnAttr("omill.virtual_exit_disposition",
                           "nested_vm_enter");

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *pc = &*args++;
  llvm::Value *memory = &*args++;
  builder.CreateCall(
      vm_enter_decl,
      {state, llvm::ConstantInt::get(i64_ty, 0x1801F7733), memory});
  builder.CreateRet(memory);

  auto items = omill::collectOutputRootClosureWorkItems(
      module,
      [&](uint64_t target) {
        return target >= 0x180000000 && target < 0x180200000;
      },
      [&](uint64_t) { return false; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  auto it = std::find_if(items.begin(), items.end(),
                         [](const omill::OutputRootClosureWorkItem &item) {
                           return item.target_pc == 0x1801F7733u &&
                                  item.exit_disposition ==
                                      omill::VirtualExitDisposition::kNestedVmEnter;
                         });
  ASSERT_NE(it, items.end());
}

TEST(OutputRootClosureTest,
     KeepsDefinedVmEnterPlaceholderAsFrontierWorkWhenTargetsExcluded) {
  llvm::LLVMContext ctx;
  llvm::Module module("test", ctx);

  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180001850", module);
  root->addFnAttr("omill.output_root");
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", root);
  llvm::IRBuilder<> builder(entry);

  auto *vm_enter_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage,
      "omill_vm_enter_target_1801F7733", module);
  vm_enter_decl->addFnAttr("omill.vm_enter_target_pc", "1801F7733");
  vm_enter_decl->addFnAttr("omill.virtual_exit_disposition",
                           "nested_vm_enter");

  auto args = root->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *memory = &*(++args);
  auto *call = builder.CreateCall(
      vm_enter_decl,
      {state, llvm::ConstantInt::get(i64_ty, 0x1801F7733), memory});
  call->addFnAttr(
      llvm::Attribute::get(ctx, "omill.virtual_exit_disposition",
                           "nested_vm_enter"));
  builder.CreateRet(memory);

  auto items = omill::collectOutputRootClosureWorkItems(
      module,
      [&](uint64_t target) {
        return target >= 0x180000000 && target < 0x180200000;
      },
      [&](uint64_t target) { return target == 0x1801F7733u; },
      [&](uint64_t target) { return target; },
      /*include_defined_targets=*/false);
  auto it = std::find_if(items.begin(), items.end(),
                         [](const omill::OutputRootClosureWorkItem &item) {
                           return item.target_pc == 0x1801F7733u &&
                                  item.exit_disposition ==
                                      omill::VirtualExitDisposition::kNestedVmEnter;
                         });
  ASSERT_NE(it, items.end());
}

}  // namespace

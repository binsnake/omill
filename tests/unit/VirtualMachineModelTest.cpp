#include "omill/Analysis/VirtualModel/Analysis.h"

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

#include <stdlib.h>

#include <algorithm>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Omill.h"
#include "omill/Support/JumpTableDiscovery.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill::virtual_model::detail {
void summarizeDispatchSuccessors(llvm::Module &M,
                                 ::omill::VirtualMachineModel &model,
                                 const ::omill::BinaryMemoryMap &binary_memory);
}

namespace {

class VirtualMachineModelTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("vm-model", Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    return M;
  }

  omill::VirtualMachineModel runAnalysis(
      llvm::Module &M, omill::BinaryMemoryMap map = {}) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass(
        [&]() { return omill::BinaryMemoryAnalysis(std::move(map)); });
    MAM.registerPass([] { return omill::VirtualMachineModelAnalysis(); });
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    return MAM.getResult<omill::VirtualMachineModelAnalysis>(M);
  }

  void setEnv(const char *name, const char *value) { _putenv_s(name, value); }

  void unsetEnv(const char *name) { _putenv_s(name, ""); }

  void addMinimalX86FlagStateTypes(llvm::Module &M) {
    auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *aflags_ty = llvm::StructType::create(Ctx, "struct.ArithFlags");
    aflags_ty->setBody({i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty,
                        i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty},
                       false);

    auto *pad_ty = llvm::ArrayType::get(i8_ty, 0x810);
    auto *gpr_ty = llvm::StructType::create(Ctx, "struct.GPR");
    gpr_ty->setBody({i64_ty, i64_ty}, false);
    auto *x86_ty = llvm::StructType::create(Ctx, "struct.X86State");
    x86_ty->setBody({pad_ty, aflags_ty, gpr_ty}, false);

    auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
    state_ty->setBody({x86_ty}, false);
  }
};

TEST_F(VirtualMachineModelTest, DetectsProtectedBoundaryDeclaration) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");
  boundary->addFnAttr("omill.boundary_target_va", "180055365");

  auto model = runAnalysis(*M);
  auto *info = model.lookupBoundary("vm_entry_180042ba4");
  ASSERT_NE(info, nullptr);
  EXPECT_EQ(info->kind, omill::VirtualBoundaryKind::kProtectedEntryStub);
  ASSERT_TRUE(info->entry_va.has_value());
  EXPECT_EQ(*info->entry_va, 0x180042BA4ULL);
  ASSERT_TRUE(info->target_va.has_value());
  EXPECT_EQ(*info->target_va, 0x180055365ULL);
}

TEST_F(VirtualMachineModelTest, SummarizesCandidateHandlerFromIrShape) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *handler = llvm::Function::Create(handler_ty,
                                         llvm::Function::ExternalLinkage,
                                         "sub_180001850", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);
  auto *state = handler->getArg(0);
  auto *slot0 = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
  auto *slot1 = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
  auto *vip = B.CreateLoad(i64_ty, slot0);
  B.CreateStore(B.getInt64(0x1234), slot1);

  llvm::SmallVector<llvm::Value *, 12> boundary_args(12, B.getInt64(0));
  boundary_args[0] = vip;
  B.CreateCall(boundary_ty, boundary, boundary_args);
  auto *target = B.CreateLoad(i64_ty, slot1);
  B.CreateCall(dispatch_ty, dispatch, {state, target, handler->getArg(2)});
  B.CreateRetVoid();

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180001850");
  ASSERT_NE(summary, nullptr);
  EXPECT_EQ(summary->protected_boundary_call_count, 1u);
  EXPECT_EQ(summary->dispatch_jump_count, 1u);
  EXPECT_TRUE(summary->is_candidate);
  EXPECT_EQ(summary->called_boundaries.size(), 1u);
  EXPECT_EQ(summary->called_boundaries.front(), "vm_entry_180042ba4");
  ASSERT_GE(summary->state_slots.size(), 2u);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  EXPECT_TRUE(summary->dispatches.front().is_jump);
  EXPECT_EQ(omill::renderVirtualValueExpr(summary->dispatches.front().target),
            "slot(arg0+0x190)");
  ASSERT_EQ(summary->state_transfers.size(), 1u);
  EXPECT_EQ(summary->state_transfers.front().target_slot.offset, 0x190);
  EXPECT_EQ(omill::renderVirtualValueExpr(summary->state_transfers.front().value),
            "0x1234");
}

TEST_F(VirtualMachineModelTest, InvalidatesCachedHandlerSummaryAfterBodyChange) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *handler = llvm::Function::Create(handler_ty,
                                         llvm::Function::ExternalLinkage,
                                         "sub_1800018f0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
    llvm::IRBuilder<> B(entry);
    B.CreateRetVoid();
  }

  auto first_model = runAnalysis(*M);
  auto *first_summary = first_model.lookupHandler("sub_1800018f0");
  ASSERT_NE(first_summary, nullptr);
  EXPECT_EQ(first_summary->dispatch_jump_count, 0u);

  handler->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(dispatch_ty, dispatch,
                 {handler->getArg(0), B.getInt64(0x180001920ULL),
                  handler->getArg(2)});
    B.CreateRetVoid();
  }

  auto second_model = runAnalysis(*M);
  auto *second_summary = second_model.lookupHandler("sub_1800018f0");
  ASSERT_NE(second_summary, nullptr);
  EXPECT_EQ(second_summary->dispatch_jump_count, 1u);
}

TEST_F(VirtualMachineModelTest, InvalidatesCachedOutgoingFactsAfterCalleeBodyChange) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180001900", *M);
  auto build_helper = [&](uint64_t target_pc) {
    helper->deleteBody();
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x108));
    B.CreateStore(B.getInt64(target_pc), slot);
    B.CreateRet(helper->getArg(0));
  };
  build_helper(0x180001980ULL);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    auto *target_pc = B.CreateLoad(i64_ty, slot);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto first_model = runAnalysis(*M);
  auto *first_summary = first_model.lookupHandler("sub_180001850");
  ASSERT_NE(first_summary, nullptr);
  ASSERT_EQ(first_summary->dispatches.size(), 1u);
  ASSERT_EQ(first_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(first_summary->dispatches.front().successors.front().target_pc,
            0x180001980ULL);

  build_helper(0x1800019A0ULL);

  auto second_model = runAnalysis(*M);
  auto *second_summary = second_model.lookupHandler("sub_180001850");
  ASSERT_NE(second_summary, nullptr);
  ASSERT_EQ(second_summary->dispatches.size(), 1u);
  ASSERT_EQ(second_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(second_summary->dispatches.front().successors.front().target_pc,
            0x1800019A0ULL);
}

TEST_F(VirtualMachineModelTest, RecoversSymbolicDispatchAndStateTransfer) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *handler = llvm::Function::Create(handler_ty,
                                         llvm::Function::ExternalLinkage,
                                         "sub_180004000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);
  auto *state = handler->getArg(0);
  auto *slot0 = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
  auto *slot1 = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
  auto *slot2 = B.CreateGEP(i8_ty, state, B.getInt64(0x198));
  auto *vip = B.CreateLoad(i64_ty, slot0);
  auto *mixed = B.CreateAdd(vip, B.getInt64(0x40));
  auto *target = B.CreateXor(mixed, B.getInt64(0x55));
  auto *transfer = B.CreateOr(target, B.getInt64(0x10));
  B.CreateStore(transfer, slot1);
  B.CreateStore(B.CreateSub(vip, B.getInt64(1)), slot2);
  B.CreateCall(dispatch_ty, dispatch, {state, target, handler->getArg(2)});
  B.CreateRetVoid();

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  EXPECT_EQ(omill::renderVirtualValueExpr(summary->dispatches.front().target),
            "xor(add(slot(arg0+0x108), 0x40), 0x55)");

  ASSERT_EQ(summary->state_transfers.size(), 2u);
  EXPECT_EQ(summary->state_transfers[0].target_slot.offset, 0x190);
  EXPECT_EQ(omill::renderVirtualValueExpr(summary->state_transfers[0].value),
            "or(xor(add(slot(arg0+0x108), 0x40), 0x55), 0x10)");
  EXPECT_EQ(summary->state_transfers[1].target_slot.offset, 0x198);
  EXPECT_EQ(omill::renderVirtualValueExpr(summary->state_transfers[1].value),
            "sub(slot(arg0+0x108), 0x1)");
}

TEST_F(VirtualMachineModelTest, CanonicalizesSharedStateSlotsAcrossHandlers) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *handler_a = llvm::Function::Create(handler_ty,
                                           llvm::Function::ExternalLinkage,
                                           "sub_180004100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler_a);
    llvm::IRBuilder<> B(entry);
    auto *state = handler_a->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot);
    B.CreateCall(dispatch_ty, dispatch, {state, vip, handler_a->getArg(2)});
    B.CreateRetVoid();
  }

  auto *handler_b = llvm::Function::Create(handler_ty,
                                           llvm::Function::ExternalLinkage,
                                           "sub_180004200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler_b);
    llvm::IRBuilder<> B(entry);
    auto *state = handler_b->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot);
    B.CreateCall(dispatch_ty, dispatch,
                 {state, B.CreateAdd(vip, B.getInt64(1)), handler_b->getArg(2)});
    B.CreateRetVoid();
  }

  auto model = runAnalysis(*M);
  auto *summary_a = model.lookupHandler("sub_180004100");
  auto *summary_b = model.lookupHandler("sub_180004200");
  ASSERT_NE(summary_a, nullptr);
  ASSERT_NE(summary_b, nullptr);
  ASSERT_GE(model.slots().size(), 1u);
  ASSERT_EQ(summary_a->state_slots.size(), 1u);
  ASSERT_EQ(summary_b->state_slots.size(), 1u);
  ASSERT_TRUE(summary_a->state_slots.front().canonical_id.has_value());
  ASSERT_TRUE(summary_b->state_slots.front().canonical_id.has_value());
  EXPECT_EQ(*summary_a->state_slots.front().canonical_id,
            *summary_b->state_slots.front().canonical_id);
  auto *slot = model.lookupSlot(*summary_a->state_slots.front().canonical_id);
  ASSERT_NE(slot, nullptr);
  EXPECT_EQ(slot->offset, 0x108);
  EXPECT_EQ(slot->handler_names.size(), 2u);
}

TEST_F(VirtualMachineModelTest,
       PropagatesAbstractStateFactsAcrossDirectHandlerCalls) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *callee = llvm::Function::Create(handler_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004400", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", callee);
    llvm::IRBuilder<> B(entry);
    auto *state = callee->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *target = B.CreateLoad(i64_ty, slot);
    B.CreateCall(dispatch_ty, dispatch, {state, target, callee->getArg(2)});
    B.CreateRetVoid();
  }

  auto *caller = llvm::Function::Create(handler_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004300", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *state = caller->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x4010), slot);
    B.CreateCall(handler_ty, callee, {state, caller->getArg(1), caller->getArg(2)});
    B.CreateRetVoid();
  }

  auto model = runAnalysis(*M);
  auto *caller_summary = model.lookupHandler("sub_180004300");
  auto *callee_summary = model.lookupHandler("sub_180004400");
  ASSERT_NE(caller_summary, nullptr);
  ASSERT_NE(callee_summary, nullptr);
  ASSERT_EQ(caller_summary->outgoing_facts.size(), 1u);
  EXPECT_EQ(omill::renderVirtualValueExpr(caller_summary->outgoing_facts.front().value),
            "0x4010");
  ASSERT_EQ(callee_summary->incoming_facts.size(), 1u);
  EXPECT_EQ(omill::renderVirtualValueExpr(callee_summary->incoming_facts.front().value),
            "0x4010");
  ASSERT_EQ(callee_summary->outgoing_facts.size(), 1u);
  EXPECT_EQ(omill::renderVirtualValueExpr(callee_summary->outgoing_facts.front().value),
            "0x4010");
  EXPECT_TRUE(std::find(caller_summary->direct_callees.begin(),
                        caller_summary->direct_callees.end(),
                        "sub_180004400") != caller_summary->direct_callees.end());
}

TEST_F(VirtualMachineModelTest,
       PreservesSmallIncomingFactConflictsAsPhiChoices) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *callee = llvm::Function::Create(handler_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004520", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", callee);
    llvm::IRBuilder<> B(entry);
    auto *state = callee->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *target = B.CreateLoad(i64_ty, slot);
    B.CreateCall(dispatch_ty, dispatch, {state, target, callee->getArg(2)});
    B.CreateRetVoid();
  }

  auto *caller_a = llvm::Function::Create(handler_ty,
                                          llvm::Function::ExternalLinkage,
                                          "sub_180004500", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_a);
    llvm::IRBuilder<> B(entry);
    auto *state = caller_a->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x4010), slot);
    B.CreateCall(handler_ty, callee,
                 {state, caller_a->getArg(1), caller_a->getArg(2)});
    B.CreateRetVoid();
  }

  auto *caller_b = llvm::Function::Create(handler_ty,
                                          llvm::Function::ExternalLinkage,
                                          "sub_180004510", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_b);
    llvm::IRBuilder<> B(entry);
    auto *state = caller_b->getArg(0);
    auto *slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x4020), slot);
    B.CreateCall(handler_ty, callee,
                 {state, caller_b->getArg(1), caller_b->getArg(2)});
    B.CreateRetVoid();
  }

  auto model = runAnalysis(*M);
  auto *callee_summary = model.lookupHandler("sub_180004520");
  ASSERT_NE(callee_summary, nullptr);
  ASSERT_EQ(callee_summary->incoming_facts.size(), 1u);
  EXPECT_EQ(
      omill::renderVirtualValueExpr(callee_summary->incoming_facts.front().value),
      "phi(0x4010, 0x4020)");
  ASSERT_EQ(callee_summary->outgoing_facts.size(), 1u);
  EXPECT_EQ(
      omill::renderVirtualValueExpr(callee_summary->outgoing_facts.front().value),
      "phi(0x4010, 0x4020)");
}

TEST_F(VirtualMachineModelTest,
       BuildsBoundaryAdjacentRegionForConnectedCandidateHandlers) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *helper = llvm::Function::Create(handler_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *target = B.CreateLoad(i64_ty, slot_target);
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.CreateAdd(vip, B.getInt64(1)), slot_vip);
    B.CreateCall(dispatch_ty, dispatch, {state, target, helper->getArg(2)});
    B.CreateRetVoid();
  }

  auto *root = llvm::Function::Create(handler_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004600", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.getInt64(0x4010), slot_target);
    llvm::SmallVector<llvm::Value *, 12> boundary_args(12, B.getInt64(0));
    boundary_args[0] = vip;
    B.CreateCall(boundary_ty, boundary, boundary_args);
    B.CreateCall(handler_ty, helper, {state, root->getArg(1), root->getArg(2)});
    B.CreateRetVoid();
  }

  auto model = runAnalysis(*M);
  auto *region = model.lookupRegionForBoundary("vm_entry_180042ba4");
  ASSERT_NE(region, nullptr);
  EXPECT_EQ(region->boundary_names.size(), 1u);
  EXPECT_EQ(region->handler_names.size(), 2u);
  EXPECT_TRUE(std::find(region->handler_names.begin(), region->handler_names.end(),
                        "sub_180004600") != region->handler_names.end());
  EXPECT_TRUE(std::find(region->handler_names.begin(), region->handler_names.end(),
                        "sub_180004620") != region->handler_names.end());
  EXPECT_TRUE(std::find(region->entry_handler_names.begin(),
                        region->entry_handler_names.end(),
                        "sub_180004600") != region->entry_handler_names.end());
  ASSERT_GE(region->incoming_facts.size(), 1u);
  ASSERT_EQ(region->outgoing_facts.size(), 2u);
  auto target_fact = std::find_if(
      region->outgoing_facts.begin(), region->outgoing_facts.end(),
      [&](const omill::VirtualSlotFact &fact) {
        auto *slot = model.lookupSlot(fact.slot_id);
        return slot && slot->offset == 0x190;
      });
  ASSERT_NE(target_fact, region->outgoing_facts.end());
  EXPECT_EQ(omill::renderVirtualValueExpr(target_fact->value), "0x4010");
}

TEST_F(VirtualMachineModelTest,
       IncludesBoundaryAdjacentLiftedHelpersWithoutOwnDispatchInRegion) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_call", *M);

  auto *leaf = llvm::Function::Create(dispatch_ty,
                                      llvm::Function::ExternalLinkage,
                                      "blk_180004740", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    auto *state = leaf->getArg(0);
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    auto *loaded_target = B.CreateLoad(i64_ty, slot_target);
    llvm::SmallVector<llvm::Value *, 12> boundary_args(12, B.getInt64(0));
    boundary_args[0] = vip;
    B.CreateCall(boundary_ty, boundary, boundary_args);
    auto *call = B.CreateCall(dispatch, {state, loaded_target, leaf->getArg(2)});
    B.CreateRet(call);
  }

  auto *helper = llvm::Function::Create(dispatch_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180004720", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.CreateAdd(vip, B.getInt64(0x20)), slot_target);
    auto *call =
        B.CreateCall(dispatch_ty, leaf, {state, helper->getArg(1), helper->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(dispatch_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004700", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.CreateAdd(vip, B.getInt64(1)), slot_vip);
    auto *call =
        B.CreateCall(dispatch_ty, helper, {state, root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180004700");
  auto *helper_summary = model.lookupHandler("blk_180004720");
  auto *leaf_summary = model.lookupHandler("blk_180004740");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_NE(helper_summary, nullptr);
  ASSERT_NE(leaf_summary, nullptr);
  EXPECT_FALSE(root_summary->is_candidate);
  EXPECT_FALSE(helper_summary->is_candidate);
  EXPECT_TRUE(leaf_summary->is_candidate);

  auto *region = model.lookupRegionForBoundary("vm_entry_180042ba4");
  ASSERT_NE(region, nullptr);
  EXPECT_EQ(region->handler_names.size(), 3u);
  EXPECT_TRUE(std::find(region->handler_names.begin(), region->handler_names.end(),
                        "sub_180004700") != region->handler_names.end());
  EXPECT_TRUE(std::find(region->handler_names.begin(), region->handler_names.end(),
                        "blk_180004720") != region->handler_names.end());
  EXPECT_TRUE(std::find(region->handler_names.begin(), region->handler_names.end(),
                        "blk_180004740") != region->handler_names.end());
  EXPECT_TRUE(std::find(region->entry_handler_names.begin(),
                        region->entry_handler_names.end(),
                        "sub_180004700") != region->entry_handler_names.end());
  EXPECT_TRUE(std::find(region->exit_handler_names.begin(),
                        region->exit_handler_names.end(),
                        "blk_180004740") != region->exit_handler_names.end());
  EXPECT_EQ(region->internal_edges.size(), 2u);
}

TEST_F(VirtualMachineModelTest,
       SeedsRegionFromDispatchToProtectedBoundaryWithoutExplicitBoundaryCall) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_jump", *M);

  auto *handler_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty},
                                             false);
  auto *helper = llvm::Function::Create(handler_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180004820", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.CreateAdd(vip, B.getInt64(1)), slot_vip);
    B.CreateRetVoid();
  }

  auto *root = llvm::Function::Create(handler_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004800", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x180042BA4ULL), slot_target);
    B.CreateCall(handler_ty, helper, {state, root->getArg(1), root->getArg(2)});
    auto *loaded_target = B.CreateLoad(i64_ty, slot_target);
    B.CreateCall(dispatch_ty, dispatch,
                 {state, loaded_target, root->getArg(2)});
    B.CreateRetVoid();
  }

  omill::BinaryMemoryMap mem;
  uint8_t region[0x40] = {};
  region[0x00] = 0x68;
  region[0x05] = 0xE9;
  region[0x06] = 0x14;
  region[0x1E] = 0xE9;
  region[0x1F] = 0x0B;
  region[0x30] = 0xC3;
  mem.addRegion(0x180042BA4ULL, region, sizeof(region), /*read_only=*/true);

  auto model = runAnalysis(*M, std::move(mem));
  auto *region_summary = model.lookupRegionForBoundary("vm_entry_180042ba4");
  ASSERT_NE(region_summary, nullptr);
  EXPECT_EQ(region_summary->boundary_names.size(), 1u);
  EXPECT_EQ(region_summary->handler_names.size(), 2u);
  EXPECT_TRUE(std::find(region_summary->handler_names.begin(),
                        region_summary->handler_names.end(),
                        "sub_180004800") != region_summary->handler_names.end());
  EXPECT_TRUE(std::find(region_summary->handler_names.begin(),
                        region_summary->handler_names.end(),
                        "blk_180004820") != region_summary->handler_names.end());
  EXPECT_TRUE(std::find(region_summary->exit_handler_names.begin(),
                        region_summary->exit_handler_names.end(),
                        "sub_180004800") !=
              region_summary->exit_handler_names.end());
}

TEST_F(VirtualMachineModelTest,
       TreatsLiftedCallsiteDispatchBlockWithMinimalStateAsCandidate) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(dispatch_ty,
                                          llvm::Function::ExternalLinkage,
                                          "__omill_dispatch_call", *M);

  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *block = llvm::Function::Create(dispatch_ty,
                                       llvm::Function::ExternalLinkage,
                                       "blk_180026eb7", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", block);
    llvm::IRBuilder<> B(entry);
    auto *state = block->getArg(0);
    auto *pc_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x9A8));
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateStore(block->getArg(1), pc_slot);
    B.CreateCall(calli_ty, calli,
                 {block->getArg(2), state, B.getInt64(0x180026ec1), next_pc,
                  B.getInt64(0x180026ebc), return_pc});
    auto *dispatched =
        B.CreateCall(dispatch_ty, dispatch,
                     {state, B.getInt64(0x180026ec2), block->getArg(2)});
    B.CreateRet(dispatched);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("blk_180026eb7");
  ASSERT_NE(summary, nullptr);
  EXPECT_EQ(summary->dispatch_call_count, 1u);
  EXPECT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->is_candidate);
}

TEST_F(VirtualMachineModelTest,
       BuildsClosedRootSliceAcrossProtectedBoundaryContinuation) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");
  boundary->addFnAttr("omill.boundary_target_va", "180055365");

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *continued = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180055365", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continued);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continued->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180042BA4ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180001850");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().kind,
            omill::VirtualSuccessorKind::kProtectedBoundary);
  ASSERT_TRUE(root_summary->dispatches.front()
                  .successors.front()
                  .canonical_boundary_target_va.has_value());
  EXPECT_EQ(*root_summary->dispatches.front()
                 .successors.front()
                 .canonical_boundary_target_va,
            0x180055365ULL);

  auto *slice = model.lookupRootSlice(0x180001850ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_TRUE(std::find(slice->reachable_handler_names.begin(),
                        slice->reachable_handler_names.end(),
                        "sub_180001850") != slice->reachable_handler_names.end());
  EXPECT_TRUE(std::find(slice->reachable_handler_names.begin(),
                        slice->reachable_handler_names.end(),
                        "sub_180055365") != slice->reachable_handler_names.end());
  EXPECT_TRUE(slice->frontier_edges.empty());
}

TEST_F(VirtualMachineModelTest,
       LeavesRootSliceFrontierWhenBoundaryContinuationIsUnlifted) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");
  boundary->addFnAttr("omill.boundary_target_va", "180055365");

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180042BA4ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *slice = model.lookupRootSlice(0x180001850ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().reason, "boundary_target_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().canonical_target_va.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().canonical_target_va,
            0x180055365ULL);
  ASSERT_TRUE(slice->frontier_edges.front().boundary_name.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().boundary_name,
            "vm_entry_180042ba4");
}

TEST_F(VirtualMachineModelTest,
       TreatsNonExecutableBoundaryFrontierAsClosedTerminalSlice) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");
  boundary->addFnAttr("omill.boundary_target_va", "180055365");

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180042BA4ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *slice = model.lookupRootSlice(0x180001850ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().reason, "boundary_target_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().canonical_target_va.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().canonical_target_va,
            0x180055365ULL);
}

TEST_F(VirtualMachineModelTest,
       TreatsNonExecutableDispatchTargetAsClosedTerminalSlice) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180012000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0xDEADBEEFULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180012000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().kind,
            omill::VirtualSuccessorKind::kUnknown);

  auto *slice = model.lookupRootSlice(0x180012000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kDispatch);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "dispatch_target_not_executable");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0xDEADBEEFULL);
}

TEST_F(VirtualMachineModelTest,
       TreatsUndecodableDispatchTargetAsClosedTerminalSlice) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180012400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180012000ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x1000, 0x0F);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180012000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180012000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_180012400");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().kind,
            omill::VirtualSuccessorKind::kUnknown);

  auto *slice = model.lookupRootSlice(0x180012400ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kDispatch);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "dispatch_target_undecodable");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x180012000ULL);
}

TEST_F(VirtualMachineModelTest,
       MarksDecodableDispatchTargetAsUnliftedFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180012800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180012900ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  image[0x900] = 0x0F;
  image[0x901] = 0xBB;
  image[0x902] = 0xC0;
  image[0x903] = 0xC3;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180012000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180012000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *slice = model.lookupRootSlice(0x180012800ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kDispatch);
  EXPECT_EQ(slice->frontier_edges.front().reason, "dispatch_target_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x180012900ULL);
}

TEST_F(VirtualMachineModelTest,
       RecoversNearbyDispatchEntryAsCanonicalUnliftedFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180012c00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180012D05ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  image[0xD00] = 0x48;
  image[0xD01] = 0xF3;
  image[0xD02] = 0x73;
  image[0xD03] = 0x04;
  image[0xD04] = 0xFF;
  image[0xD05] = 0x17;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180012000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180012000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *slice = model.lookupRootSlice(0x180012C00ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kDispatch);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "dispatch_target_nearby_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x180012D05ULL);
  ASSERT_TRUE(slice->frontier_edges.front().canonical_target_va.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().canonical_target_va,
            0x180012D04ULL);
}

TEST_F(VirtualMachineModelTest,
       TraversesDirectLiftedCallChainsThroughNonCandidateBlocks) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *leaf = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "blk_180013020", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {leaf->getArg(0), B.getInt64(0xDEADBEEFULL),
                                leaf->getArg(2)});
    B.CreateRet(call);
  }

  auto *middle = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180013010", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", middle);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(leaf, {middle->getArg(0), middle->getArg(1),
                            middle->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180013000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(middle, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *slice = model.lookupRootSlice(0x180013000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_180013010"),
            slice->reachable_handler_names.end());
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_180013020"),
            slice->reachable_handler_names.end());
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kDispatch);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "dispatch_target_not_executable");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0xDEADBEEFULL);
}

TEST_F(VirtualMachineModelTest,
       ExcludesVmSemanticsHelpersFromRootSliceMembers) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *leaf = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "blk_180014020", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(leaf->getArg(0));
  }

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "helper_semantics", *M);
  helper->addFnAttr("omill.vm_handler");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(leaf, {helper->getArg(0), helper->getArg(1),
                            helper->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180014000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  EXPECT_NE(model.lookupHandler("helper_semantics"), nullptr);
  auto *slice = model.lookupRootSlice(0x180014000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_180014020"),
            slice->reachable_handler_names.end());
  EXPECT_EQ(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "helper_semantics"),
            slice->reachable_handler_names.end());
}

TEST_F(VirtualMachineModelTest,
       DoesNotSeedUnreferencedVmSemanticsHelpersIntoModel) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "helper_semantics_unused", *M);
  helper->addFnAttr("omill.vm_handler");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180014100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  EXPECT_EQ(model.lookupHandler("helper_semantics_unused"), nullptr);
  EXPECT_NE(model.lookupHandler("sub_180014100"), nullptr);
}

TEST_F(VirtualMachineModelTest,
       DoesNotSeedClosedSliceTaggedVmSemanticsHelpersIntoModel) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "helper_semantics_marked", *M);
  helper->addFnAttr("omill.vm_handler");
  helper->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180014180", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  EXPECT_EQ(model.lookupHandler("helper_semantics_marked"), nullptr);
  EXPECT_NE(model.lookupHandler("sub_180014180"), nullptr);
}

TEST_F(VirtualMachineModelTest,
       UsesClosedRootSliceScopeToLimitInitialModelSeeds) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *leaf = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "blk_180014220", *M);
  leaf->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(leaf->getArg(0));
  }

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "helper_semantics_scoped", *M);
  helper->addFnAttr("omill.vm_handler");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(leaf, {helper->getArg(0), helper->getArg(1),
                            helper->getArg(2)});
    B.CreateRet(call);
  }

  auto *unrelated = llvm::Function::Create(lifted_ty,
                                           llvm::Function::ExternalLinkage,
                                           "blk_1800142f0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", unrelated);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(unrelated->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180014200", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  EXPECT_NE(model.lookupHandler("sub_180014200"), nullptr);
  EXPECT_NE(model.lookupHandler("helper_semantics_scoped"), nullptr);
  EXPECT_NE(model.lookupHandler("blk_180014220"), nullptr);
  EXPECT_EQ(model.lookupHandler("blk_1800142f0"), nullptr);
}

TEST_F(VirtualMachineModelTest,
       TerminalBoundaryRecoverySeedsBoundedLocalCodeBearingRing) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *third = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                       "blk_1030", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", third);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(third->getArg(0));
  }

  auto *transitive = llvm::Function::Create(lifted_ty,
                                            llvm::Function::ExternalLinkage,
                                            "blk_1020", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", transitive);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(third, {transitive->getArg(0), transitive->getArg(1),
                                      transitive->getArg(2)});
    B.CreateRet(call);
  }

  auto *direct = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        "blk_1010", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", direct);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(transitive, {direct->getArg(0), direct->getArg(1),
                                  direct->getArg(2)});
    B.CreateRet(call);
  }

  auto *helper = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        "helper_recovery_bridge", *M);
  helper->addFnAttr("omill.vm_handler");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(direct, {helper->getArg(0), helper->getArg(1),
                              helper->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "blk_1000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  setEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA", "0x1000");
  setEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE", "2");
  auto model = runAnalysis(*M);
  unsetEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE");
  unsetEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA");

  EXPECT_NE(model.lookupHandler("blk_1000"), nullptr);
  EXPECT_NE(model.lookupHandler("helper_recovery_bridge"), nullptr);
  EXPECT_NE(model.lookupHandler("blk_1010"), nullptr);
  EXPECT_NE(model.lookupHandler("blk_1020"), nullptr);
  EXPECT_EQ(model.lookupHandler("blk_1030"), nullptr);
  EXPECT_EQ(model.lookupHandler("blk_1800142f0"), nullptr);
}

TEST_F(VirtualMachineModelTest,
       ClosedRootSliceScopeKeepsShortNestedHelperChains) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *leaf = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "blk_180014320", *M);
  leaf->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(leaf->getArg(0));
  }

  auto *helper_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "helper_semantics_b", *M);
  helper_b->addFnAttr("omill.vm_handler");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper_b);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(leaf, {helper_b->getArg(0), helper_b->getArg(1),
                            helper_b->getArg(2)});
    B.CreateRet(call);
  }

  auto *helper_a = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "helper_semantics_a", *M);
  helper_a->addFnAttr("omill.vm_handler");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper_a);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper_b, {helper_a->getArg(0), helper_a->getArg(1),
                                helper_a->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180014300", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(helper_a, {root->getArg(0), root->getArg(1),
                                         root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  EXPECT_NE(model.lookupHandler("helper_semantics_a"), nullptr);
  EXPECT_NE(model.lookupHandler("helper_semantics_b"), nullptr);
  EXPECT_NE(model.lookupHandler("blk_180014320"), nullptr);
}

TEST_F(VirtualMachineModelTest,
       TracksVmStackFactsAcrossHelperPushPopChain) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180009320", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_push_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), sp, push_helper->getArg(1)});
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_pop_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, pop_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {pop_helper->getArg(2), sp});
    B.CreateStore(value, pop_helper->getArg(1));
    B.CreateRet(pop_helper->getArg(2));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009300", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *stack_cell = B.CreateAlloca(i64_ty, nullptr, "vm_stack");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_cell, i64_ty), sp_slot);
    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x180009320ULL), root->getArg(2)});
    B.CreateCall(pop_ty, pop_helper,
                 {root->getArg(0), next_pc, root->getArg(2)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180009300");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x180009320ULL);
  EXPECT_FALSE(root_summary->outgoing_stack_facts.empty());
  EXPECT_TRUE(std::any_of(root_summary->outgoing_stack_facts.begin(),
                          root_summary->outgoing_stack_facts.end(),
                          [](const omill::VirtualStackFact &fact) {
                            return fact.value.constant.has_value() &&
                                   *fact.value.constant == 0x180009320ULL;
                          }));
}

TEST_F(VirtualMachineModelTest,
       RemapsHelperRelativeVmStackFactsIntoCallerLocalNextPc) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180009620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_push_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), sp, push_helper->getArg(1)});
    B.CreateRet(next_memory);
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_pop_vm_stack_arg1_state", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {helper->getArg(0), sp});
    B.CreateStore(value, helper->getArg(2));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009600", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(i64_ty, nullptr, "vm_stack");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(vm_stack, i64_ty), sp_slot);
    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x180009620ULL), root->getArg(2)});
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180009600");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x180009620ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
  EXPECT_TRUE(std::none_of(
      root_summary->outgoing_facts.begin(), root_summary->outgoing_facts.end(),
      [](const omill::VirtualSlotFact &fact) {
        return omill::renderVirtualValueExpr(fact.value).find("arg1+0x908") !=
               std::string::npos;
      }));
  EXPECT_TRUE(std::none_of(
      root_summary->outgoing_stack_facts.begin(),
      root_summary->outgoing_stack_facts.end(),
      [](const omill::VirtualStackFact &fact) {
        return omill::renderVirtualValueExpr(fact.value).find("arg1+0x908") !=
               std::string::npos;
      }));
}

TEST_F(VirtualMachineModelTest,
       ResolvesDispatchFromHelperMaskedLowByteReconstruction) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180008520", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180008500", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *vip_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x120));
    auto *target_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *vip = B.CreateLoad(i64_ty, vip_slot);
    auto *masked_high = B.CreateAnd(vip, B.getInt64(0xFFFFFFFFFFFFFF00ULL));
    auto *masked_low =
        B.CreateAnd(B.CreateZExt(B.CreateTrunc(vip, i8_ty), i64_ty),
                    B.getInt64(0xFF));
    B.CreateStore(B.CreateOr(masked_high, masked_low), target_slot);
    B.CreateRet(state);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_1800084f0", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *vip_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x120));
    auto *target_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x180008520ULL), vip_slot);
    B.CreateCall(helper, {state, root->getArg(1), root->getArg(2)});
    auto *loaded_target = B.CreateLoad(i64_ty, target_slot);
    auto *call = B.CreateCall(dispatch,
                              {state, loaded_target, root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_1800084f0");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);

  const auto &dispatch_summary = summary->dispatches.front();
  EXPECT_TRUE(dispatch_summary.unresolved_reason.empty())
      << dispatch_summary.unresolved_reason << " target="
      << omill::renderVirtualValueExpr(dispatch_summary.specialized_target);
  ASSERT_EQ(dispatch_summary.successors.size(), 1u);
  EXPECT_EQ(dispatch_summary.successors.front().target_pc, 0x180008520ULL);
}

TEST_F(VirtualMachineModelTest,
       ResolvesDispatchFromNestedMaskedPhiReconstruction) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target0 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_180061a0e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target0);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target0->getArg(0));
  }

  auto *target1 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18006a04d", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target1);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target1->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_18000f100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *then_bb = llvm::BasicBlock::Create(Ctx, "then", root);
    auto *else_bb = llvm::BasicBlock::Create(Ctx, "else", root);
    auto *merge_bb = llvm::BasicBlock::Create(Ctx, "merge", root);

    llvm::IRBuilder<> B(entry);
    auto *flag_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x811));
    auto *flag = B.CreateLoad(i8_ty, flag_slot);
    B.CreateCondBr(B.CreateICmpNE(flag, B.getInt8(0)), then_bb, else_bb);

    B.SetInsertPoint(then_bb);
    B.CreateBr(merge_bb);

    B.SetInsertPoint(else_bb);
    B.CreateBr(merge_bb);

    B.SetInsertPoint(merge_bb);
    auto *wide_phi = B.CreatePHI(i64_ty, 2);
    wide_phi->addIncoming(B.getInt64(0x18005C2F4ULL), then_bb);
    wide_phi->addIncoming(B.getInt64(0x180064933ULL), else_bb);
    auto *low8_phi = B.CreatePHI(i64_ty, 2);
    low8_phi->addIncoming(B.getInt64(0xF4), then_bb);
    low8_phi->addIncoming(B.getInt64(0x33), else_bb);
    auto *low16_phi = B.CreatePHI(i64_ty, 2);
    low16_phi->addIncoming(B.getInt64(0xC2F4), then_bb);
    low16_phi->addIncoming(B.getInt64(0x4933), else_bb);

    auto *inner = B.CreateOr(
        B.CreateAnd(wide_phi, B.getInt64(0xFFFFFFFFFFFFFF00ULL)),
        B.CreateAnd(low8_phi, B.getInt64(0xFF)));
    auto *outer = B.CreateOr(
        B.CreateAnd(inner, B.getInt64(0xFFFFFFFFFFFF0000ULL)),
        B.CreateAnd(low16_phi, B.getInt64(0xFFFF)));
    auto *target_pc = B.CreateAdd(outer, B.getInt64(0x571A));
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_18000f100");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  const auto &dispatch_summary = summary->dispatches.front();
  EXPECT_TRUE(dispatch_summary.unresolved_reason.empty())
      << dispatch_summary.unresolved_reason << " target="
      << omill::renderVirtualValueExpr(dispatch_summary.specialized_target);
  ASSERT_EQ(dispatch_summary.successors.size(), 2u);
  llvm::SmallVector<uint64_t, 2> targets;
  for (const auto &successor : dispatch_summary.successors)
    targets.push_back(successor.target_pc);
  llvm::sort(targets);
  EXPECT_EQ(targets[0], 0x180061A0EULL);
  EXPECT_EQ(targets[1], 0x18006A04DULL);
}

TEST_F(VirtualMachineModelTest,
       ResolvesDispatchFromHelperReadMemoryThroughAddressArgument) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180009920", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_load_vm_stack_addr_arg", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *value = B.CreateCall(
        read_mem, {helper->getArg(0), helper->getArg(2)});
    B.CreateStore(value, helper->getArg(1));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009900", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(i64_ty, nullptr, "vm_stack");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(vm_stack, i64_ty), sp_slot);
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *addr = B.CreateAdd(sp, B.getInt64(0x10));
    B.CreateCall(write_mem,
                 {root->getArg(2), addr, B.getInt64(0x180009920ULL)});
    B.CreateCall(helper, {root->getArg(2), next_pc, addr});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180009900");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x180009920ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       KeepsHelperReadMemorySextThroughStateSlotAddressCallerLocal) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i32_ty, {ptr_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_32",
      *M);

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_movsxd_addr_state_slot", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *value32 =
        B.CreateCall(read_mem, {helper->getArg(0), helper->getArg(3)});
    auto *value64 = B.CreateSExt(value32, i64_ty);
    B.CreateStore(value64, helper->getArg(2));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009940", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *addr_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8D8));
    auto *addr = B.CreateLoad(i64_ty, addr_slot);
    B.CreateCall(helper,
                 {root->getArg(2), root->getArg(0), next_pc, addr});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180009940");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);

  const auto rendered =
      omill::renderVirtualValueExpr(root_summary->dispatches.front().specialized_target);
  EXPECT_EQ(rendered.find("arg3"), std::string::npos);
  EXPECT_NE(rendered.find("arg0+0x8d8"), std::string::npos);
  EXPECT_TRUE(rendered.rfind("sext(", 0) == 0);
}

TEST_F(VirtualMachineModelTest,
       SpecializesHelperVmStackReadsThroughCallerSpDeltaFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_1800096A0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage,
      "helper_push_vm_stack_with_sp_decrement_addr_arg_chain", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    B.CreateStore(new_sp, sp_slot);
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), new_sp, push_helper->getArg(1)});
    B.CreateRet(next_memory);
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_pop_vm_stack_arg1_state", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {helper->getArg(0), sp});
    B.CreateStore(value, helper->getArg(2));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009680", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x1800096A0ULL), root->getArg(2)});
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180009680");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x1800096A0ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ResolvesVmStackReturnPcLoadedFromCallerAllocaThroughHelpers) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *call_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *jump_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000AB20", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *call_helper = llvm::Function::Create(
      call_ty, llvm::Function::ExternalLinkage, "helper_push_return_pc", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, call_helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory = B.CreateCall(
        write_mem, {call_helper->getArg(0), new_sp, call_helper->getArg(2)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateStore(call_helper->getArg(2), call_helper->getArg(3));
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_pop_vm_stack_to_tmp",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, pop_helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {pop_helper->getArg(0), sp});
    B.CreateStore(B.CreateAdd(sp, B.getInt64(8)), sp_slot);
    B.CreateStore(value, pop_helper->getArg(2));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *jump_helper = llvm::Function::Create(
      jump_ty, llvm::Function::ExternalLinkage, "helper_write_next_pc", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jump_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jump_helper->getArg(2), jump_helper->getArg(3));
    B.CreateRet(jump_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000AB00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    auto *tmp = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    B.CreateStore(B.getInt64(0x18000AB00ULL), return_pc);
    auto *loaded_return_pc = B.CreateLoad(i64_ty, return_pc);
    B.CreateCall(call_ty, call_helper,
                 {root->getArg(2), root->getArg(0), loaded_return_pc,
                  return_pc});
    B.CreateCall(pop_ty, pop_helper, {root->getArg(2), root->getArg(0), tmp});
    auto *loaded_tmp = B.CreateLoad(i64_ty, tmp);
    auto *target_pc = B.CreateAdd(loaded_tmp, B.getInt64(0x20));
    B.CreateCall(jump_ty, jump_helper,
                 {root->getArg(2), root->getArg(0), target_pc, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_18000AB00");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x18000AB20ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ResolvesVmStackLoadAfterRepeatedPushesThroughSpecializedAddressArgs) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 4);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);
  auto *load_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000AD20", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_push_vm_stack_qword",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot =
        B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), new_sp,
                                 push_helper->getArg(1)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateRet(next_memory);
  }

  auto *store_helper = llvm::Function::Create(
      store_ty, llvm::Function::ExternalLinkage, "helper_store_vm_stack_addr",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    auto *next_memory =
        B.CreateCall(write_mem, {store_helper->getArg(0), store_helper->getArg(1),
                                 store_helper->getArg(2)});
    B.CreateRet(next_memory);
  }

  auto *load_helper = llvm::Function::Create(
      load_ty, llvm::Function::ExternalLinkage, "helper_load_vm_stack_addr",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", load_helper);
    llvm::IRBuilder<> B(entry);
    auto *value =
        B.CreateCall(read_mem, {load_helper->getArg(0), load_helper->getArg(2)});
    B.CreateStore(value, load_helper->getArg(1));
    B.CreateRet(load_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000AD00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *entry_sp = B.CreateGEP(stack_array_ty, vm_stack,
                                 {B.getInt64(0), B.getInt64(2)});
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    auto *rax_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.CreatePtrToInt(entry_sp, i64_ty), sp_slot);

    auto *sp0 = B.CreateLoad(i64_ty, sp_slot);
    B.CreateCall(store_ty, store_helper,
                 {root->getArg(2), sp0, B.getInt64(0x18000AD20ULL)});
    B.CreateStore(B.getInt64(0x1111222233334444ULL), rax_slot);

    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x10101010ULL), root->getArg(2)});
    auto *sp1 = B.CreateLoad(i64_ty, sp_slot);
    auto *addr1 = B.CreateAdd(sp1, B.getInt64(16));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    B.CreateCall(store_ty, store_helper, {root->getArg(2), addr1, rax});

    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x20202020ULL), root->getArg(2)});
    auto *sp2 = B.CreateLoad(i64_ty, sp_slot);
    auto *addr2 = B.CreateAdd(sp2, B.getInt64(16));
    B.CreateCall(load_ty, load_helper, {root->getArg(2), next_pc, addr2});

    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_18000AD00");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x18000AD20ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ResolvesDispatchFromLiftedCallContinuationReturnAddress) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *remill_bb = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", remill_bb);
    llvm::IRBuilder<> B(entry);
    B.CreateGEP(i8_ty, remill_bb->getArg(0), B.getInt64(0x908), "RSP");
    B.CreateRet(remill_bb->getArg(2));
  }

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180010220", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation->getArg(0));
  }

  auto *trampoline = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", trampoline);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, trampoline->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *ret_pc = B.CreateCall(read_mem, {trampoline->getArg(2), sp});
    auto *target_pc = B.CreateAdd(ret_pc, B.getInt64(0x20));
    B.CreateStore(target_pc, next_pc);
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *next_memory = B.CreateCall(
        dispatch, {trampoline->getArg(0), loaded_next_pc, trampoline->getArg(2)});
    B.CreateRet(next_memory);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call_memory = B.CreateCall(
        lifted_ty, trampoline,
        {root->getArg(0), B.getInt64(0x180010100ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        lifted_ty, continuation,
        {root->getArg(0), B.getInt64(0x180010200ULL), call_memory});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  auto model = runAnalysis(*M);
  auto *trampoline_summary = model.lookupHandler("blk_180010100");
  ASSERT_NE(trampoline_summary, nullptr);
  ASSERT_EQ(trampoline_summary->dispatches.size(), 1u);
  ASSERT_EQ(trampoline_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(trampoline_summary->dispatches.front().successors.front().target_pc,
            0x180010220ULL);
  EXPECT_TRUE(trampoline_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ResolvesLeafHelperNextPcPerCallsiteWithoutCrossCallerPhiPollution) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180005002", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180006002", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_write_next_pc_plus_two", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *scratch = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAdd(helper->getArg(2), B.getInt64(2));
    B.CreateStore(next_pc, scratch);
    auto *reloaded_next_pc = B.CreateLoad(i64_ty, scratch);
    B.CreateStore(reloaded_next_pc, helper->getArg(3));
    B.CreateRet(helper->getArg(0));
  }

  auto make_root = [&](llvm::StringRef name, uint64_t target_pc) {
    auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        name, *M);
    root->addFnAttr("omill.output_root");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *call = B.CreateCall(
        helper, {root->getArg(2), root->getArg(0), B.getInt64(target_pc - 2),
                 next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, call});
    B.CreateRet(root->getArg(0));
    return root;
  };

  auto *root_a = make_root("sub_180008000", 0x180005002ULL);
  auto *root_b = make_root("sub_180008100", 0x180006002ULL);

  auto model = runAnalysis(*M);

  auto *summary_a = model.lookupHandler(root_a->getName());
  ASSERT_NE(summary_a, nullptr);
  ASSERT_EQ(summary_a->dispatches.size(), 1u);
  ASSERT_EQ(summary_a->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary_a->dispatches.front().successors.front().target_pc,
            0x180005002ULL);
  EXPECT_TRUE(summary_a->dispatches.front().unresolved_reason.empty());

  auto *summary_b = model.lookupHandler(root_b->getName());
  ASSERT_NE(summary_b, nullptr);
  ASSERT_EQ(summary_b->dispatches.size(), 1u);
  ASSERT_EQ(summary_b->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary_b->dispatches.front().successors.front().target_pc,
            0x180006002ULL);
  EXPECT_TRUE(summary_b->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ReplaysSequentialLeafHelperVmMemoryEffectsLocally) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180005120", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_push_then_pop_vm_stack_same_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {helper->getArg(0), new_sp, helper->getArg(3)});
    B.CreateStore(new_sp, sp_slot);
    auto *reloaded = B.CreateCall(read_mem, {helper->getArg(0), new_sp});
    B.CreateStore(reloaded, helper->getArg(2));
    B.CreateRet(next_memory);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180005100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), next_pc,
                          B.getInt64(0x180005120ULL)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180005100");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x180005120ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ReplaysSequentialSingleBlockHandlerHelperChainLocally) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *jmpi_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *read_mem_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  constexpr uint64_t kDelta = 0xF5DDULL;

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180005620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180006620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_chain_push_imm", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(1),
                                B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(0), new_sp,
                                 push_helper->getArg(2)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_chain_pop_to_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded =
        B.CreateCall(read_mem, {pop_helper->getArg(0), pop_helper->getArg(3)});
    B.CreateStore(loaded, pop_helper->getArg(2));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *store_helper = llvm::Function::Create(
      store_ty, llvm::Function::ExternalLinkage, "helper_chain_store_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(store_helper->getArg(3), store_helper->getArg(2));
    B.CreateRet(store_helper->getArg(0));
  }

  auto *jmpi_helper = llvm::Function::Create(
      jmpi_ty, llvm::Function::ExternalLinkage, "helper_chain_jmpi", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jmpi_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jmpi_helper->getArg(2), jmpi_helper->getArg(3));
    B.CreateRet(jmpi_helper->getArg(0));
  }

  auto make_root = [&](llvm::StringRef name, uint64_t target_pc) {
    auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        name, *M);
    root->addFnAttr("omill.output_root");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *tmp = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    auto *mem1 = B.CreateCall(push_helper, {root->getArg(2), root->getArg(0),
                                            B.getInt64(target_pc + kDelta)});
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *mem2 = B.CreateCall(pop_helper,
                              {mem1, root->getArg(0), tmp, sp});
    auto *loaded = B.CreateLoad(i64_ty, tmp);
    auto *adjusted = B.CreateAdd(loaded, B.getInt64(-static_cast<int64_t>(kDelta)));
    auto *mem3 = B.CreateCall(store_helper,
                              {mem2, root->getArg(0), tmp, adjusted});
    auto *resolved = B.CreateLoad(i64_ty, tmp);
    auto *mem4 = B.CreateCall(jmpi_helper,
                              {mem3, root->getArg(0), resolved, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, mem4});
    B.CreateRet(root->getArg(0));
    return root;
  };

  auto *root_a = make_root("sub_180005600", 0x180005620ULL);
  auto *root_b = make_root("sub_180006600", 0x180006620ULL);

  auto model = runAnalysis(*M);

  auto *summary_a = model.lookupHandler(root_a->getName());
  ASSERT_NE(summary_a, nullptr);
  ASSERT_EQ(summary_a->dispatches.size(), 1u);
  ASSERT_EQ(summary_a->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary_a->dispatches.front().successors.front().target_pc,
            0x180005620ULL);
  EXPECT_TRUE(summary_a->dispatches.front().unresolved_reason.empty());

  auto *summary_b = model.lookupHandler(root_b->getName());
  ASSERT_NE(summary_b, nullptr);
  ASSERT_EQ(summary_b->dispatches.size(), 1u);
  ASSERT_EQ(summary_b->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary_b->dispatches.front().successors.front().target_pc,
            0x180006620ULL);
  EXPECT_TRUE(summary_b->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       ReplaysSequentialLinearTwoBlockHandlerHelperChainLocally) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *jmpi_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *read_mem_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  constexpr uint64_t kDelta = 0xF5DDULL;

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180005820", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_two_block_push_imm", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(1),
                                B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(0), new_sp,
                                 push_helper->getArg(2)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_two_block_pop_to_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded =
        B.CreateCall(read_mem, {pop_helper->getArg(0), pop_helper->getArg(3)});
    B.CreateStore(loaded, pop_helper->getArg(2));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *store_helper = llvm::Function::Create(
      store_ty, llvm::Function::ExternalLinkage, "helper_two_block_store_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(store_helper->getArg(3), store_helper->getArg(2));
    B.CreateRet(store_helper->getArg(0));
  }

  auto *jmpi_helper = llvm::Function::Create(
      jmpi_ty, llvm::Function::ExternalLinkage, "helper_two_block_jmpi", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jmpi_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jmpi_helper->getArg(2), jmpi_helper->getArg(3));
    B.CreateRet(jmpi_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180005800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *tail = llvm::BasicBlock::Create(Ctx, "tail", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *tmp = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    auto *mem1 = B.CreateCall(push_helper, {root->getArg(2), root->getArg(0),
                                            B.getInt64(0x180005820ULL + kDelta)});
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *mem2 = B.CreateCall(pop_helper, {mem1, root->getArg(0), tmp, sp});
    auto *loaded = B.CreateLoad(i64_ty, tmp);
    auto *adjusted = B.CreateAdd(loaded, B.getInt64(-static_cast<int64_t>(kDelta)));
    B.CreateCall(store_helper, {mem2, root->getArg(0), tmp, adjusted});
    B.CreateBr(tail);

    B.SetInsertPoint(tail);
    auto *resolved = B.CreateLoad(i64_ty, tmp);
    auto *mem4 = B.CreateCall(jmpi_helper,
                              {root->getArg(2), root->getArg(0), resolved, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, mem4});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180005800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180005820ULL);
  EXPECT_TRUE(summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       FallsBackFromUnsupportedLeafHelperReplayToSummaryImport) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180005320", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_store_next_pc_with_dead_mul", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    (void) B.CreateMul(helper->getArg(2), B.getInt64(3), "dead_mul");
    B.CreateStore(helper->getArg(2), helper->getArg(1));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180005300", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    B.CreateCall(helper,
                 {root->getArg(2), next_pc, B.getInt64(0x180005320ULL)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180005300");
  ASSERT_NE(root_summary, nullptr);
  ASSERT_EQ(root_summary->dispatches.size(), 1u);
  ASSERT_EQ(root_summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(root_summary->dispatches.front().successors.front().target_pc,
            0x180005320ULL);
  EXPECT_TRUE(root_summary->dispatches.front().unresolved_reason.empty());
}

TEST_F(VirtualMachineModelTest,
       SeedsOutputRootProgramCounterIntoLocalStateFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8c8));
    auto *value = B.CreateAdd(root->getArg(1), B.getInt64(0x2970));
    B.CreateStore(value, slot);
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180001850");
  ASSERT_NE(root_summary, nullptr);
  EXPECT_TRUE(std::any_of(root_summary->outgoing_facts.begin(),
                          root_summary->outgoing_facts.end(),
                          [](const omill::VirtualSlotFact &fact) {
                            return fact.value.constant.has_value() &&
                                   *fact.value.constant == 0x1800041c0ULL;
                          }));
}

TEST_F(VirtualMachineModelTest,
       PreservesCallerConstantAgainstIdentityCalleeWriteback) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180002060", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x8c8));
    auto *value = B.CreateLoad(i64_ty, slot);
    B.CreateStore(value, slot);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8c8));
    B.CreateStore(B.getInt64(0x1800041c0ULL), slot);
    B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *root_summary = model.lookupHandler("sub_180001850");
  ASSERT_NE(root_summary, nullptr);
  EXPECT_TRUE(std::any_of(root_summary->outgoing_facts.begin(),
                          root_summary->outgoing_facts.end(),
                          [](const omill::VirtualSlotFact &fact) {
                            return fact.value.constant.has_value() &&
                                   *fact.value.constant == 0x1800041c0ULL;
                          }));
}

TEST_F(VirtualMachineModelTest,
       MapsCallerStateFactsIntoArgumentRelativeHelperLiveIns) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);

  auto *helper = llvm::Function::Create(helper_ty,
                                        llvm::Function::ExternalLinkage,
                                        "helper_arg_relative_state", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *src = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x8c8));
    auto *dst = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x978));
    auto *value = B.CreateLoad(i64_ty, src);
    B.CreateStore(value, dst);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8c8));
    B.CreateStore(B.getInt64(0x1800041c0ULL), slot);
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *helper_summary = model.lookupHandler("helper_arg_relative_state");
  ASSERT_NE(helper_summary, nullptr);
  EXPECT_TRUE(std::any_of(helper_summary->outgoing_facts.begin(),
                          helper_summary->outgoing_facts.end(),
                          [](const omill::VirtualSlotFact &fact) {
                            return fact.value.constant.has_value() &&
                                   *fact.value.constant == 0x1800041c0ULL;
                          }));
}

TEST_F(VirtualMachineModelTest, ResolvesRecursiveSlotAliasDispatchToConstant) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004600", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_y = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *slot_x = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x110));
    B.CreateStore(B.getInt64(0x180004620ULL), slot_y);
    auto *value_y = B.CreateLoad(i64_ty, slot_y);
    B.CreateStore(value_y, slot_x);
    auto *target_pc = B.CreateLoad(i64_ty, slot_x);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004600");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180004620ULL);
}

TEST_F(VirtualMachineModelTest, ResolvesAdditiveSlotAliasDispatchToConstant) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004720", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004700", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_y = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *slot_x = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x110));
    B.CreateStore(B.getInt64(0x180004700ULL), slot_y);
    auto *value_y = B.CreateLoad(i64_ty, slot_y);
    auto *value_x = B.CreateAdd(value_y, B.getInt64(0x20));
    B.CreateStore(value_x, slot_x);
    auto *target_pc = B.CreateLoad(i64_ty, slot_x);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004700");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180004720ULL);
}

TEST_F(VirtualMachineModelTest,
       ResolvesDispatchFromStructuralSlotFactFallback) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_1800047a0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004780", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_target = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    B.CreateStore(B.getInt64(0x1800047A0ULL), slot_target);
    auto *target_pc = B.CreateLoad(i64_ty, slot_target);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004780");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);

  auto &slots = model.mutableSlots();
  auto &handlers = model.mutableHandlers();
  auto handler_it = llvm::find_if(handlers, [](const omill::VirtualHandlerSummary &H) {
    return H.function_name == "sub_180004780";
  });
  ASSERT_NE(handler_it, handlers.end());
  ASSERT_FALSE(handler_it->outgoing_facts.empty());

  unsigned original_slot_id = handler_it->outgoing_facts.front().slot_id;
  auto slot_it = llvm::find_if(slots, [&](const omill::VirtualStateSlotInfo &slot) {
    return slot.id == original_slot_id;
  });
  ASSERT_NE(slot_it, slots.end());

  const unsigned duplicate_slot_id = 9001;
  slots.push_back(omill::VirtualStateSlotInfo{
      duplicate_slot_id, slot_it->base_name, slot_it->offset, slot_it->width,
      slot_it->from_argument, slot_it->from_alloca, slot_it->handler_names});
  handler_it->outgoing_facts.front().slot_id = duplicate_slot_id;
  handler_it->dispatches.front().successors.clear();
  handler_it->dispatches.front().unresolved_reason.clear();
  handler_it->dispatches.front().specialized_target =
      handler_it->dispatches.front().target;
  handler_it->dispatches.front().specialized_target_source =
      omill::VirtualDispatchResolutionSource::kUnknown;

  omill::virtual_model::detail::summarizeDispatchSuccessors(*M, model, {});

  summary = model.lookupHandler("sub_180004780");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x1800047A0ULL);
}

TEST_F(VirtualMachineModelTest,
       DiscoversImageBaseRelativeDispatchTargetsFromBinaryRegion) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target_a = llvm::Function::Create(lifted_ty,
                                          llvm::Function::ExternalLinkage,
                                          "sub_180001200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(lifted_ty,
                                          llvm::Function::ExternalLinkage,
                                          "sub_180001240", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *target_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8C8));
    auto *target_pc = B.CreateLoad(i64_ty, target_slot);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x1000, 0x90);
  image[0x000] = 0x40;
  image[0x001] = 0x8B;
  image[0x002] = 0x84;
  image[0x003] = 0x80;
  image[0x004] = 0x00;
  image[0x005] = 0x11;
  image[0x006] = 0x00;
  image[0x007] = 0x00;
  image[0x00A] = 0xFF;
  image[0x00B] = 0xE0;
  image[0x100] = 0x00;
  image[0x101] = 0x12;
  image[0x102] = 0x00;
  image[0x103] = 0x00;
  image[0x104] = 0x40;
  image[0x105] = 0x12;
  image[0x106] = 0x00;
  image[0x107] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(0x4000);
  map.addRegion(0x180001000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto discovered = omill::discoverImageBaseRelativeTargetsInRegion(
      map, map.imageBase(), 0x180001000ULL);
  ASSERT_EQ(discovered.size(), 2u);
  EXPECT_EQ(discovered[0], 0x180001200ULL);
  EXPECT_EQ(discovered[1], 0x180001240ULL);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_180001000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 2u);
  EXPECT_EQ(summary->dispatches.front().successors[0].target_pc,
            0x180001200ULL);
  EXPECT_EQ(summary->dispatches.front().successors[1].target_pc,
            0x180001240ULL);
}

TEST_F(VirtualMachineModelTest,
       PreservesHelperSlotAliasProvenanceAcrossArgumentRelativeWrite) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004820", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(helper_ty,
                                        llvm::Function::ExternalLinkage,
                                        "helper_slot_alias", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *src = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x108));
    auto *dst = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x110));
    auto *value = B.CreateLoad(i64_ty, src);
    B.CreateStore(value, dst);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *src = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *dst = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x110));
    B.CreateStore(B.getInt64(0x180004820ULL), src);
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), root->getArg(2)});
    auto *target_pc = B.CreateLoad(i64_ty, dst);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180004820ULL);
}

TEST_F(VirtualMachineModelTest,
       ImportsHelperByteWritesIntoOverlappingWideSlotLoads) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i8_ty}, false);
  auto *helper_jump_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180004A20", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *store_byte_helper = llvm::Function::Create(
      helper_store_ty, llvm::Function::ExternalLinkage,
      "helper_store_byte_slot", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_byte_helper);
    llvm::IRBuilder<> B(entry);
    auto *byte_slot =
        B.CreateGEP(i8_ty, store_byte_helper->getArg(1), B.getInt64(0x120));
    B.CreateStore(store_byte_helper->getArg(2), byte_slot);
    B.CreateRet(store_byte_helper->getArg(0));
  }

  auto *jump_helper = llvm::Function::Create(
      helper_jump_ty, llvm::Function::ExternalLinkage, "helper_write_next_pc",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jump_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jump_helper->getArg(2), jump_helper->getArg(3));
    B.CreateRet(jump_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004A00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *wide_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x120));
    B.CreateStore(B.getInt64(0x180004A00ULL), wide_slot);
    (void) B.CreateLoad(i8_ty, wide_slot);
    B.CreateCall(store_byte_helper,
                 {root->getArg(2), root->getArg(0), B.getInt8(0x20)});
    auto *target_pc = B.CreateLoad(i64_ty, wide_slot);
    B.CreateCall(jump_helper,
                 {root->getArg(2), root->getArg(0), target_pc, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004A00");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180004A20ULL);
}

TEST_F(VirtualMachineModelTest, ResolvesNextPcThroughRecursiveSlotAliases) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004920", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004900", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *slot_y = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *slot_x = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x110));
    B.CreateStore(B.getInt64(0x180004920ULL), slot_y);
    auto *value_y = B.CreateLoad(i64_ty, slot_y);
    B.CreateStore(value_y, slot_x);
    auto *value_x = B.CreateLoad(i64_ty, slot_x);
    B.CreateStore(value_x, next_pc);
    auto *target_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004900");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180004920ULL);
}

TEST_F(VirtualMachineModelTest,
       SummarizesConstantCallSiteAndImportedReturnFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *call_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_18000c080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, call_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x18000C160ULL), rax_slot);
    B.CreateRet(call_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000c000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000C080ULL), next_pc,
                         B.getInt64(0x18000C013ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x20000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000c000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);

  const auto &callsite = summary->callsites.front();
  EXPECT_TRUE(callsite.is_call);
  ASSERT_TRUE(callsite.resolved_target_pc.has_value());
  EXPECT_EQ(*callsite.resolved_target_pc, 0x18000C080ULL);
  ASSERT_TRUE(callsite.continuation_pc.has_value());
  EXPECT_EQ(*callsite.continuation_pc, 0x18000C013ULL);
  EXPECT_TRUE(callsite.is_executable_in_image);
  EXPECT_TRUE(callsite.is_decodable_entry);
  ASSERT_TRUE(callsite.target_function_name.has_value());
  EXPECT_EQ(*callsite.target_function_name, "sub_18000c080");
  EXPECT_TRUE(callsite.unresolved_reason.empty());

  bool saw_rax_return = std::any_of(
      callsite.return_slot_facts.begin(), callsite.return_slot_facts.end(),
      [&](const omill::VirtualSlotFact &fact) {
        auto *slot = model.lookupSlot(fact.slot_id);
        return slot && slot->offset == 0x8A8 &&
               omill::renderVirtualValueExpr(fact.value) == "0x18000c160";
      });
  EXPECT_TRUE(saw_rax_return);

  auto *slice = model.lookupRootSlice(0x18000C000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->frontier_edges.empty());
  EXPECT_TRUE(llvm::is_contained(slice->reachable_handler_names, "sub_18000c080"));
}

TEST_F(VirtualMachineModelTest,
       MarksOutOfImageCallSiteTargetAsCallFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0xDEADBEEFULL), next_pc,
                         B.getInt64(0x18000D013ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_out_of_image");

  auto *slice = model.lookupRootSlice(0x18000D000ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason, "call_target_out_of_image");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0xDEADBEEFULL);
}

TEST_F(VirtualMachineModelTest,
       MarksMappedNonExecutableCallSiteTargetAsCallFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000E080ULL), next_pc,
                         B.getInt64(0x18000D413ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> code(0x2000, 0x90);
  std::vector<uint8_t> data(0x2000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(0x20000);
  map.addRegion(0x180000000ULL, code.data(), code.size(), false,
                /*executable=*/true);
  map.addRegion(0x18000E000ULL, data.data(), data.size(), true,
                /*executable=*/false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d400");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_FALSE(summary->callsites.front().is_executable_in_image);
  EXPECT_FALSE(summary->callsites.front().is_decodable_entry);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_not_executable_in_image");

  auto *slice = model.lookupRootSlice(0x18000D400ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "call_target_not_executable_in_image");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000E080ULL);
}

TEST_F(VirtualMachineModelTest,
       MarksImportPointerCallSiteTargetAsTerminalCallFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  constexpr uint64_t kImportSlot = 0x18000E080ULL;

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d500", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(kImportSlot), next_pc,
                         B.getInt64(0x18000D513ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> code(0x2000, 0x90);
  std::vector<uint8_t> data(0x2000, 0x00);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(0x20000);
  map.addRegion(0x180000000ULL, code.data(), code.size(), false,
                /*executable=*/true);
  map.addRegion(0x18000E000ULL, data.data(), data.size(), true,
                /*executable=*/false);
  map.addImport(kImportSlot, "KERNEL32.dll", "CreateFileW");

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d500");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_import_pointer");

  auto *slice = model.lookupRootSlice(0x18000D500ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason, "call_target_import_pointer");
  EXPECT_TRUE(slice->is_closed);
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, kImportSlot);
  ASSERT_TRUE(slice->frontier_edges.front().boundary_name.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().boundary_name,
            "KERNEL32.dll!CreateFileW");
}

TEST_F(VirtualMachineModelTest,
       MarksInImageUndecodableCallSiteTargetAsCallFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000DFFFULL), next_pc,
                         B.getInt64(0x18000D813ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x1000, 0x90);
  std::fill(image.end() - 96, image.end(), 0x0F);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000D000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000D000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->callsites.front().is_executable_in_image);
  EXPECT_FALSE(summary->callsites.front().is_decodable_entry);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_undecodable");

  auto *slice = model.lookupRootSlice(0x18000D800ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason, "call_target_undecodable");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000DFFFULL);
}

TEST_F(VirtualMachineModelTest,
       RecoversNearbyCallSiteEntryAsCanonicalUnliftedFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000D105ULL), next_pc,
                         B.getInt64(0x18000D813ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x100] = 0x48;
  image[0x101] = 0xF3;
  image[0x102] = 0x73;
  image[0x103] = 0x04;
  image[0x104] = 0xFF;
  image[0x105] = 0x17;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000D000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000D000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->callsites.front().is_executable_in_image);
  EXPECT_FALSE(summary->callsites.front().is_decodable_entry);
  ASSERT_TRUE(summary->callsites.front().recovered_entry_pc.has_value());
  EXPECT_EQ(*summary->callsites.front().recovered_entry_pc, 0x18000D104ULL);
  EXPECT_FALSE(summary->callsites.front().target_function_name.has_value());
  EXPECT_FALSE(
      summary->callsites.front().recovered_target_function_name.has_value());
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_nearby_unlifted");

  auto *slice = model.lookupRootSlice(0x18000D800ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "call_target_nearby_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000D105ULL);
  ASSERT_TRUE(slice->frontier_edges.front().canonical_target_va.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().canonical_target_va,
            0x18000D104ULL);
}

TEST_F(VirtualMachineModelTest,
       RecoversNearbyCallSiteEntryAsReachableMidInstructionTarget) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);
  auto *nearby_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000d100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", nearby_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(nearby_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000D105ULL), next_pc,
                         B.getInt64(0x18000D813ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x100] = 0x48;
  image[0x101] = 0xF3;
  image[0x102] = 0x73;
  image[0x103] = 0x04;
  image[0x104] = 0xFF;
  image[0x105] = 0x17;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000D000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000D000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->callsites.front().is_executable_in_image);
  EXPECT_FALSE(summary->callsites.front().is_decodable_entry);
  ASSERT_TRUE(summary->callsites.front().recovered_entry_pc.has_value());
  EXPECT_EQ(*summary->callsites.front().recovered_entry_pc, 0x18000D100ULL);
  ASSERT_TRUE(
      summary->callsites.front().recovered_target_function_name.has_value());
  EXPECT_EQ(*summary->callsites.front().recovered_target_function_name,
            "blk_18000d100");
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_mid_instruction");

  auto *slice = model.lookupRootSlice(0x18000D800ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_18000d100"),
            slice->reachable_handler_names.end());
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "call_target_mid_instruction");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000D105ULL);
  ASSERT_TRUE(slice->frontier_edges.front().canonical_target_va.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().canonical_target_va,
            0x18000D100ULL);
}

TEST_F(VirtualMachineModelTest,
       RecoversNearbyLiftedCallSiteEntryEvenWhenRawTargetIsDecodable) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);
  auto *nearby_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000e0fc", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", nearby_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(nearby_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000E100ULL), next_pc,
                         B.getInt64(0x18000E813ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  image[0x100] = 0x0F;
  image[0x101] = 0xBB;
  image[0x102] = 0xC0;
  image[0x103] = 0xC3;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000E000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000E000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000e800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->callsites.front().is_executable_in_image);
  EXPECT_TRUE(summary->callsites.front().is_decodable_entry);
  ASSERT_TRUE(summary->callsites.front().recovered_entry_pc.has_value());
  EXPECT_EQ(*summary->callsites.front().recovered_entry_pc, 0x18000E0FCULL);
  ASSERT_TRUE(
      summary->callsites.front().recovered_target_function_name.has_value());
  EXPECT_EQ(*summary->callsites.front().recovered_target_function_name,
            "blk_18000e0fc");
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_mid_instruction");

  auto *slice = model.lookupRootSlice(0x18000E800ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_18000e0fc"),
            slice->reachable_handler_names.end());
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason,
            "call_target_mid_instruction");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000E100ULL);
  ASSERT_TRUE(slice->frontier_edges.front().canonical_target_va.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().canonical_target_va,
            0x18000E0FCULL);
}

TEST_F(VirtualMachineModelTest,
       MarksDecodableBtcCallSiteTargetAsUnliftedFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000E100ULL), next_pc,
                         B.getInt64(0x18000E013ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  image[0x100] = 0x0F;
  image[0x101] = 0xBB;
  image[0x102] = 0xC0;
  image[0x103] = 0xC3;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000E000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000E000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000e000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->callsites.front().is_executable_in_image);
  EXPECT_TRUE(summary->callsites.front().is_decodable_entry);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_unlifted");

  auto *slice = model.lookupRootSlice(0x18000E000ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason, "call_target_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000E100ULL);
}

TEST_F(VirtualMachineModelTest,
       MarksDecodableRolCallSiteTargetAsUnliftedFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000E480ULL), next_pc,
                         B.getInt64(0x18000E413ULL), return_pc});
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x1000, 0x90);
  image[0x480] = 0xD0;
  image[0x481] = 0xC1;
  image[0x482] = 0xFE;
  image[0x483] = 0xC1;
  image[0x484] = 0xC3;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000E000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000E000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000e400");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_TRUE(summary->callsites.front().is_executable_in_image);
  EXPECT_TRUE(summary->callsites.front().is_decodable_entry);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_unlifted");

  auto *slice = model.lookupRootSlice(0x18000E400ULL);
  ASSERT_NE(slice, nullptr);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason, "call_target_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000E480ULL);
}

TEST_F(VirtualMachineModelTest,
       IgnoresLocalizedNonExecutableCallSiteForRootSliceClosure) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);
  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000e013", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000E100ULL), next_pc,
                         B.getInt64(0x18000E013ULL), return_pc});
    auto *tail = B.CreateCall(continuation, {root->getArg(0),
                                             B.getInt64(0x18000E013ULL),
                                             root->getArg(2)});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000E000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000E000ULL, image.data(), image.size(), false,
                /*executable=*/false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000e000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_not_executable_in_image");

  auto *slice = model.lookupRootSlice(0x18000E000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_TRUE(slice->frontier_edges.empty());
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_18000e013"),
            slice->reachable_handler_names.end());
}

TEST_F(VirtualMachineModelTest,
       IgnoresSameHandlerLocalizedNonExecutableCallSiteForRootSliceClosure) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000f000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000F100ULL), next_pc,
                         B.getInt64(0x18000F013ULL), return_pc});
    auto *saved_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *state_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(saved_return_pc, state_slot);
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000F000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000F000ULL, image.data(), image.size(), false,
                /*executable=*/false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000f000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_not_executable_in_image");

  bool saw_return_pc_fact = std::any_of(
      summary->outgoing_facts.begin(), summary->outgoing_facts.end(),
      [&](const omill::VirtualSlotFact &fact) {
        return omill::renderVirtualValueExpr(fact.value) == "slot(RETURN_PC+0x0)";
      });
  EXPECT_TRUE(saw_return_pc_fact);

  auto *slice = model.lookupRootSlice(0x18000F000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_TRUE(slice->frontier_edges.empty());
}

TEST_F(VirtualMachineModelTest,
       IgnoresLocalizedImportPointerCallSiteForRootSliceClosure) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  constexpr uint64_t kImportSlot = 0x180010100ULL;

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e600", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(kImportSlot), next_pc,
                         B.getInt64(0x18000E613ULL), return_pc});
    auto *saved_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *state_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(saved_return_pc, state_slot);
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> code(0x2000, 0x90);
  std::vector<uint8_t> data(0x2000, 0x00);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000E000ULL);
  map.setImageSize(0x4000);
  map.addRegion(0x18000E000ULL, code.data(), code.size(), false,
                /*executable=*/true);
  map.addRegion(0x180010000ULL, data.data(), data.size(), true,
                /*executable=*/false);
  map.addImport(kImportSlot, "KERNEL32.dll", "CreateFileW");

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000e600");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_import_pointer");

  auto *slice = model.lookupRootSlice(0x18000E600ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_TRUE(slice->frontier_edges.empty());
}

TEST_F(VirtualMachineModelTest,
       IgnoresLocalizedMidInstructionCallSiteForRootSliceClosure) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);
  auto *nearby_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000d100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", nearby_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(nearby_target->getArg(0));
  }
  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000d813", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d800", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000D105ULL), next_pc,
                         B.getInt64(0x18000D813ULL), return_pc});
    auto *tail = B.CreateCall(continuation, {root->getArg(0),
                                             B.getInt64(0x18000D813ULL),
                                             root->getArg(2)});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x1000, 0x90);
  image[0x100] = 0x48;
  image[0x101] = 0xF3;
  image[0x102] = 0x73;
  image[0x103] = 0x04;
  image[0x104] = 0xFF;
  image[0x105] = 0x17;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000D000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000D000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_18000d800");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_mid_instruction");
  ASSERT_TRUE(summary->callsites.front().recovered_target_function_name.has_value());
  EXPECT_EQ(*summary->callsites.front().recovered_target_function_name,
            "blk_18000d100");

  auto *slice = model.lookupRootSlice(0x18000D800ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
  EXPECT_TRUE(slice->frontier_edges.empty());
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_18000d100"),
            slice->reachable_handler_names.end());
  EXPECT_NE(std::find(slice->reachable_handler_names.begin(),
                      slice->reachable_handler_names.end(), "blk_18000d813"),
            slice->reachable_handler_names.end());
}

TEST_F(VirtualMachineModelTest,
       RecoveryModeKeepsExecutableUnliftedLocalizedCallSiteAsFrontier) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);
  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000f013", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000f000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000F100ULL), next_pc,
                         B.getInt64(0x18000F013ULL), return_pc});
    auto *tail = B.CreateCall(continuation, {root->getArg(0),
                                             B.getInt64(0x18000F013ULL),
                                             root->getArg(2)});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  image[0x100] = 0x48;
  image[0x101] = 0x31;
  image[0x102] = 0xC0;
  image[0x103] = 0xC3;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000F000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000F000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  setEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA", "0x18000F000");
  auto model = runAnalysis(*M, std::move(map));
  unsetEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA");

  auto *summary = model.lookupHandler("sub_18000f000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);
  EXPECT_EQ(summary->callsites.front().unresolved_reason,
            "call_target_unlifted");

  auto *slice = model.lookupRootSlice(0x18000F000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().kind,
            omill::VirtualRootFrontierKind::kCall);
  EXPECT_EQ(slice->frontier_edges.front().reason, "call_target_unlifted");
  ASSERT_TRUE(slice->frontier_edges.front().target_pc.has_value());
  EXPECT_EQ(*slice->frontier_edges.front().target_pc, 0x18000F100ULL);
}

TEST_F(VirtualMachineModelTest,
       InfersHelperCallContinuationAndReturnPcSeededTarget) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *call_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(call_target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010013", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation->getArg(2));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    auto *seeded_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *seeded_target = B.CreateAdd(seeded_return_pc, B.getInt64(0x6D));
    B.CreateStore(seeded_target, next_pc);
    auto *target_pc = B.CreateLoad(i64_ty, next_pc);
    auto *helper_return_pc = B.CreateLoad(i64_ty, return_pc);
    B.CreateCall(calli, {root->getArg(2), root->getArg(0), target_pc, next_pc,
                         helper_return_pc, return_pc});
    auto *call_result = B.CreateCall(
        call_target,
        {root->getArg(0), B.getInt64(0x180010080ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x180010013ULL), call_result});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x40000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_180010000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);

  const auto &callsite = summary->callsites.front();
  ASSERT_TRUE(callsite.resolved_target_pc.has_value());
  EXPECT_EQ(*callsite.resolved_target_pc, 0x180010080ULL);
  ASSERT_TRUE(callsite.continuation_pc.has_value());
  EXPECT_EQ(*callsite.continuation_pc, 0x180010013ULL);
}

TEST_F(VirtualMachineModelTest,
       PrefersOutgoingNextPcAnchoredToReturnPcForCallSiteTarget) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *call_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180020080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, call_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x180020160ULL), rax_slot);
    B.CreateRet(call_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180020000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");

    B.CreateStore(B.getInt64(0xFFFF000000000000ULL), next_pc);
    auto *bad_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *bad_target = B.CreateAdd(bad_next_pc, B.getInt64(0x6D));
    B.CreateCall(calli, {root->getArg(2), root->getArg(0), bad_target, next_pc,
                         B.getInt64(0x180020013ULL), return_pc});

    auto *seeded_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *good_next_pc = B.CreateAdd(seeded_return_pc, B.getInt64(0x6D));
    B.CreateStore(good_next_pc, next_pc);
    B.CreateRet(root->getArg(0));
  }

  std::vector<uint8_t> image(0x40000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("sub_180020000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->callsites.size(), 1u);

  const auto &callsite = summary->callsites.front();
  EXPECT_TRUE(callsite.is_call);
  ASSERT_TRUE(callsite.resolved_target_pc.has_value());
  EXPECT_EQ(*callsite.resolved_target_pc, 0x180020080ULL);
  ASSERT_TRUE(callsite.continuation_pc.has_value());
  EXPECT_EQ(*callsite.continuation_pc, 0x180020013ULL);
  EXPECT_TRUE(callsite.is_executable_in_image);
  EXPECT_TRUE(callsite.is_decodable_entry);
  ASSERT_TRUE(callsite.target_function_name.has_value());
  EXPECT_EQ(*callsite.target_function_name, "sub_180020080");
  EXPECT_EQ(callsite.specialized_target_source,
            omill::VirtualDispatchResolutionSource::kOutgoingFacts);
  EXPECT_EQ(omill::renderVirtualValueExpr(callsite.specialized_target),
            "add(slot(RETURN_PC+0x0), 0x6d)");
  EXPECT_NE(callsite.unresolved_reason, "call_target_unresolved");
  EXPECT_NE(callsite.unresolved_reason, "call_target_not_executable_in_image");
}

TEST_F(VirtualMachineModelTest,
       AddsPreludeDirectCallTargetAsRootSliceFrontier) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, llvm::Type::getInt64Ty(Ctx), ptr_ty},
                                            false);

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(mid->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *slice = model.lookupRootSlice(0x180010000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  auto it = std::find_if(
      slice->frontier_edges.begin(), slice->frontier_edges.end(),
      [](const omill::VirtualRootSliceSummary::FrontierEdge &edge) {
        return edge.kind == omill::VirtualRootFrontierKind::kCall &&
               edge.reason == "call_target_unlifted" &&
               edge.target_pc.has_value() &&
               *edge.target_pc == 0x180010080ULL;
      });
  EXPECT_NE(it, slice->frontier_edges.end());
}

TEST_F(VirtualMachineModelTest,
       SkipsPreludeDirectCallFrontierWhenSemanticallyLocalized) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *localized_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010120", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", localized_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(localized_target->getArg(0));
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateStore(B.getInt64(0x18001000EULL), return_pc);
    auto *call =
        B.CreateCall(localized_target, {mid->getArg(0), B.getInt64(0x180010120ULL),
                                        mid->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *slice = model.lookupRootSlice(0x180010000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->frontier_edges.empty());
  EXPECT_TRUE(slice->is_closed);
}

TEST_F(VirtualMachineModelTest,
       MarksUndecodablePreludeDirectCallTargetAsRootSliceFrontier) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, llvm::Type::getInt64Ty(Ctx), ptr_ty},
                              false);

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001100e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(mid->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180011000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(mid, {root->getArg(0), root->getArg(1),
                                    root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x1000, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0xF1;
  image[0x0B] = 0x0F;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;
  std::fill(image.end() - 16, image.end(), 0x0F);

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180011000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180011000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *slice = model.lookupRootSlice(0x180011000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  auto it = std::find_if(
      slice->frontier_edges.begin(), slice->frontier_edges.end(),
      [](const omill::VirtualRootSliceSummary::FrontierEdge &edge) {
        return edge.kind == omill::VirtualRootFrontierKind::kCall &&
               (edge.reason == "call_target_undecodable" ||
                edge.reason == "call_target_nearby_unlifted") &&
               edge.target_pc.has_value() &&
               *edge.target_pc == 0x180011FFFULL;
      });
  EXPECT_NE(it, slice->frontier_edges.end());
}

TEST_F(VirtualMachineModelTest,
       SeedsMidBlockEntryFromPreludeDirectCallReturnFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *prelude_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", prelude_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, prelude_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x1800106DDULL), rax_slot);
    B.CreateRet(prelude_target->getArg(0));
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, mid->getArg(0), B.getInt64(0x8A8));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(rax, B.getInt64(0x5DDULL));
    auto *call = B.CreateCall(dispatch, {mid->getArg(0), target_pc, mid->getArg(2)});
    B.CreateRet(call);
  }

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("blk_18001000e");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->incoming_facts.size() > 0, true);

  bool saw_rax_seed = std::any_of(
      summary->incoming_facts.begin(), summary->incoming_facts.end(),
      [&](const omill::VirtualSlotFact &fact) {
        auto *slot = model.lookupSlot(fact.slot_id);
        return slot && slot->offset == 0x8A8 &&
               omill::renderVirtualValueExpr(fact.value) == "0x1800106dd";
      });
  EXPECT_TRUE(saw_rax_seed);

  const auto &dispatch_summary = summary->dispatches.front();
  ASSERT_EQ(dispatch_summary.successors.size(), 1u);
  EXPECT_EQ(dispatch_summary.successors.front().target_pc, 0x180010100ULL);

  auto *slice = model.lookupRootSlice(0x180010000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
}

TEST_F(VirtualMachineModelTest,
       ResolvesPreludeTargetDispatchFromPredecessorLocalizedFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *prelude_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", prelude_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, prelude_target->getArg(0), B.getInt64(0x8A8));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(rax, B.getInt64(0x5DDULL));
    auto *call = B.CreateCall(
        dispatch, {prelude_target->getArg(0), target_pc, prelude_target->getArg(2)});
    B.CreateRet(call);
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, mid->getArg(0), B.getInt64(0x8A8));
    (void) B.CreateLoad(i64_ty, rax_slot);
    B.CreateRet(mid->getArg(0));
  }

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x1800106DDULL), rax_slot);
    auto *call =
        B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("blk_180010080");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  const auto &dispatch_summary = summary->dispatches.front();
  EXPECT_EQ(dispatch_summary.specialized_target_source,
            omill::VirtualDispatchResolutionSource::kPreludeLocalization);
  ASSERT_EQ(dispatch_summary.successors.size(), 1u);
  EXPECT_EQ(dispatch_summary.successors.front().target_pc, 0x180010100ULL);

  auto *slice = model.lookupRootSlice(0x180010000ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_TRUE(slice->is_closed);
}

TEST_F(VirtualMachineModelTest,
       SeedsMidBlockEntryFromPreludeNestedCallSiteReturnFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *inner_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_1800100c0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", inner_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, inner_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x1800106DDULL), rax_slot);
    B.CreateRet(inner_target->getArg(0));
  }

  auto *inner_cont = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010093", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", inner_cont);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(inner_cont->getArg(0));
  }

  auto *prelude_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", prelude_target);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {prelude_target->getArg(2), prelude_target->getArg(0),
                         B.getInt64(0x1800100C0ULL), next_pc,
                         B.getInt64(0x180010093ULL), return_pc});
    auto *call_result = B.CreateCall(
        inner_target,
        {prelude_target->getArg(0), B.getInt64(0x1800100C0ULL),
         prelude_target->getArg(2)});
    auto *tail = B.CreateCall(
        inner_cont,
        {prelude_target->getArg(0), B.getInt64(0x180010093ULL), call_result});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, mid->getArg(0), B.getInt64(0x8A8));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(rax, B.getInt64(0x5DDULL));
    auto *call = B.CreateCall(dispatch, {mid->getArg(0), target_pc, mid->getArg(2)});
    B.CreateRet(call);
  }

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x300, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  auto model = runAnalysis(*M, std::move(map));
  auto *summary = model.lookupHandler("blk_18001000e");
  ASSERT_NE(summary, nullptr);

  bool saw_rax_seed = std::any_of(
      summary->incoming_facts.begin(), summary->incoming_facts.end(),
      [&](const omill::VirtualSlotFact &fact) {
        auto *slot = model.lookupSlot(fact.slot_id);
        return slot && slot->offset == 0x8A8 &&
               omill::renderVirtualValueExpr(fact.value) == "0x1800106dd";
      });
  EXPECT_TRUE(saw_rax_seed);

  ASSERT_EQ(summary->dispatches.size(), 1u);
  ASSERT_EQ(summary->dispatches.front().successors.size(), 1u);
  EXPECT_EQ(summary->dispatches.front().successors.front().target_pc,
            0x180010100ULL);
}

TEST_F(VirtualMachineModelTest,
       MarksUnsupportedSlotProvenanceTargetAsOpenFrontier) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180004a00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_y = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *value_y = B.CreateLoad(i64_ty, slot_y);
    auto *value_x = B.CreateXor(value_y, B.getInt64(0x20));
    B.CreateCall(dispatch, {root->getArg(0), value_x, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_180004a00");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  EXPECT_TRUE(summary->dispatches.front().successors.empty());
  EXPECT_EQ(summary->dispatches.front().unresolved_reason,
            "unsupported_slot_provenance_target");
  EXPECT_EQ(omill::renderVirtualValueExpr(
                summary->dispatches.front().specialized_target),
            "xor(slot(arg0+0x108), 0x20)");
}

TEST_F(VirtualMachineModelTest,
       MarksUnsupportedVmStackOffsetsAsOpenFrontier) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_pop_dynamic_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *state = pop_helper->getArg(0);
    auto *sp_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x908));
    auto *delta_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x910));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *delta = B.CreateLoad(i64_ty, delta_slot);
    auto *addr = B.CreateAdd(sp, delta);
    auto *sp_ptr = B.CreateIntToPtr(addr, ptr_ty);
    auto *value = B.CreateLoad(i64_ty, sp_ptr);
    B.CreateStore(value, pop_helper->getArg(1));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    B.CreateCall(pop_ty, pop_helper, {root->getArg(0), next_pc, root->getArg(2)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  auto model = runAnalysis(*M);
  auto *slice = model.lookupRootSlice(0x180009400ULL);
  ASSERT_NE(slice, nullptr);
  EXPECT_FALSE(slice->is_closed);
  ASSERT_EQ(slice->frontier_edges.size(), 1u);
  EXPECT_EQ(slice->frontier_edges.front().reason, "unsupported_memory_target");
}

TEST_F(VirtualMachineModelTest,
       ResolvesBooleanFlagSlotDispatchToFiniteSuccessors) {
  auto M = createModule();
  addMinimalX86FlagStateTypes(*M);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target0 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000c000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target0);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target0->getArg(0));
  }

  auto *target1 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000c001", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target1);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target1->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000b000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *cf_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x811));
    auto *cf = B.CreateLoad(i8_ty, cf_slot);
    auto *cf64 = B.CreateZExt(cf, i64_ty);
    auto *target_pc = B.CreateAdd(B.getInt64(0x18000C000ULL), cf64);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  omill::StateFieldMap field_map(*M);
  auto field = field_map.fieldAtOffset(0x811);
  ASSERT_TRUE(field.has_value());
  EXPECT_EQ(field->category, omill::StateFieldCategory::kFlag);
  auto *summary = model.lookupHandler("sub_18000b000");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);

  const auto &dispatch_summary = summary->dispatches.front();
  EXPECT_TRUE(dispatch_summary.unresolved_reason.empty())
      << dispatch_summary.unresolved_reason << " target="
      << omill::renderVirtualValueExpr(dispatch_summary.specialized_target);
  ASSERT_EQ(dispatch_summary.successors.size(), 2u);
  llvm::SmallVector<uint64_t, 2> targets;
  for (const auto &successor : dispatch_summary.successors)
    targets.push_back(successor.target_pc);
  llvm::sort(targets);
  EXPECT_EQ(targets[0], 0x18000C000ULL);
  EXPECT_EQ(targets[1], 0x18000C001ULL);
}

TEST_F(VirtualMachineModelTest,
       ResolvesSingleBitMaskedSlotDispatchToFiniteSuccessors) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target0 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000d200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target0);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target0->getArg(0));
  }

  auto *target1 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000d201", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target1);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target1->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_18000d100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8F8));
    auto *value = B.CreateLoad(i64_ty, slot);
    auto *shifted = B.CreateLShr(value, B.getInt64(62));
    auto *bit = B.CreateAnd(B.CreateTrunc(shifted, i8_ty), B.getInt8(1));
    auto *bit64 = B.CreateZExt(bit, i64_ty);
    auto *target_pc = B.CreateAdd(B.getInt64(0x18000D200ULL), bit64);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_18000d100");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);

  const auto &dispatch_summary = summary->dispatches.front();
  EXPECT_TRUE(dispatch_summary.unresolved_reason.empty())
      << dispatch_summary.unresolved_reason << " target="
      << omill::renderVirtualValueExpr(dispatch_summary.specialized_target);
  ASSERT_EQ(dispatch_summary.successors.size(), 2u);
  llvm::SmallVector<uint64_t, 2> targets;
  for (const auto &successor : dispatch_summary.successors)
    targets.push_back(successor.target_pc);
  llvm::sort(targets);
  EXPECT_EQ(targets[0], 0x18000D200ULL);
  EXPECT_EQ(targets[1], 0x18000D201ULL);
}

TEST_F(VirtualMachineModelTest,
       RecoversNearbyLiftedEntryForDispatchSuccessor) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000e140", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_18000e100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch, {root->getArg(0),
                                         B.getInt64(0x18000E145ULL),
                                         root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_18000e100");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  const auto &dispatch_summary = summary->dispatches.front();
  ASSERT_EQ(dispatch_summary.successors.size(), 1u);
  EXPECT_EQ(dispatch_summary.successors.front().target_pc, 0x18000E140ULL);
  ASSERT_TRUE(dispatch_summary.successors.front().target_function_name.has_value());
  EXPECT_EQ(*dispatch_summary.successors.front().target_function_name,
            "blk_18000e140");
}

TEST_F(VirtualMachineModelTest,
       RecoversForwardNearbyLiftedEntryForDispatchSuccessor) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000e348", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_18000e300", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch, {root->getArg(0),
                                         B.getInt64(0x18000E345ULL),
                                         root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_18000e300");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  const auto &dispatch_summary = summary->dispatches.front();
  ASSERT_EQ(dispatch_summary.successors.size(), 1u);
  EXPECT_EQ(dispatch_summary.successors.front().target_pc, 0x18000E348ULL);
  ASSERT_TRUE(dispatch_summary.successors.front().target_function_name.has_value());
  EXPECT_EQ(*dispatch_summary.successors.front().target_function_name,
            "blk_18000e348");
}

TEST_F(VirtualMachineModelTest,
       RecoversDispatchSuccessorWithinExtendedNearbyWindow) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000e340", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_18000e300", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch, {root->getArg(0),
                                         B.getInt64(0x18000E35BULL),
                                         root->getArg(2)});
    B.CreateRet(call);
  }

  auto model = runAnalysis(*M);
  auto *summary = model.lookupHandler("sub_18000e300");
  ASSERT_NE(summary, nullptr);
  ASSERT_EQ(summary->dispatches.size(), 1u);
  const auto &dispatch_summary = summary->dispatches.front();
  ASSERT_EQ(dispatch_summary.successors.size(), 1u);
  EXPECT_EQ(dispatch_summary.successors.front().target_pc, 0x18000E340ULL);
  ASSERT_TRUE(dispatch_summary.successors.front().target_function_name.has_value());
  EXPECT_EQ(*dispatch_summary.successors.front().target_function_name,
            "blk_18000e340");
}

}  // namespace

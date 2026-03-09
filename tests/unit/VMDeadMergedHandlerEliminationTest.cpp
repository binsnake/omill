#include "omill/Passes/VMDeadMergedHandlerElimination.h"

#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/Utils/LiftedNames.h"

#include <gtest/gtest.h>

namespace {

class VMDeadMergedHandlerEliminationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    return std::make_unique<llvm::Module>("test", Ctx);
  }

  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  llvm::Function *createMergedHandler(llvm::Module &M, uint64_t va) {
    std::string name = omill::liftedFunctionName(va);
    auto *F = llvm::Function::Create(liftedFnType(),
                                     llvm::GlobalValue::InternalLinkage, name,
                                     M);
    F->addFnAttr("omill.vm_handler");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(F->getArg(2));
    return F;
  }

  llvm::Function *createDemergedClone(llvm::Module &M, uint64_t va,
                                      uint64_t incoming_hash) {
    std::string name = omill::demergedHandlerCloneName(va, incoming_hash);
    auto *F = llvm::Function::Create(liftedFnType(),
                                     llvm::GlobalValue::InternalLinkage, name,
                                     M);
    F->addFnAttr("omill.vm_handler");
    F->addFnAttr("omill.vm_demerged_clone", "1");
    F->addFnAttr("omill.vm_trace_in_hash", llvm::utohexstr(incoming_hash));
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(F->getArg(2));
    return F;
  }

  llvm::Function *createCaller(llvm::Module &M, llvm::StringRef name,
                               llvm::Function *callee) {
    auto *ft = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {}, false);
    auto *F =
        llvm::Function::Create(ft, llvm::GlobalValue::ExternalLinkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *null_ptr = llvm::ConstantPointerNull::get(ptr_ty);
    auto *zero_i64 = llvm::ConstantInt::get(i64_ty, 0);
    B.CreateCall(callee, {null_ptr, zero_i64, null_ptr});
    B.CreateRetVoid();
    return F;
  }

  void runPass(llvm::Module &M, omill::VMTraceMap trace_map = {},
               std::vector<omill::VirtualCalleeRecord> vcr_records = {}) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass(
        [&] { return omill::VMTraceMapAnalysis(std::move(trace_map)); });
    MAM.registerPass(
        [&] { return omill::VirtualCalleeRegistryAnalysis(); });

    if (!vcr_records.empty())
      omill::setVirtualCalleeRegistryMetadata(M, vcr_records);

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::VMDeadMergedHandlerEliminationPass());
    MPM.run(M, MAM);
  }
};

// A merged handler with full clone coverage and no uses is eliminated.
TEST_F(VMDeadMergedHandlerEliminationTest, EliminatesFullyCoveredUnused) {
  auto M = createModule();
  uint64_t handler_va = 0x401000;
  uint64_t hash_a = 0xAAAA;
  uint64_t hash_b = 0xBBBB;

  auto *merged = createMergedHandler(*M, handler_va);
  (void)merged;
  createDemergedClone(*M, handler_va, hash_a);
  createDemergedClone(*M, handler_va, hash_b);

  omill::VMTraceMap trace_map;
  omill::VMTraceRecord rec_a;
  rec_a.handler_va = handler_va;
  rec_a.incoming_hash = hash_a;
  rec_a.outgoing_hash = 0;
  rec_a.is_vmexit = true;
  trace_map.recordTrace(rec_a);

  omill::VMTraceRecord rec_b;
  rec_b.handler_va = handler_va;
  rec_b.incoming_hash = hash_b;
  rec_b.outgoing_hash = 0;
  rec_b.is_vmexit = true;
  trace_map.recordTrace(rec_b);

  ASSERT_NE(M->getFunction(omill::liftedFunctionName(handler_va)), nullptr);

  runPass(*M, std::move(trace_map));

  // Merged handler should be deleted.
  EXPECT_EQ(M->getFunction(omill::liftedFunctionName(handler_va)), nullptr);
  // Clones should remain.
  EXPECT_NE(M->getFunction(omill::demergedHandlerCloneName(handler_va, hash_a)),
            nullptr);
  EXPECT_NE(M->getFunction(omill::demergedHandlerCloneName(handler_va, hash_b)),
            nullptr);
}

// A merged handler with partial coverage is kept.
TEST_F(VMDeadMergedHandlerEliminationTest, KeepsPartiallyCoveredHandler) {
  auto M = createModule();
  uint64_t handler_va = 0x401000;
  uint64_t hash_a = 0xAAAA;
  uint64_t hash_b = 0xBBBB;

  createMergedHandler(*M, handler_va);
  createDemergedClone(*M, handler_va, hash_a);
  // hash_b has NO clone

  omill::VMTraceMap trace_map;
  omill::VMTraceRecord rec_a;
  rec_a.handler_va = handler_va;
  rec_a.incoming_hash = hash_a;
  rec_a.is_vmexit = true;
  trace_map.recordTrace(rec_a);

  omill::VMTraceRecord rec_b;
  rec_b.handler_va = handler_va;
  rec_b.incoming_hash = hash_b;
  rec_b.is_vmexit = true;
  trace_map.recordTrace(rec_b);

  runPass(*M, std::move(trace_map));

  // Merged handler should be kept.
  EXPECT_NE(M->getFunction(omill::liftedFunctionName(handler_va)), nullptr);
}

// A merged handler with full coverage but remaining uses is not deleted.
TEST_F(VMDeadMergedHandlerEliminationTest, KeepsFullyCoveredWithUses) {
  auto M = createModule();
  uint64_t handler_va = 0x401000;
  uint64_t hash_a = 0xAAAA;

  auto *merged = createMergedHandler(*M, handler_va);
  createDemergedClone(*M, handler_va, hash_a);
  // Create a caller that uses the merged handler, keeping it alive.
  createCaller(*M, "caller", merged);

  omill::VMTraceMap trace_map;
  omill::VMTraceRecord rec;
  rec.handler_va = handler_va;
  rec.incoming_hash = hash_a;
  rec.is_vmexit = true;
  trace_map.recordTrace(rec);

  runPass(*M, std::move(trace_map));

  // Merged handler should be kept (has uses).
  auto *fn = M->getFunction(omill::liftedFunctionName(handler_va));
  ASSERT_NE(fn, nullptr);
  // But should be marked internal so GlobalDCE can clean it up later.
  EXPECT_TRUE(fn->hasInternalLinkage());
}

// A handler with no trace data is untouched.
TEST_F(VMDeadMergedHandlerEliminationTest, IgnoresHandlerWithNoTraceData) {
  auto M = createModule();
  uint64_t handler_va = 0x401000;

  createMergedHandler(*M, handler_va);

  omill::VMTraceMap trace_map;  // Empty trace map.
  runPass(*M, std::move(trace_map));

  EXPECT_NE(M->getFunction(omill::liftedFunctionName(handler_va)), nullptr);
}

// Demerged clones and wrappers are not considered as candidates.
TEST_F(VMDeadMergedHandlerEliminationTest, SkipsDemergedCloneAndWrapper) {
  auto M = createModule();
  uint64_t handler_va = 0x401000;
  uint64_t hash_a = 0xAAAA;

  // Create only a demerged clone (not a merged handler).
  createDemergedClone(*M, handler_va, hash_a);

  // Create a wrapper.
  auto *wrapper = llvm::Function::Create(
      liftedFnType(), llvm::GlobalValue::ExternalLinkage, "sub_402000", *M);
  wrapper->addFnAttr("omill.vm_handler");
  wrapper->addFnAttr("omill.vm_wrapper");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", wrapper);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(wrapper->getArg(2));

  omill::VMTraceMap trace_map;
  omill::VMTraceRecord rec;
  rec.handler_va = handler_va;
  rec.incoming_hash = hash_a;
  rec.is_vmexit = true;
  trace_map.recordTrace(rec);

  runPass(*M, std::move(trace_map));

  // Both should remain.
  EXPECT_NE(
      M->getFunction(omill::demergedHandlerCloneName(handler_va, hash_a)),
      nullptr);
  EXPECT_NE(M->getFunction("sub_402000"), nullptr);
}

// Coverage via VirtualCalleeRegistry (outlined virtual callees).
TEST_F(VMDeadMergedHandlerEliminationTest,
       EliminatesWhenCoveredByRegistry) {
  auto M = createModule();
  uint64_t handler_va = 0x401000;
  uint64_t hash_a = 0xAAAA;

  createMergedHandler(*M, handler_va);
  // No demerged clone function, but the registry knows about this trace key.

  omill::VMTraceMap trace_map;
  omill::VMTraceRecord rec;
  rec.handler_va = handler_va;
  rec.incoming_hash = hash_a;
  rec.is_vmexit = true;
  trace_map.recordTrace(rec);

  std::vector<omill::VirtualCalleeRecord> vcr_records = {
      {"sub_401000_native__caller_0_hAAAA", "sub_401000_native",
       "caller_native", "hash_resolved", hash_a, 1, handler_va, hash_a, false},
  };

  runPass(*M, std::move(trace_map), vcr_records);

  // Merged handler should be deleted — the registry provides coverage.
  EXPECT_EQ(M->getFunction(omill::liftedFunctionName(handler_va)), nullptr);
}

// Empty module is a no-op.
TEST_F(VMDeadMergedHandlerEliminationTest, EmptyModuleNoOp) {
  auto M = createModule();
  omill::VMTraceMap trace_map;
  runPass(*M, std::move(trace_map));
  // No crash, no changes.
}

}  // namespace

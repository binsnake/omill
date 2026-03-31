#include "omill/Remill/Normalization.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Omill.h"

#include <gtest/gtest.h>

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Passes/PassBuilder.h>

namespace {

class RemillNormalizationOrchestratorTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  static llvm::FunctionType *liftedFnTy(llvm::LLVMContext &Ctx) {
    auto *ptr_ty = llvm::PointerType::getUnqual(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  static void runModulePasses(llvm::Module &M, llvm::ModulePassManager &MPM,
                              omill::BinaryMemoryMap map = {}) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    MAM.registerPass(
        [&] { return omill::BinaryMemoryAnalysis(std::move(map)); });
    PB.registerLoopAnalyses(LAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerModuleAnalyses(MAM);
    omill::registerAnalyses(FAM);
    omill::registerModuleAnalyses(MAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    MPM.run(M, MAM);
  }
};

TEST_F(RemillNormalizationOrchestratorTest,
       FinalVerificationCanonicalizesLegacyDispatchNames) {
  llvm::Module M("legacy_dispatch", Ctx);
  auto *lifted_ty = liftedFnTy(Ctx);
  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_401000", M);
  auto *legacy_dispatch = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__omill_dispatch_call",
      M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
  llvm::IRBuilder<> B(entry);
  auto *call = B.CreateCall(
      legacy_dispatch, {root->getArg(0), B.getInt64(0x401020), root->getArg(2)});
  B.CreateRet(call);

  omill::RemillNormalizationOrchestrator orchestrator;
  llvm::ModulePassManager MPM;
  orchestrator.appendToPipeline(
      MPM, omill::RemillNormalizationRequest{
               omill::RemillNormalizationEpoch::kFinalVerification,
               /*no_abi_mode=*/true,
               /*aggressive_folding=*/false,
               {}});
  runModulePasses(M, MPM);

  EXPECT_EQ(M.getFunction("__omill_dispatch_call"), nullptr);
  auto *canonical = M.getFunction("__remill_function_call");
  ASSERT_NE(canonical, nullptr);

  bool found = false;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      auto *callee = CB ? CB->getCalledFunction() : nullptr;
      if (callee && callee == canonical)
        found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST_F(RemillNormalizationOrchestratorTest,
       SummaryCountsLegacyDispatchWithoutWrapperMetrics) {
  llvm::Module M("summary", Ctx);
  auto *lifted_ty = liftedFnTy(Ctx);
  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_401000", M);
  auto *legacy_dispatch = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__omill_dispatch_jump",
      M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
  llvm::IRBuilder<> B(entry);
  auto *call = B.CreateCall(
      legacy_dispatch, {root->getArg(0), B.getInt64(0x401020), root->getArg(2)});
  B.CreateRet(call);

  omill::RemillNormalizationOrchestrator orchestrator;
  auto summary = orchestrator.summarize(M);
  EXPECT_EQ(summary.unresolved_dispatch_intrinsics, 1u);
  EXPECT_EQ(summary.legacy_omill_dispatch_intrinsics, 1u);
  EXPECT_EQ(summary.native_wrapper_functions, 0u);
}

TEST_F(RemillNormalizationOrchestratorTest,
       AggressiveFoldingUsesCombinedFixedPointCanonicalization) {
  llvm::Module M("aggressive_fold", Ctx);
  auto *ptr_ty = llvm::PointerType::getUnqual(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(liftedFnTy(Ctx),
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_401000", M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
  llvm::IRBuilder<> B(entry);
  auto *slot = B.CreateAlloca(i64_ty, nullptr, "slot");
  B.CreateStore(B.getInt64(0x12345678), slot);
  auto *value = B.CreateLoad(i64_ty, slot);
  auto *xored = B.CreateXor(value, B.getInt64(0x10));
  auto *ret_pc = B.CreateAdd(xored, B.getInt64(1));
  B.CreateRet(B.CreateIntToPtr(ret_pc, ptr_ty));

  omill::RemillNormalizationOrchestrator orchestrator;
  llvm::ModulePassManager MPM;
  orchestrator.appendToPipeline(
      MPM, omill::RemillNormalizationRequest{
               omill::RemillNormalizationEpoch::kIncrementalRound,
               /*no_abi_mode=*/true,
               /*aggressive_folding=*/true,
               {}});
  runModulePasses(M, MPM);

  unsigned i64_loads = 0;
  unsigned xors = 0;
  unsigned adds = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
          LI && LI->getType() == i64_ty)
        ++i64_loads;
      if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        if (BO->getOpcode() == llvm::Instruction::Xor)
          ++xors;
        if (BO->getOpcode() == llvm::Instruction::Add)
          ++adds;
      }
    }
  }
  EXPECT_EQ(i64_loads, 0u);
  EXPECT_EQ(xors, 0u);
  EXPECT_EQ(adds, 0u);
}

TEST_F(RemillNormalizationOrchestratorTest,
       FinalNoAbiNormalizationCanLowerSemanticHelpers) {
  llvm::Module M("semantic_helper", Ctx);
  auto *ptr_ty = llvm::PointerType::getUnqual(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(liftedFnTy(Ctx),
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_401000", M);
  auto *helper = llvm::Function::Create(liftedFnTy(Ctx),
                                        llvm::GlobalValue::InternalLinkage,
                                        "_ZN12_GLOBAL__N_14PUSHI2InImEEE"
                                        "P6MemoryS4_R5StateT_",
                                        M);
  auto *read64 = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "__remill_read_memory_64", M);

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded = B.CreateCall(read64, {helper->getArg(0), helper->getArg(1)});
    auto *ret = B.CreateIntToPtr(loaded, ptr_ty);
    B.CreateRet(ret);
  }
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  omill::RemillNormalizationOrchestrator orchestrator;
  llvm::ModulePassManager MPM;
  orchestrator.appendToPipeline(
      MPM, omill::RemillNormalizationRequest{
               omill::RemillNormalizationEpoch::kFinalVerification,
               /*no_abi_mode=*/true,
               /*aggressive_folding=*/true,
               {},
               /*include_semantic_helpers=*/true});
  runModulePasses(M, MPM);

  auto summary = orchestrator.summarize(M);
  EXPECT_EQ(summary.live_memory_intrinsics, 0u);
}

}  // namespace

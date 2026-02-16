#include "omill/Passes/PassRegistry.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/RemillIntrinsicAnalysis.h"

#include <gtest/gtest.h>

namespace {

class PassRegistryTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
};

TEST_F(PassRegistryTest, RegisterAnalyses_Succeeds) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
      "f80:128-n8:16:32:64-S128");

  // Create a simple function to query the analysis on.
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<>(entry).CreateRetVoid();

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

  // Register omill analyses.
  omill::registerAnalyses(FAM);

  // Query RemillIntrinsicAnalysis — should succeed without crashing.
  auto &result = FAM.getResult<omill::RemillIntrinsicAnalysis>(*fn);

  // Empty function should have no intrinsics.
  EXPECT_FALSE(result.hasAnyIntrinsics());
}

TEST_F(PassRegistryTest, RegisterPassBuilderCallbacks_Succeeds) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
      "f80:128-n8:16:32:64-S128");

  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *fn_ty = llvm::FunctionType::get(void_ty, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<>(entry).CreateRetVoid();

  llvm::PassBuilder PB;

  // Register callbacks before creating analysis managers.
  omill::registerPassBuilderCallbacks(PB);

  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;

  // PB's analysis registration callbacks should fire during these calls,
  // registering RemillIntrinsicAnalysis automatically.
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  // Should be able to query the analysis without manual registration.
  auto &result = FAM.getResult<omill::RemillIntrinsicAnalysis>(*fn);
  EXPECT_FALSE(result.hasAnyIntrinsics());
}

}  // namespace

#include "omill/Passes/EliminateStateStruct.h"

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

class EliminateStateStructTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with sub_401000 + sub_401000_native, and some
  /// unused __remill_* declarations.
  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Lifted function type
    auto *lifted_fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

    // Create sub_401000 (the original lifted function)
    auto *lifted_fn = llvm::Function::Create(
        lifted_fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted_fn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted_fn->getArg(2));

    // Create sub_401000_native (the recovered wrapper)
    auto *native_fn_ty =
        llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
    auto *native_fn = llvm::Function::Create(
        native_fn_ty, llvm::Function::ExternalLinkage, "sub_401000_native",
        *M);
    auto *native_entry =
        llvm::BasicBlock::Create(Ctx, "entry", native_fn);
    llvm::IRBuilder<> NB(native_entry);
    NB.CreateRet(NB.getInt64(0));

    // Declare some unused __remill_* intrinsics
    M->getOrInsertFunction("__remill_read_memory_32",
                           llvm::FunctionType::get(
                               llvm::Type::getInt32Ty(Ctx),
                               {ptr_ty, i64_ty}, false));
    M->getOrInsertFunction("__remill_write_memory_32",
                           llvm::FunctionType::get(
                               ptr_ty, {ptr_ty, i64_ty,
                                        llvm::Type::getInt32Ty(Ctx)},
                               false));

    return M;
  }
};

TEST_F(EliminateStateStructTest, InternalizesLiftedFunction) {
  auto M = createTestModule();

  auto *lifted_fn = M->getFunction("sub_401000");
  ASSERT_NE(lifted_fn, nullptr);
  EXPECT_EQ(lifted_fn->getLinkage(), llvm::GlobalValue::ExternalLinkage);

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

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::EliminateStateStructPass());
  MPM.run(*M, MAM);

  // After: sub_401000 should have internal linkage
  EXPECT_EQ(lifted_fn->getLinkage(), llvm::GlobalValue::InternalLinkage);

  // sub_401000_native should remain external
  auto *native_fn = M->getFunction("sub_401000_native");
  ASSERT_NE(native_fn, nullptr);
  EXPECT_EQ(native_fn->getLinkage(), llvm::GlobalValue::ExternalLinkage);
}

TEST_F(EliminateStateStructTest, RemovesUnusedRemillDecls) {
  auto M = createTestModule();

  // Before: unused __remill_* declarations exist
  EXPECT_NE(M->getFunction("__remill_read_memory_32"), nullptr);
  EXPECT_NE(M->getFunction("__remill_write_memory_32"), nullptr);

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

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::EliminateStateStructPass());
  MPM.run(*M, MAM);

  // After: unused __remill_* declarations should be removed
  EXPECT_EQ(M->getFunction("__remill_read_memory_32"), nullptr);
  EXPECT_EQ(M->getFunction("__remill_write_memory_32"), nullptr);
}

}  // namespace

#include "omill/Passes/FoldProgramCounter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class FoldProgramCounterTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with a lifted function that uses the PC arg in an add.
  std::unique_ptr<llvm::Module> createTestModule(llvm::StringRef fn_name,
                                                  bool use_pc = true) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    auto *fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, fn_name, *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    if (use_pc) {
      auto *pc = test_fn->getArg(1);
      auto *result = B.CreateAdd(pc, B.getInt64(0x100), "rip_rel");
      (void)result;
    }

    B.CreateRet(test_fn->getArg(2));
    return M;
  }

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::FoldProgramCounterPass());

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

    FPM.run(*F, FAM);
  }
};

TEST_F(FoldProgramCounterTest, FoldsToEntryVA) {
  auto M = createTestModule("sub_140001000");
  auto *F = M->getFunction("sub_140001000");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // The add instruction should now use constant 0x140001000 instead of the arg.
  bool found_constant = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *add = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(0))) {
          EXPECT_EQ(CI->getZExtValue(), 0x140001000ULL);
          found_constant = true;
        }
      }
    }
  }
  EXPECT_TRUE(found_constant);
  EXPECT_TRUE(F->getArg(1)->use_empty());
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(FoldProgramCounterTest, DottedNameVariant) {
  auto M = createTestModule("sub_140001000.1");
  auto *F = M->getFunction("sub_140001000.1");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // Same VA should be extracted despite the .1 suffix.
  bool found_constant = false;
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *add = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(0))) {
          EXPECT_EQ(CI->getZExtValue(), 0x140001000ULL);
          found_constant = true;
        }
      }
    }
  }
  EXPECT_TRUE(found_constant);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(FoldProgramCounterTest, SkipsNonLiftedFunction) {
  auto M = createTestModule("foo");
  auto *F = M->getFunction("foo");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // PC arg should still have uses (not replaced).
  EXPECT_FALSE(F->getArg(1)->use_empty());
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(FoldProgramCounterTest, SkipsUnusedPC) {
  auto M = createTestModule("sub_140001000", /*use_pc=*/false);
  auto *F = M->getFunction("sub_140001000");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // No change expected — PC was unused.
  EXPECT_TRUE(F->getArg(1)->use_empty());
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(FoldProgramCounterTest, InvalidHexSkipped) {
  auto M = createTestModule("sub_ZZZZ");
  auto *F = M->getFunction("sub_ZZZZ");
  ASSERT_NE(F, nullptr);

  runPass(F);

  // PC arg should still have uses (bad hex → no fold).
  EXPECT_FALSE(F->getArg(1)->use_empty());
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(FoldProgramCounterTest, DoesNotFoldControlFlowSensitivePCUse) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_140001000", *M);
  auto dispatch = M->getOrInsertFunction("__omill_dispatch_jump", fn_ty);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *pc = F->getArg(1);
  auto *pc_plus = B.CreateAdd(pc, B.getInt64(0x20), "pc_plus");
  auto *p = B.CreateIntToPtr(pc_plus, ptr_ty);
  (void)B.CreateLoad(B.getInt8Ty(), p);
  (void)B.CreateCall(dispatch, {F->getArg(0), pc, F->getArg(2)});
  B.CreateRet(F->getArg(2));

  runPass(F);

  bool found_folded_add = false;
  bool dispatch_arg_kept_dynamic = false;

  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (auto *add = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(add->getOperand(0))) {
          EXPECT_EQ(CI->getZExtValue(), 0x140001000ULL);
          found_folded_add = true;
        }
      }

      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "__omill_dispatch_jump") {
          dispatch_arg_kept_dynamic = (CI->getArgOperand(1) == F->getArg(1));
        }
      }
    }
  }

  EXPECT_TRUE(found_folded_add);
  EXPECT_TRUE(dispatch_arg_kept_dynamic);
  EXPECT_FALSE(F->getArg(1)->use_empty());
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace

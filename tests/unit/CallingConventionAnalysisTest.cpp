#include "omill/Analysis/CallingConventionAnalysis.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Utils/StateFieldMap.h"

#include <gtest/gtest.h>

namespace {

class CallingConventionAnalysisTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Helper: create a module with __remill_basic_block register GEPs
  /// and a lifted function that reads/writes specified registers.
  std::unique_ptr<llvm::Module> createModuleWithState(
      const std::vector<std::pair<std::string, unsigned>> &live_in_regs,
      bool writes_rax = true) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
    auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
    state_ty->setBody({arr_ty});

    // __remill_basic_block with register name GEPs.
    auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);

    auto *bb_state = bb_fn->getArg(0);
    struct RegDef { const char *name; unsigned offset; };
    RegDef all_regs[] = {
        {"RAX", 0}, {"RBX", 8}, {"RCX", 16}, {"RDX", 24},
        {"RSI", 32}, {"RDI", 40}, {"RSP", 48}, {"RBP", 56},
        {"R8", 64}, {"R9", 72}, {"R10", 80}, {"R11", 88},
        {"R12", 96}, {"R13", 104}, {"R14", 112}, {"R15", 120},
        {"RIP", 128},
    };
    for (auto &reg : all_regs) {
      BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, reg.offset, reg.name);
    }
    BBB.CreateRet(bb_fn->getArg(2));

    // Test lifted function.
    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *mem = test_fn->getArg(2);

    // Load from each live-in register.
    for (auto &[name, offset] : live_in_regs) {
      auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, offset);
      B.CreateLoad(i64_ty, gep, name + "_val");
    }

    // Optionally store result to RAX.
    if (writes_rax) {
      auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
      B.CreateStore(B.getInt64(42), rax_gep);
    }

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(CallingConventionAnalysisTest, DetectsWin64WithTwoParams) {
  // Win64: params in RCX (offset 16), RDX (offset 24)
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RDX", 24},
  });

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *test_fn = M->getFunction("sub_401000");
  ASSERT_NE(test_fn, nullptr);

  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  EXPECT_EQ(abi->cc, omill::DetectedCC::kWin64);
  EXPECT_EQ(abi->numParams(), 2u);
  EXPECT_EQ(abi->params[0].reg_name, "RCX");
  EXPECT_EQ(abi->params[1].reg_name, "RDX");
  EXPECT_TRUE(abi->ret.has_value());
  EXPECT_EQ(abi->ret->reg_name, "RAX");
  EXPECT_EQ(abi->shadow_space_size, 32u);
}

TEST_F(CallingConventionAnalysisTest, DetectsWin64FourParams) {
  // Win64: all 4 params RCX, RDX, R8, R9
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RDX", 24},
      {"R8", 64},
      {"R9", 72},
  });

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *test_fn = M->getFunction("sub_401000");
  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  EXPECT_EQ(abi->cc, omill::DetectedCC::kWin64);
  EXPECT_EQ(abi->numParams(), 4u);
  EXPECT_EQ(abi->params[0].reg_name, "RCX");
  EXPECT_EQ(abi->params[1].reg_name, "RDX");
  EXPECT_EQ(abi->params[2].reg_name, "R8");
  EXPECT_EQ(abi->params[3].reg_name, "R9");
}

TEST_F(CallingConventionAnalysisTest, DetectsVoidFunction) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(test_fn->getArg(2));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  EXPECT_EQ(abi->cc, omill::DetectedCC::kVoid);
  EXPECT_EQ(abi->numParams(), 0u);
  EXPECT_FALSE(abi->ret.has_value());
}

}  // namespace

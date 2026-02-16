#include "omill/Passes/RecoverGlobalTypes.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"

#include <gtest/gtest.h>

namespace {

class RecoverGlobalTypesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");
    return M;
  }

  /// Create a function with an inttoptr(const addr) that is used.
  llvm::Function *createFnWithIntToPtr(llvm::Module &M, uint64_t addr) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {}, false);
    auto *fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(entry);
    auto *addr_val = B.getInt64(addr);
    auto *ptr = B.CreateIntToPtr(addr_val, ptr_ty, "str_ptr");
    B.CreateRet(ptr);
    return fn;
  }

  llvm::PreservedAnalyses runPass(llvm::Module &M,
                                   omill::BinaryMemoryMap &&mem_map) {
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
    MAM.registerPass(
        [&] { return omill::BinaryMemoryAnalysis(std::move(mem_map)); });

    // Require the analysis so it's cached for function passes.
    llvm::ModulePassManager MPM;
    MPM.addPass(
        llvm::RequireAnalysisPass<omill::BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::RecoverGlobalTypesPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    return MPM.run(M, MAM);
  }
};

TEST_F(RecoverGlobalTypesTest, AsciiStringRecovered) {
  auto M = createModule();
  auto *fn = createFnWithIntToPtr(*M, 0x140010000);

  // Set up binary memory with "Hello, World!\0" at the address.
  omill::BinaryMemoryMap mem;
  const char *str = "Hello, World!";
  mem.addRegion(0x140010000,
                reinterpret_cast<const uint8_t *>(str),
                strlen(str) + 1);

  runPass(*M, std::move(mem));
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The function should return a global variable, not a ConstantExpr.
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *GV = llvm::dyn_cast<llvm::GlobalVariable>(ret->getReturnValue());
  ASSERT_NE(GV, nullptr);
  EXPECT_TRUE(GV->isConstant());
  EXPECT_TRUE(GV->hasPrivateLinkage());
}

TEST_F(RecoverGlobalTypesTest, ShortStringSkipped) {
  auto M = createModule();
  createFnWithIntToPtr(*M, 0x140010000);

  // "abc" is only 3 chars — below minimum.
  omill::BinaryMemoryMap mem;
  const char *str = "abc";
  mem.addRegion(0x140010000,
                reinterpret_cast<const uint8_t *>(str),
                strlen(str) + 1);

  runPass(*M, std::move(mem));

  // Should NOT create a global.
  EXPECT_EQ(M->getGlobalVariable(".str.0x140010000"), nullptr);
}

TEST_F(RecoverGlobalTypesTest, NonStringBinaryDataUnchanged) {
  auto M = createModule();
  auto *fn = createFnWithIntToPtr(*M, 0x140010000);

  // Binary data with non-printable bytes.
  omill::BinaryMemoryMap mem;
  uint8_t data[] = {0xFF, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06};
  mem.addRegion(0x140010000, data, sizeof(data));

  runPass(*M, std::move(mem));

  // Should NOT create a global.
  EXPECT_EQ(M->getGlobalVariable(".str.0x140010000"), nullptr);

  // The return value should still be the original inttoptr (ConstantExpr).
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(
      fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret, nullptr);
  EXPECT_FALSE(llvm::isa<llvm::GlobalVariable>(ret->getReturnValue()));
}

}  // namespace

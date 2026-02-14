#include "omill/Passes/LowerMemoryIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LowerMemoryIntrinsicsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createTestModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128");

    auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    // Declare __remill_read_memory_32(Memory*, addr_t) -> uint32_t
    auto *read32_ty = llvm::FunctionType::get(i32_ty, {ptr_ty, i64_ty}, false);
    M->getOrInsertFunction("__remill_read_memory_32", read32_ty);

    // Declare __remill_write_memory_32(Memory*, addr_t, uint32_t) -> Memory*
    auto *write32_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i32_ty}, false);
    M->getOrInsertFunction("__remill_write_memory_32", write32_ty);

    // Create a test function that reads memory, adds 1, writes back.
    auto *fn_ty = llvm::FunctionType::get(
        ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "test_func", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> Builder(entry);

    auto *state = test_fn->getArg(0);
    auto *pc = test_fn->getArg(1);
    auto *mem = test_fn->getArg(2);

    // uint32_t val = __remill_read_memory_32(mem, 0x1000)
    auto *read_fn = M->getFunction("__remill_read_memory_32");
    auto *addr = Builder.getInt64(0x1000);
    auto *val = Builder.CreateCall(read_fn, {mem, addr});

    // val = val + 1
    auto *val_plus_1 = Builder.CreateAdd(val, Builder.getInt32(1));

    // mem2 = __remill_write_memory_32(mem, 0x1000, val + 1)
    auto *write_fn = M->getFunction("__remill_write_memory_32");
    auto *mem2 = Builder.CreateCall(write_fn, {mem, addr, val_plus_1});

    Builder.CreateRet(mem2);

    return M;
  }
};

TEST_F(LowerMemoryIntrinsicsTest, LowersReadsToLoads) {
  auto M = createTestModule();
  auto *test_fn = M->getFunction("test_func");
  ASSERT_NE(test_fn, nullptr);

  // Run the pass.
  llvm::FunctionPassManager FPM;
  FPM.addPass(omill::LowerMemoryIntrinsicsPass());

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

  FPM.run(*test_fn, FAM);

  // Verify: no more calls to __remill_read/write_memory
  unsigned remill_call_count = 0;
  unsigned load_count = 0;
  unsigned store_count = 0;

  for (auto &BB : *test_fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName().starts_with("__remill_")) {
          remill_call_count++;
        }
      }
      if (llvm::isa<llvm::LoadInst>(&I)) load_count++;
      if (llvm::isa<llvm::StoreInst>(&I)) store_count++;
    }
  }

  EXPECT_EQ(remill_call_count, 0u);
  EXPECT_GE(load_count, 1u);   // At least one load from the read
  EXPECT_GE(store_count, 1u);  // At least one store from the write

  EXPECT_FALSE(llvm::verifyFunction(*test_fn, &llvm::errs()));
}

}  // namespace

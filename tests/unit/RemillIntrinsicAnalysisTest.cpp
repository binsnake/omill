#include "omill/Analysis/RemillIntrinsicAnalysis.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class RemillIntrinsicAnalysisTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  llvm::FunctionType *liftedFnTy() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  std::unique_ptr<llvm::Module> createModule() {
    return std::make_unique<llvm::Module>("test", Ctx);
  }

  /// Create a lifted function with an entry block.
  llvm::Function *addLiftedFn(llvm::Module &M, const char *name) {
    auto *fn = llvm::Function::Create(
        liftedFnTy(), llvm::Function::ExternalLinkage, name, M);
    llvm::BasicBlock::Create(Ctx, "entry", fn);
    return fn;
  }

  /// Declare a remill intrinsic with the given name and type.
  llvm::Function *declareIntrinsic(llvm::Module &M, const char *name,
                                   llvm::FunctionType *ty) {
    return llvm::Function::Create(
        ty, llvm::Function::ExternalLinkage, name, M);
  }

  omill::RemillIntrinsicInfo runAnalysis(llvm::Function &F) {
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
    FAM.registerPass([&] { return omill::RemillIntrinsicAnalysis(); });
    return FAM.getResult<omill::RemillIntrinsicAnalysis>(F);
  }
};

TEST_F(RemillIntrinsicAnalysisTest, ReadMemory) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // uint64_t __remill_read_memory_64(Memory*, addr_t)
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_fn = declareIntrinsic(*M, "__remill_read_memory_64", read_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(read_fn, {llvm::Constant::getNullValue(ptr_ty),
                         llvm::ConstantInt::get(i64_ty, 0x1000)});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.read_memory.size(), 1u);
  EXPECT_TRUE(info.write_memory.empty());
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, WriteMemory) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Memory* __remill_write_memory_64(Memory*, addr_t, uint64_t)
  auto *write_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);
  auto *write_fn = declareIntrinsic(*M, "__remill_write_memory_64", write_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(write_fn, {llvm::Constant::getNullValue(ptr_ty),
                          llvm::ConstantInt::get(i64_ty, 0x1000),
                          llvm::ConstantInt::get(i64_ty, 42)});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.write_memory.size(), 1u);
  EXPECT_TRUE(info.read_memory.empty());
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, FlagComputation) {
  auto M = createModule();
  auto *i1_ty = llvm::Type::getInt1Ty(Ctx);

  // bool __remill_flag_computation_zero(bool, ...)
  auto *flag_ty = llvm::FunctionType::get(i1_ty, {i1_ty}, true);
  auto *flag_fn =
      declareIntrinsic(*M, "__remill_flag_computation_zero", flag_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(flag_fn, {llvm::ConstantInt::getFalse(Ctx)});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.flag_computations.size(), 1u);
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, UndefinedValue) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // uint64_t __remill_undefined_64(void)
  auto *undef_ty = llvm::FunctionType::get(i64_ty, false);
  auto *undef_fn = declareIntrinsic(*M, "__remill_undefined_64", undef_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(undef_fn);
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.undefined_values.size(), 1u);
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, ControlFlow) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Memory* __remill_function_call(State&, addr_t, Memory*)
  auto *cf_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *call_fn = declareIntrinsic(*M, "__remill_function_call", cf_ty);
  auto *jump_fn = declareIntrinsic(*M, "__remill_jump", cf_ty);
  auto *ret_fn = declareIntrinsic(*M, "__remill_function_return", cf_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  auto *null_ptr = llvm::Constant::getNullValue(ptr_ty);
  auto *zero = llvm::ConstantInt::get(i64_ty, 0);

  B.CreateCall(call_fn, {null_ptr, zero, null_ptr});
  B.CreateCall(jump_fn, {null_ptr, zero, null_ptr});
  B.CreateCall(ret_fn, {null_ptr, zero, null_ptr});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.control_flow.size(), 3u);
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, HyperCall) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Memory* __remill_sync_hyper_call(State&, addr_t, Memory*)
  auto *hc_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *sync_fn = declareIntrinsic(*M, "__remill_sync_hyper_call", hc_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  auto *null_ptr = llvm::Constant::getNullValue(ptr_ty);
  auto *zero = llvm::ConstantInt::get(i64_ty, 0);
  B.CreateCall(sync_fn, {null_ptr, zero, null_ptr});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.hyper_calls.size(), 1u);
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, NoIntrinsics) {
  auto M = createModule();

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_FALSE(info.hasAnyIntrinsics());
  EXPECT_TRUE(info.read_memory.empty());
  EXPECT_TRUE(info.write_memory.empty());
  EXPECT_TRUE(info.flag_computations.empty());
  EXPECT_TRUE(info.undefined_values.empty());
  EXPECT_TRUE(info.control_flow.empty());
  EXPECT_TRUE(info.hyper_calls.empty());
  EXPECT_TRUE(info.barriers.empty());
  EXPECT_TRUE(info.volatile_barriers.empty());
}

TEST_F(RemillIntrinsicAnalysisTest, MultipleMixed) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1_ty = llvm::Type::getInt1Ty(Ctx);

  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_fn = declareIntrinsic(*M, "__remill_read_memory_64", read_ty);

  auto *write_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);
  auto *write_fn = declareIntrinsic(*M, "__remill_write_memory_64", write_ty);

  auto *flag_ty = llvm::FunctionType::get(i1_ty, {i1_ty}, true);
  auto *flag_fn =
      declareIntrinsic(*M, "__remill_flag_computation_zero", flag_ty);

  auto *cf_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *call_fn = declareIntrinsic(*M, "__remill_function_call", cf_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  auto *null_ptr = llvm::Constant::getNullValue(ptr_ty);
  auto *zero = llvm::ConstantInt::get(i64_ty, 0);

  // Two reads, one write, one flag, one control flow
  B.CreateCall(read_fn, {null_ptr, zero});
  B.CreateCall(read_fn, {null_ptr, zero});
  B.CreateCall(write_fn, {null_ptr, zero, zero});
  B.CreateCall(flag_fn, {llvm::ConstantInt::getFalse(Ctx)});
  B.CreateCall(call_fn, {null_ptr, zero, null_ptr});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.read_memory.size(), 2u);
  EXPECT_EQ(info.write_memory.size(), 1u);
  EXPECT_EQ(info.flag_computations.size(), 1u);
  EXPECT_EQ(info.control_flow.size(), 1u);
  EXPECT_TRUE(info.undefined_values.empty());
  EXPECT_TRUE(info.hyper_calls.empty());
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, DeclarationSkip) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Declare intrinsic but don't call it; analyze an empty function.
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  declareIntrinsic(*M, "__remill_read_memory_64", read_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_FALSE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, VolatileBarrier) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

  // Empty inline asm with side effects = remill volatile barrier.
  auto *asm_ty = llvm::FunctionType::get(void_ty, false);
  auto *ia = llvm::InlineAsm::get(asm_ty, "", "", /*hasSideEffects=*/true);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(asm_ty, ia);
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.volatile_barriers.size(), 1u);
  EXPECT_TRUE(info.hasAnyIntrinsics());
  // Inline asm should not appear in other buckets.
  EXPECT_TRUE(info.barriers.empty());
}

TEST_F(RemillIntrinsicAnalysisTest, NonVolatileInlineAsmIgnored) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

  // Non-empty inline asm or no side effects should be ignored.
  auto *asm_ty = llvm::FunctionType::get(void_ty, false);
  auto *ia_nonempty =
      llvm::InlineAsm::get(asm_ty, "nop", "", /*hasSideEffects=*/true);
  auto *ia_no_se =
      llvm::InlineAsm::get(asm_ty, "", "", /*hasSideEffects=*/false);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(asm_ty, ia_nonempty);
  B.CreateCall(asm_ty, ia_no_se);
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_TRUE(info.volatile_barriers.empty());
  EXPECT_FALSE(info.hasAnyIntrinsics());
}

TEST_F(RemillIntrinsicAnalysisTest, BarrierLoadStore) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Memory* __remill_barrier_load_store(Memory*)
  auto *barrier_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
  auto *barrier_fn =
      declareIntrinsic(*M, "__remill_barrier_load_store", barrier_ty);

  auto *F = addLiftedFn(*M, "test_fn");
  llvm::IRBuilder<> B(&F->getEntryBlock());
  B.CreateCall(barrier_fn, {llvm::Constant::getNullValue(ptr_ty)});
  B.CreateRet(F->getArg(2));

  auto info = runAnalysis(*F);
  EXPECT_EQ(info.barriers.size(), 1u);
  EXPECT_TRUE(info.hasAnyIntrinsics());
}

}  // namespace

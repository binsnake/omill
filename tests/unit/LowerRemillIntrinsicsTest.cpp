#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

static constexpr const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128";

class LowerRemillIntrinsicsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with standard types ready.
  std::unique_ptr<llvm::Module> makeModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a lifted function with remill signature: (ptr, i64, ptr) -> ptr
  llvm::Function *createLiftedFn(llvm::Module &M,
                                 llvm::StringRef name = "sub_401000") {
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
    return llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                  name, &M);
  }

  /// Run the pass with a specific category bitmask.
  void runPass(llvm::Function *F, uint32_t categories) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::LowerRemillIntrinsicsPass(categories));

    llvm::FunctionAnalysisManager FAM;
    llvm::LoopAnalysisManager LAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    llvm::PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    FPM.run(*F, FAM);
  }
};

// ---------------------------------------------------------------------------
// Test 1: __remill_read_memory_64 → load i64 from inttoptr(addr)
// ---------------------------------------------------------------------------
TEST_F(LowerRemillIntrinsicsTest, MemoryRead_LoweredToLoad) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_read_memory_64: (ptr, i64) -> i64
  auto *readFnTy = llvm::FunctionType::get(i64Ty, {ptrTy, i64Ty}, false);
  auto readFn = M->getOrInsertFunction("__remill_read_memory_64", readFnTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);
  (void)state;

  // %val = call i64 @__remill_read_memory_64(ptr %mem, i64 0x1000)
  auto *addr = llvm::ConstantInt::get(i64Ty, 0x1000);
  auto *call = B.CreateCall(readFn, {mem, addr});
  // We need to return ptr; use inttoptr of the read value as a dummy.
  auto *ret = B.CreateIntToPtr(call, ptrTy);
  B.CreateRet(ret);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  runPass(F, omill::LowerCategories::Memory);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // The read intrinsic call should be gone. Verify we now have a load.
  bool foundLoad = false;
  bool foundReadCall = false;
  for (auto &I : F->getEntryBlock()) {
    if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      EXPECT_TRUE(LI->getType()->isIntegerTy(64));
      foundLoad = true;
    }
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction())
        if (callee->getName() == "__remill_read_memory_64")
          foundReadCall = true;
    }
  }
  EXPECT_TRUE(foundLoad);
  EXPECT_FALSE(foundReadCall);
}

// ---------------------------------------------------------------------------
// Test 2: __remill_write_memory_64 → store + returns mem
// ---------------------------------------------------------------------------
TEST_F(LowerRemillIntrinsicsTest, MemoryWrite_LoweredToStore) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_write_memory_64: (ptr, i64, i64) -> ptr
  auto *writeFnTy =
      llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, i64Ty}, false);
  auto writeFn =
      M->getOrInsertFunction("__remill_write_memory_64", writeFnTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);

  auto *mem = F->getArg(2);
  auto *addr = llvm::ConstantInt::get(i64Ty, 0x2000);
  auto *val = llvm::ConstantInt::get(i64Ty, 42);

  // %newmem = call ptr @__remill_write_memory_64(ptr %mem, i64 0x2000, i64 42)
  auto *call = B.CreateCall(writeFn, {mem, addr, val});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  runPass(F, omill::LowerCategories::Memory);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Verify: store present, no write call, return value is original mem arg.
  bool foundStore = false;
  bool foundWriteCall = false;
  for (auto &I : F->getEntryBlock()) {
    if (llvm::isa<llvm::StoreInst>(&I))
      foundStore = true;
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction())
        if (callee->getName() == "__remill_write_memory_64")
          foundWriteCall = true;
    }
    if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
      // Write lowering replaces the call with the original mem argument.
      EXPECT_EQ(RI->getReturnValue(), mem);
    }
  }
  EXPECT_TRUE(foundStore);
  EXPECT_FALSE(foundWriteCall);
}

// ---------------------------------------------------------------------------
// Test 3: Flag computation intrinsic → returns first arg (the bool)
// ---------------------------------------------------------------------------
TEST_F(LowerRemillIntrinsicsTest, FlagBarrier_Erased) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i1Ty = llvm::Type::getInt1Ty(Ctx);

  // Declare __remill_flag_computation_zero: (i1) -> i1 (variadic in remill)
  auto *flagFnTy = llvm::FunctionType::get(i1Ty, {i1Ty}, true);
  auto flagFn =
      M->getOrInsertFunction("__remill_flag_computation_zero", flagFnTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);

  auto *mem = F->getArg(2);
  auto *flagVal = llvm::ConstantInt::getTrue(Ctx);

  // %flag = call i1 @__remill_flag_computation_zero(i1 true)
  auto *call = B.CreateCall(flagFn, {flagVal});
  // Use the flag in a select so it has a user, then return mem.
  auto *dummySelect =
      B.CreateSelect(call, mem, llvm::ConstantPointerNull::get(ptrTy));
  B.CreateRet(dummySelect);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  runPass(F, omill::LowerCategories::Flags);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // The flag call should be erased; the select should now use the original
  // constant true directly.
  bool foundFlagCall = false;
  for (auto &I : F->getEntryBlock()) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction())
        if (callee->getName().starts_with("__remill_flag_computation"))
          foundFlagCall = true;
    }
    if (auto *SI = llvm::dyn_cast<llvm::SelectInst>(&I)) {
      EXPECT_EQ(SI->getCondition(), flagVal);
    }
  }
  EXPECT_FALSE(foundFlagCall);
}

// ---------------------------------------------------------------------------
// Test 4: __remill_undefined_64 → freeze(poison)
// ---------------------------------------------------------------------------
TEST_F(LowerRemillIntrinsicsTest, Undefined_LoweredToFreezePoison) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_undefined_64: () -> i64
  auto *undefFnTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto undefFn =
      M->getOrInsertFunction("__remill_undefined_64", undefFnTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);

  auto *mem = F->getArg(2);
  // %undef = call i64 @__remill_undefined_64()
  auto *call = B.CreateCall(undefFn, {});
  // Use the result so it's not dead.
  auto *dummy = B.CreateIntToPtr(call, ptrTy);
  auto *sel = B.CreateSelect(
      llvm::ConstantInt::getTrue(Ctx), dummy, mem);
  B.CreateRet(sel);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  runPass(F, omill::LowerCategories::Undefined);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Verify: no call to __remill_undefined_64, and a freeze instruction exists.
  bool foundUndefCall = false;
  bool foundFreeze = false;
  for (auto &I : F->getEntryBlock()) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction())
        if (callee->getName() == "__remill_undefined_64")
          foundUndefCall = true;
    }
    if (llvm::isa<llvm::FreezeInst>(&I))
      foundFreeze = true;
  }
  EXPECT_FALSE(foundUndefCall);
  EXPECT_TRUE(foundFreeze);
}

// ---------------------------------------------------------------------------
// Test 5: __remill_function_return → ret mem
// ---------------------------------------------------------------------------
TEST_F(LowerRemillIntrinsicsTest, Return_LoweredToRet) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Declare __remill_function_return: (ptr, i64, ptr) -> ptr
  auto *retFnTy =
      llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
  auto retFn =
      M->getOrInsertFunction("__remill_function_return", retFnTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);

  auto *state = F->getArg(0);
  auto *pc = F->getArg(1);
  auto *mem = F->getArg(2);

  // %ret = call ptr @__remill_function_return(ptr %state, i64 %pc, ptr %mem)
  auto *call = B.CreateCall(retFn, {state, pc, mem});
  // Dead code after the intrinsic (the pass must handle this).
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  runPass(F, omill::LowerCategories::Return);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Verify: no call to __remill_function_return; block ends with ret %mem.
  bool foundReturnCall = false;
  for (auto &I : F->getEntryBlock()) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction())
        if (callee->getName() == "__remill_function_return")
          foundReturnCall = true;
    }
  }
  EXPECT_FALSE(foundReturnCall);

  auto *term = F->getEntryBlock().getTerminator();
  ASSERT_NE(term, nullptr);
  auto *RI = llvm::dyn_cast<llvm::ReturnInst>(term);
  ASSERT_NE(RI, nullptr);
  EXPECT_EQ(RI->getReturnValue(), mem);
}

// ---------------------------------------------------------------------------
// Test 6: Selective category — only memory lowered, flags remain
// ---------------------------------------------------------------------------
TEST_F(LowerRemillIntrinsicsTest, SelectiveCategory_OnlyLowersSpecified) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *i1Ty = llvm::Type::getInt1Ty(Ctx);

  // Declare both memory and flag intrinsics.
  auto *readFnTy = llvm::FunctionType::get(i64Ty, {ptrTy, i64Ty}, false);
  auto readFn = M->getOrInsertFunction("__remill_read_memory_64", readFnTy);

  auto *flagFnTy = llvm::FunctionType::get(i1Ty, {i1Ty}, true);
  auto flagFn =
      M->getOrInsertFunction("__remill_flag_computation_zero", flagFnTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);

  auto *mem = F->getArg(2);
  auto *addr = llvm::ConstantInt::get(i64Ty, 0x3000);

  // Memory intrinsic call.
  auto *readCall = B.CreateCall(readFn, {mem, addr});
  // Flag intrinsic call.
  auto *flagCall = B.CreateCall(flagFn, {llvm::ConstantInt::getFalse(Ctx)});

  // Use both results.
  auto *readPtr = B.CreateIntToPtr(readCall, ptrTy);
  auto *result = B.CreateSelect(flagCall, readPtr, mem);
  B.CreateRet(result);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Run with ONLY Memory category.
  runPass(F, omill::LowerCategories::Memory);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // Memory call should be gone (lowered to load).
  // Flag call should still be present.
  bool foundReadCall = false;
  bool foundFlagCall = false;
  bool foundLoad = false;
  for (auto &I : F->getEntryBlock()) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction()) {
        if (callee->getName() == "__remill_read_memory_64")
          foundReadCall = true;
        if (callee->getName() == "__remill_flag_computation_zero")
          foundFlagCall = true;
      }
    }
    if (llvm::isa<llvm::LoadInst>(&I))
      foundLoad = true;
  }
  EXPECT_FALSE(foundReadCall);
  EXPECT_TRUE(foundFlagCall);
  EXPECT_TRUE(foundLoad);
}

TEST_F(LowerRemillIntrinsicsTest, FpuHelpersLowerToInternalStateWithoutDecls) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);

  auto *testTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *setRoundTy = llvm::FunctionType::get(i32Ty, {i32Ty}, false);
  auto *getRoundTy = llvm::FunctionType::get(i32Ty, {}, false);
  auto testFn =
      M->getOrInsertFunction("__remill_fpu_exception_test", testTy);
  auto clearFn =
      M->getOrInsertFunction("__remill_fpu_exception_clear", testTy);
  auto raiseFn =
      M->getOrInsertFunction("__remill_fpu_exception_raise", testTy);
  auto setRoundFn =
      M->getOrInsertFunction("__remill_fpu_set_rounding", setRoundTy);
  auto getRoundFn =
      M->getOrInsertFunction("__remill_fpu_get_rounding", getRoundTy);

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);
  auto *mem = F->getArg(2);

  auto *clearCall = B.CreateCall(clearFn, {B.getInt32(0x7f)});
  auto *raiseCall = B.CreateCall(raiseFn, {B.getInt32(0x3)});
  auto *setRoundCall = B.CreateCall(setRoundFn, {B.getInt32(2)});
  auto *testCall = B.CreateCall(testFn, {B.getInt32(0x7f)});
  auto *getRoundCall = B.CreateCall(getRoundFn, {});
  auto *combined = B.CreateAdd(testCall, getRoundCall);
  auto *combined2 = B.CreateAdd(combined, clearCall);
  auto *combined3 = B.CreateAdd(combined2, raiseCall);
  auto *combined4 = B.CreateAdd(combined3, setRoundCall);
  (void)combined4;
  B.CreateRet(mem);

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  runPass(F, omill::LowerCategories::HyperCalls);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  EXPECT_EQ(M->getFunction("fetestexcept"), nullptr);
  EXPECT_EQ(M->getFunction("feclearexcept"), nullptr);
  EXPECT_EQ(M->getFunction("feraiseexcept"), nullptr);
  EXPECT_EQ(M->getFunction("fesetround"), nullptr);
  EXPECT_EQ(M->getFunction("fegetround"), nullptr);

  auto *exceptState = M->getNamedGlobal("__omill_fenv_except_state");
  auto *roundState = M->getNamedGlobal("__omill_fenv_rounding_mode");
  ASSERT_NE(exceptState, nullptr);
  ASSERT_NE(roundState, nullptr);

  bool sawLoad = false;
  bool sawStore = false;
  bool sawRemillCall = false;
  for (auto &I : *BB) {
    sawLoad |= llvm::isa<llvm::LoadInst>(&I);
    sawStore |= llvm::isa<llvm::StoreInst>(&I);
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction();
          callee && callee->getName().starts_with("__remill_fpu_")) {
        sawRemillCall = true;
      }
    }
  }
  EXPECT_TRUE(sawLoad);
  EXPECT_TRUE(sawStore);
  EXPECT_FALSE(sawRemillCall);
}

TEST_F(LowerRemillIntrinsicsTest, FP80NearbyIntLowersWithoutResidualIntrinsic) {
  auto M = makeModule();
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *fp80Ty = llvm::Type::getX86_FP80Ty(Ctx);
  auto *nearbyDecl =
      llvm::Intrinsic::getOrInsertDeclaration(M.get(), llvm::Intrinsic::nearbyint,
                                              {fp80Ty});

  auto *F = createLiftedFn(*M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(BB);
  auto *rounded =
      B.CreateCall(nearbyDecl, {llvm::ConstantFP::get(fp80Ty, 1.5)});
  (void)B.CreateFNeg(rounded);
  B.CreateRet(F->getArg(2));

  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
  runPass(F, omill::LowerCategories::HyperCalls);
  ASSERT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  bool sawNearbyIntrinsic = false;
  bool sawInlineAsm = false;
  for (auto &I : *BB) {
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      if (auto *callee = CI->getCalledFunction()) {
        if (callee->getName() == "llvm.nearbyint.f80")
          sawNearbyIntrinsic = true;
      }
      sawInlineAsm |= CI->isInlineAsm();
    }
  }
  EXPECT_FALSE(sawNearbyIntrinsic);
  EXPECT_TRUE(sawInlineAsm);
  EXPECT_EQ(M->getFunction("nearbyintl"), nullptr);
}

}  // namespace

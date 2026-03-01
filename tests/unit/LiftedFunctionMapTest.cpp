#include "omill/Analysis/LiftedFunctionMap.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class LiftedFunctionMapTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// The remill lifted signature: (ptr, i64, ptr) -> ptr.
  llvm::FunctionType *liftedTy() {
    auto *Ptr = llvm::PointerType::getUnqual(Ctx);
    auto *I64 = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(Ptr, {Ptr, I64, Ptr}, false);
  }

  /// A wrong signature: void(void).
  llvm::FunctionType *wrongTy() {
    return llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
  }

  /// Create a function with the given name and type, adding a trivial body
  /// (single basic block with unreachable) so isLiftedFunction sees it as
  /// a definition, not a declaration.
  llvm::Function *addDefinedFunc(llvm::Module &M, llvm::StringRef Name,
                                 llvm::FunctionType *FTy) {
    auto *F = llvm::Function::Create(FTy, llvm::GlobalValue::ExternalLinkage,
                                     Name, &M);
    auto *BB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(BB);
    if (FTy->getReturnType()->isVoidTy()) {
      B.CreateRetVoid();
    } else {
      B.CreateRet(llvm::UndefValue::get(FTy->getReturnType()));
    }
    return F;
  }

  /// Run LiftedFunctionAnalysis on the module and return the result.
  omill::LiftedFunctionMap runAnalysis(llvm::Module &M) {
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
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });
    return MAM.getResult<omill::LiftedFunctionAnalysis>(M);
  }
};

// ===----------------------------------------------------------------------===
// Test 1: Empty module produces empty map
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, EmptyModule) {
  llvm::Module M("empty", Ctx);
  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 0u);
}

// ===----------------------------------------------------------------------===
// Test 2: Single lifted function is discovered
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, SingleLiftedFunction) {
  llvm::Module M("single", Ctx);
  auto *F = addDefinedFunc(M, "sub_1000", liftedTy());

  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 1u);
  EXPECT_EQ(map.lookup(0x1000), F);
}

// ===----------------------------------------------------------------------===
// Test 3: Multiple lifted functions are all found
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, MultipleLiftedFunctions) {
  llvm::Module M("multi", Ctx);
  auto *F1 = addDefinedFunc(M, "sub_1000", liftedTy());
  auto *F2 = addDefinedFunc(M, "sub_2000", liftedTy());
  auto *F3 = addDefinedFunc(M, "sub_ABCD", liftedTy());

  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 3u);
  EXPECT_EQ(map.lookup(0x1000), F1);
  EXPECT_EQ(map.lookup(0x2000), F2);
  EXPECT_EQ(map.lookup(0xABCD), F3);
}

// ===----------------------------------------------------------------------===
// Test 4: __remill_ prefixed functions are skipped
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, SkipsRemillPrefixed) {
  llvm::Module M("remill", Ctx);
  addDefinedFunc(M, "__remill_foo", liftedTy());

  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 0u);
}

// ===----------------------------------------------------------------------===
// Test 5: __omill_ prefixed functions are skipped
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, SkipsOmillPrefixed) {
  llvm::Module M("omill", Ctx);
  addDefinedFunc(M, "__omill_bar", liftedTy());

  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 0u);
}

// ===----------------------------------------------------------------------===
// Test 6: Functions ending with _native are skipped
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, SkipsNativeSuffix) {
  llvm::Module M("native", Ctx);
  addDefinedFunc(M, "sub_5000_native", liftedTy());

  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 0u);
}

// ===----------------------------------------------------------------------===
// Test 7: Function with wrong signature is skipped
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, SkipsWrongSignature) {
  llvm::Module M("wrongsig", Ctx);
  addDefinedFunc(M, "sub_5000", wrongTy());

  auto map = runAnalysis(M);
  EXPECT_EQ(map.size(), 0u);
}

// ===----------------------------------------------------------------------===
// Test 8: isLifted returns true for lifted, false for non-lifted
// ===----------------------------------------------------------------------===

TEST_F(LiftedFunctionMapTest, IsLiftedQuery) {
  llvm::Module M("query", Ctx);
  auto *Lifted = addDefinedFunc(M, "sub_3000", liftedTy());
  auto *NotLifted = addDefinedFunc(M, "helper_func", wrongTy());

  auto map = runAnalysis(M);
  EXPECT_TRUE(map.isLifted(Lifted));
  EXPECT_FALSE(map.isLifted(NotLifted));
}

}  // namespace

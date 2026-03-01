#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/private/CustomABI.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class CustomABIObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_cabi", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create an internal function with the given type. If add_body is true,
  /// adds an entry block that adds the first two args (or returns a constant)
  /// and returns the result.
  llvm::Function *createInternalFunction(llvm::Module &M,
                                         const std::string &name,
                                         llvm::FunctionType *fnTy,
                                         bool addBody = true) {
    auto *F = llvm::Function::Create(fnTy, llvm::Function::InternalLinkage,
                                     name, M);
    if (addBody) {
      auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
      llvm::IRBuilder<> B(entry);
      if (F->arg_size() >= 2) {
        auto *sum = B.CreateAdd(F->getArg(0), F->getArg(1), "sum");
        B.CreateRet(sum);
      } else if (F->arg_size() == 1) {
        B.CreateRet(F->getArg(0));
      } else {
        B.CreateRet(llvm::ConstantInt::get(fnTy->getReturnType(), 0));
      }
    }
    return F;
  }

  /// Create an external function that calls the callee with dummy args.
  llvm::Function *createCaller(llvm::Module &M, const std::string &callerName,
                               llvm::Function *callee) {
    auto *retTy = callee->getReturnType();
    auto *callerTy = llvm::FunctionType::get(retTy, {}, false);
    auto *caller = llvm::Function::Create(
        callerTy, llvm::Function::ExternalLinkage, callerName, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);

    llvm::SmallVector<llvm::Value *, 8> args;
    for (unsigned i = 0; i < callee->arg_size(); ++i) {
      auto *paramTy = callee->getFunctionType()->getParamType(i);
      args.push_back(llvm::Constant::getNullValue(paramTy));
    }
    auto *result = B.CreateCall(callee, args, "res");
    B.CreateRet(result);
    return caller;
  }
};

// 1. Basic — transform internal function, verify module valid.
TEST_F(CustomABIObfTest, Basic) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
  auto *foo = createInternalFunction(*M, "foo", fnTy);
  createCaller(*M, "caller", foo);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::customABIModule(*M, 12345);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Original "foo" with exactly 2 params should no longer exist.
  bool foundOriginal = false;
  for (auto &F : *M) {
    if (F.getName() == "foo" && F.arg_size() == 2)
      foundOriginal = true;
  }
  EXPECT_FALSE(foundOriginal);
}

// 2. SkipsDeclaration — declared function should be unchanged.
TEST_F(CustomABIObfTest, SkipsDeclaration) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *decl =
      createInternalFunction(*M, "declared_fn", fnTy, /*addBody=*/false);

  ASSERT_TRUE(decl->isDeclaration());

  ollvm::customABIModule(*M, 42);

  auto *after = M->getFunction("declared_fn");
  ASSERT_NE(after, nullptr);
  EXPECT_TRUE(after->isDeclaration());
  EXPECT_EQ(after->arg_size(), 1u);
}

// 3. SkipsVarArgs — vararg function should be unchanged.
TEST_F(CustomABIObfTest, SkipsVarArgs) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, true);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::InternalLinkage,
                                   "varfn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(0));

  // Need a caller for completeness.
  auto *callerTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto *caller = llvm::Function::Create(
      callerTy, llvm::Function::ExternalLinkage, "caller", *M);
  auto *cEntry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> CB(cEntry);
  auto *res = CB.CreateCall(fnTy, F, {llvm::ConstantInt::get(i64Ty, 0)}, "r");
  CB.CreateRet(res);

  ollvm::customABIModule(*M, 42);

  auto *after = M->getFunction("varfn");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->arg_size(), 1u);
}

// 4. SkipsExternal — external linkage function should be unchanged.
TEST_F(CustomABIObfTest, SkipsExternal) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "ext_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *sum = B.CreateAdd(F->getArg(0), F->getArg(1), "sum");
  B.CreateRet(sum);

  createCaller(*M, "caller", F);

  ollvm::customABIModule(*M, 42);

  auto *after = M->getFunction("ext_fn");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->arg_size(), 2u);
}

// 5. ParamShuffle — 4-param function should still have >= 4 params after.
TEST_F(CustomABIObfTest, ParamShuffle) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy =
      llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty, i64Ty, i64Ty}, false);
  auto *F = createInternalFunction(*M, "shuffle_fn", fnTy);
  createCaller(*M, "caller", F);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::customABIModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Find the replacement function — original name may be gone or reused.
  // At least one non-declaration internal function should have >= 4 params.
  bool found = false;
  for (auto &Fn : *M) {
    if (!Fn.isDeclaration() && Fn.hasInternalLinkage() &&
        Fn.arg_size() >= 4) {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found);
}

// 6. BogusParams — should have MORE params than original 2.
TEST_F(CustomABIObfTest, BogusParams) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
  auto *F = createInternalFunction(*M, "bogus_fn", fnTy);
  createCaller(*M, "caller", F);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::customABIModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // The replacement internal function should have more than 2 params.
  bool foundLarger = false;
  for (auto &Fn : *M) {
    if (!Fn.isDeclaration() && Fn.hasInternalLinkage() &&
        Fn.arg_size() > 2) {
      foundLarger = true;
      break;
    }
  }
  EXPECT_TRUE(foundLarger);
}

// 7. ReturnXOR — return type should still be i32.
TEST_F(CustomABIObfTest, ReturnXOR) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, {i64Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::InternalLinkage,
                                   "retxor_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *trunc = B.CreateTrunc(F->getArg(0), i32Ty, "t");
  B.CreateRet(trunc);

  createCaller(*M, "caller", F);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::customABIModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Find the replacement function — return type should still be i32.
  bool foundI32Ret = false;
  for (auto &Fn : *M) {
    if (!Fn.isDeclaration() && Fn.hasInternalLinkage() &&
        Fn.getReturnType() == i32Ty) {
      foundI32Ret = true;
      break;
    }
  }
  EXPECT_TRUE(foundI32Ret);
}

// 8. FilterMinInstructions — trivial function skipped by filter.
TEST_F(CustomABIObfTest, FilterMinInstructions) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = createInternalFunction(*M, "tiny_fn", fnTy);
  createCaller(*M, "caller", F);

  ollvm::FilterConfig cfg;
  cfg.min_instructions = 100;
  ollvm::customABIModule(*M, 42, cfg);

  auto *after = M->getFunction("tiny_fn");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->arg_size(), 1u);
}

// 9. Deterministic — same seed produces identical results.
TEST_F(CustomABIObfTest, Deterministic) {
  auto buildModule = [&]() {
    auto M = createModule();
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    createInternalFunction(*M, "det_fn", fnTy);
    createCaller(*M, "caller", M->getFunction("det_fn"));
    return M;
  };

  auto M1 = buildModule();
  ollvm::customABIModule(*M1, 42);
  ASSERT_FALSE(llvm::verifyModule(*M1, &llvm::errs()));

  auto M2 = buildModule();
  ollvm::customABIModule(*M2, 42);
  ASSERT_FALSE(llvm::verifyModule(*M2, &llvm::errs()));

  // Compare function signatures — collect sorted list of (name, arg_size).
  auto collectSigs =
      [](llvm::Module &M) -> std::vector<std::pair<std::string, unsigned>> {
    std::vector<std::pair<std::string, unsigned>> sigs;
    for (auto &F : M) {
      if (!F.isDeclaration())
        sigs.emplace_back(F.getName().str(), F.arg_size());
    }
    std::sort(sigs.begin(), sigs.end());
    return sigs;
  };

  EXPECT_EQ(collectSigs(*M1), collectSigs(*M2));
}

// 10. SkipsAddressTaken — function with address stored to global is unchanged.
TEST_F(CustomABIObfTest, SkipsAddressTaken) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty}, false);
  auto *F = createInternalFunction(*M, "addr_fn", fnTy);

  // Store address of F into a global — makes it address-taken.
  auto *ptrTy = llvm::PointerType::getUnqual(Ctx);
  new llvm::GlobalVariable(*M, ptrTy, /*isConstant=*/true,
                            llvm::GlobalValue::InternalLinkage, F,
                            "fn_ptr");

  // Also need a caller so it has call sites.
  createCaller(*M, "caller", F);

  ollvm::customABIModule(*M, 42);

  auto *after = M->getFunction("addr_fn");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->arg_size(), 1u);
}

}  // namespace

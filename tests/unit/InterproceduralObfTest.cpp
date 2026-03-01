#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/private/InterproceduralObfuscation.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class InterproceduralObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_interprocedural", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create an internal function with the given return type and parameter
  /// types.  The body does simple arithmetic on the first two params (or uses
  /// a constant) and returns a value.
  llvm::Function *createInternalFn(llvm::Module &M, const std::string &name,
                                   llvm::Type *retTy,
                                   llvm::ArrayRef<llvm::Type *> paramTys) {
    auto *fnTy = llvm::FunctionType::get(retTy, paramTys, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::InternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);

    if (paramTys.size() >= 2 && retTy->isIntegerTy()) {
      auto *sum = B.CreateAdd(F->getArg(0), F->getArg(1), "sum");
      auto *prod = B.CreateMul(sum, F->getArg(0), "prod");
      B.CreateRet(prod);
    } else if (paramTys.size() >= 1 && retTy->isIntegerTy()) {
      B.CreateRet(F->getArg(0));
    } else {
      B.CreateRet(llvm::ConstantInt::get(retTy, 42));
    }
    return F;
  }

  /// Create an external function that calls the given callee with the
  /// provided arguments (or default zero values).
  llvm::Function *createCaller(llvm::Module &M, const std::string &callerName,
                               llvm::Function *callee,
                               llvm::ArrayRef<llvm::Value *> args = {}) {
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *callerFnTy = llvm::FunctionType::get(voidTy, false);
    auto *caller = llvm::Function::Create(
        callerFnTy, llvm::Function::ExternalLinkage, callerName, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);

    if (args.empty()) {
      // Build default zero arguments.
      llvm::SmallVector<llvm::Value *, 4> defaultArgs;
      for (auto &param : callee->getFunctionType()->params())
        defaultArgs.push_back(llvm::Constant::getNullValue(param));
      B.CreateCall(callee, defaultArgs);
    } else {
      B.CreateCall(callee, args);
    }
    B.CreateRetVoid();
    return caller;
  }

  /// Check if any function in the module has a name containing the given
  /// substring.
  bool hasFunction(llvm::Module &M, llvm::StringRef nameSubstring) {
    for (auto &F : M) {
      if (F.getName().contains(nameSubstring))
        return true;
    }
    return false;
  }

  /// Check if the module has any global variables.
  bool hasGlobalVariable(llvm::Module &M) {
    return !M.global_empty();
  }

  /// Serialize module IR to a string for comparison.
  std::string serializeModule(llvm::Module &M) {
    std::string buf;
    llvm::raw_string_ostream os(buf);
    M.print(os, nullptr);
    return buf;
  }
};

// ─── Test 1: Basic ──────────────────────────────────────────────────────

TEST_F(InterproceduralObfTest, Basic) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  auto *f1 = createInternalFn(*M, "fn_a", i64Ty, {i64Ty, i64Ty});
  auto *f2 = createInternalFn(*M, "fn_b", i64Ty, {i64Ty, i64Ty});
  auto *f3 = createInternalFn(*M, "fn_c", i64Ty, {i64Ty, i64Ty});

  createCaller(*M, "caller_a", f1);
  createCaller(*M, "caller_b", f2);
  createCaller(*M, "caller_c", f3);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::interproceduralObfuscationModule(*M, 42);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// ─── Test 2: MergeFunctions ─────────────────────────────────────────────

TEST_F(InterproceduralObfTest, MergeFunctions) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  auto *f1 = createInternalFn(*M, "merge_a", i64Ty, {i64Ty, i64Ty});
  auto *f2 = createInternalFn(*M, "merge_b", i64Ty, {i64Ty, i64Ty});
  auto *f3 = createInternalFn(*M, "merge_c", i64Ty, {i64Ty, i64Ty});

  // All called from main so they have callers.
  auto *voidTy = llvm::Type::getVoidTy(Ctx);
  auto *mainTy = llvm::FunctionType::get(voidTy, false);
  auto *mainFn = llvm::Function::Create(
      mainTy, llvm::Function::ExternalLinkage, "main", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mainFn);
  llvm::IRBuilder<> B(entry);
  auto *zero = llvm::ConstantInt::get(i64Ty, 0);
  B.CreateCall(f1, {zero, zero});
  B.CreateCall(f2, {zero, zero});
  B.CreateCall(f3, {zero, zero});
  B.CreateRetVoid();

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::interproceduralObfuscationModule(*M, 42);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  EXPECT_TRUE(hasFunction(*M, ".merged."));
}

// ─── Test 3: CallIndirection ────────────────────────────────────────────

TEST_F(InterproceduralObfTest, CallIndirection) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);

  // Two functions with DIFFERENT signatures so they cannot be merged.
  auto *f1 = createInternalFn(*M, "ind_a", i64Ty, {i64Ty, i64Ty});
  auto *f2 = createInternalFn(*M, "ind_b", i32Ty, {i32Ty});

  createCaller(*M, "caller_a", f1);
  createCaller(*M, "caller_b", f2);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // No globals before the pass.
  EXPECT_TRUE(M->global_empty());

  ollvm::interproceduralObfuscationModule(*M, 42);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // The call indirection table should have been created as a global variable.
  EXPECT_TRUE(hasGlobalVariable(*M));
}

// ─── Test 4: ExternalSkip ───────────────────────────────────────────────

TEST_F(InterproceduralObfTest, ExternalSkip) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // External linkage → not eligible.
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
  auto *f1 = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "ext_a", *M);
  auto *f2 = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "ext_b", *M);

  // Give them bodies.
  for (auto *F : {f1, f2}) {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(B.CreateAdd(F->getArg(0), F->getArg(1), "sum"));
  }

  // Add callers so the only skip reason is external linkage.
  createCaller(*M, "caller_a", f1);
  createCaller(*M, "caller_b", f2);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  unsigned fnCountBefore = M->getFunctionList().size();

  ollvm::interproceduralObfuscationModule(*M, 42);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // No new functions created — pass skipped external functions.
  EXPECT_EQ(M->getFunctionList().size(), fnCountBefore);
  EXPECT_FALSE(hasFunction(*M, ".merged."));
}

// ─── Test 5: SingleFunction ─────────────────────────────────────────────

TEST_F(InterproceduralObfTest, SingleFunction) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  auto *f1 = createInternalFn(*M, "only_fn", i64Ty, {i64Ty, i64Ty});
  createCaller(*M, "caller", f1);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  unsigned fnCountBefore = M->getFunctionList().size();

  ollvm::interproceduralObfuscationModule(*M, 42);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // Single function in the group — nothing to merge.
  EXPECT_FALSE(hasFunction(*M, ".merged."));
}

// ─── Test 6: Deterministic ──────────────────────────────────────────────

TEST_F(InterproceduralObfTest, Deterministic) {
  auto buildModule = [&]() {
    auto M = createModule();
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *f1 = createInternalFn(*M, "det_a", i64Ty, {i64Ty, i64Ty});
    auto *f2 = createInternalFn(*M, "det_b", i64Ty, {i64Ty, i64Ty});
    auto *f3 = createInternalFn(*M, "det_c", i64Ty, {i64Ty, i64Ty});
    createCaller(*M, "caller_a", f1);
    createCaller(*M, "caller_b", f2);
    createCaller(*M, "caller_c", f3);
    return M;
  };

  auto M1 = buildModule();
  auto M2 = buildModule();

  ollvm::interproceduralObfuscationModule(*M1, 100);
  ollvm::interproceduralObfuscationModule(*M2, 100);

  EXPECT_FALSE(llvm::verifyModule(*M1, &llvm::errs()));
  EXPECT_FALSE(llvm::verifyModule(*M2, &llvm::errs()));
  EXPECT_EQ(serializeModule(*M1), serializeModule(*M2));
}

// ─── Test 7: FilterMinInstructions ──────────────────────────────────────

TEST_F(InterproceduralObfTest, FilterMinInstructions) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Trivial functions with very few instructions.
  auto *f1 = createInternalFn(*M, "small_a", i64Ty, {i64Ty, i64Ty});
  auto *f2 = createInternalFn(*M, "small_b", i64Ty, {i64Ty, i64Ty});
  auto *f3 = createInternalFn(*M, "small_c", i64Ty, {i64Ty, i64Ty});

  createCaller(*M, "caller_a", f1);
  createCaller(*M, "caller_b", f2);
  createCaller(*M, "caller_c", f3);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  unsigned fnCountBefore = M->getFunctionList().size();

  ollvm::FilterConfig cfg;
  cfg.min_instructions = 100;
  ollvm::interproceduralObfuscationModule(*M, 42, cfg);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // Functions too small → skipped by filter.
  EXPECT_EQ(M->getFunctionList().size(), fnCountBefore);
  EXPECT_FALSE(hasFunction(*M, ".merged."));
}

// ─── Test 8: SkipsNoCallers ─────────────────────────────────────────────

TEST_F(InterproceduralObfTest, SkipsNoCallers) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Internal functions with NO callers — dead code.
  createInternalFn(*M, "dead_a", i64Ty, {i64Ty, i64Ty});
  createInternalFn(*M, "dead_b", i64Ty, {i64Ty, i64Ty});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  unsigned fnCountBefore = M->getFunctionList().size();

  ollvm::interproceduralObfuscationModule(*M, 42);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // No callers → not eligible, should be unchanged.
  EXPECT_EQ(M->getFunctionList().size(), fnCountBefore);
  EXPECT_FALSE(hasFunction(*M, ".merged."));
}

} // namespace

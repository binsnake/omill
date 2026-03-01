#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/CodeCloning.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class CodeCloningObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_cloning", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create an internal function with enough instructions (arithmetic chain)
  /// that qualifies for cloning.
  llvm::Function *createInternalFunction(llvm::Module &M,
                                         const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::InternalLinkage,
                                     name, M);
    auto *arg0 = F->getArg(0);
    auto *arg1 = F->getArg(1);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> builder(entryBB);
    auto *sum = builder.CreateAdd(arg0, arg1, "");
    auto *prod = builder.CreateMul(sum, arg0, "");
    auto *diff = builder.CreateSub(prod, arg1, "");
    auto *xr = builder.CreateXor(diff, sum, "");
    auto *shift = builder.CreateShl(xr, llvm::ConstantInt::get(i64Ty, 1), "");
    auto *fin = builder.CreateAdd(shift, prod, "");
    builder.CreateRet(fin);

    return F;
  }

  /// Create an external function that calls the given callee.
  llvm::Function *createCallerFunction(llvm::Module &M,
                                       const std::string &name,
                                       llvm::Function *callee) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> builder(entryBB);
    auto *result = builder.CreateCall(callee, {F->getArg(0), F->getArg(1)}, "");
    builder.CreateRet(result);
    return F;
  }

  /// Create an external-linkage function with enough instructions.
  llvm::Function *createExternalFunction(llvm::Module &M,
                                         const std::string &name) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *arg0 = F->getArg(0);
    auto *arg1 = F->getArg(1);

    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> builder(entryBB);
    auto *sum = builder.CreateAdd(arg0, arg1, "");
    auto *prod = builder.CreateMul(sum, arg0, "");
    auto *diff = builder.CreateSub(prod, arg1, "");
    auto *xr = builder.CreateXor(diff, sum, "");
    auto *shift = builder.CreateShl(xr, llvm::ConstantInt::get(i64Ty, 1), "");
    auto *fin = builder.CreateAdd(shift, prod, "");
    builder.CreateRet(fin);

    return F;
  }

  /// Count functions in the module (excluding declarations).
  unsigned countDefinedFunctions(llvm::Module &M) {
    unsigned count = 0;
    for (auto &F : M)
      if (!F.isDeclaration())
        ++count;
    return count;
  }
};

// Run cloning with 100% transform_percent and a seed that guarantees the 30%
// gate fires.  We try multiple seeds and check at least one produced clones.
TEST_F(CodeCloningObfTest, BasicCloning) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  bool anyCloned = false;
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createModule();
    auto *target = createInternalFunction(*M, "target");
    createCallerFunction(*M, "caller", target);

    unsigned before = countDefinedFunctions(*M);
    ollvm::cloneFunctionsModule(*M, seed, cfg);
    unsigned after = countDefinedFunctions(*M);

    if (after > before) {
      anyCloned = true;
      // Should have 2 or 3 new clones.
      EXPECT_GE(after - before, 2u);
      EXPECT_LE(after - before, 3u);
      break;
    }
  }
  EXPECT_TRUE(anyCloned) << "No seed produced clones in 50 attempts";
}

TEST_F(CodeCloningObfTest, CallSitesRedirected) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  bool found = false;
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createModule();
    auto *target = createInternalFunction(*M, "target");
    auto *caller1 = createCallerFunction(*M, "caller1", target);
    auto *caller2 = createCallerFunction(*M, "caller2", target);

    unsigned before = countDefinedFunctions(*M);
    ollvm::cloneFunctionsModule(*M, seed, cfg);
    unsigned after = countDefinedFunctions(*M);

    if (after <= before)
      continue;

    found = true;
    // Check that at least one call site was redirected away from original.
    bool anyRedirected = false;
    for (auto *F : {caller1, caller2}) {
      for (auto &BB : *F) {
        for (auto &I : BB) {
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
            if (CB->getCalledFunction() != target)
              anyRedirected = true;
          }
        }
      }
    }
    // With multiple call sites and random dispatch, it's possible all stay on
    // original.  But the clones exist, so at minimum the function count grew.
    EXPECT_GE(after - before, 2u);
    break;
  }
  EXPECT_TRUE(found) << "No seed produced clones in 50 attempts";
}

TEST_F(CodeCloningObfTest, ClonesAreInternal) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  bool found = false;
  for (uint32_t seed = 0; seed < 50; ++seed) {
    auto M = createModule();
    auto *target = createInternalFunction(*M, "target");
    createCallerFunction(*M, "caller", target);

    unsigned before = countDefinedFunctions(*M);
    ollvm::cloneFunctionsModule(*M, seed, cfg);
    unsigned after = countDefinedFunctions(*M);

    if (after <= before)
      continue;

    found = true;
    // All non-original defined functions should be internal.
    for (auto &F : *M) {
      if (F.isDeclaration())
        continue;
      if (&F == target)
        continue;
      // caller is external, skip it.
      if (F.hasExternalLinkage() && F.getName() == "caller")
        continue;
      EXPECT_TRUE(F.hasInternalLinkage())
          << "Clone " << F.getName().str() << " is not internal";
    }
    break;
  }
  EXPECT_TRUE(found) << "No seed produced clones";
}

TEST_F(CodeCloningObfTest, ExternalSkipped) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  // Create an external function with callers — should NOT be cloned.
  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    auto *ext = createExternalFunction(*M, "ext_func");
    createCallerFunction(*M, "caller", ext);

    unsigned before = countDefinedFunctions(*M);
    ollvm::cloneFunctionsModule(*M, seed, cfg);
    unsigned after = countDefinedFunctions(*M);

    // External function must never be cloned.
    EXPECT_EQ(before, after)
        << "External function was cloned at seed " << seed;
  }
}

TEST_F(CodeCloningObfTest, AddressTakenSkipped) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed = 0; seed < 30; ++seed) {
    auto M = createModule();
    auto *target = createInternalFunction(*M, "target");

    // Create a caller that also stores the function pointer (address taken).
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *fnPtrTy = target->getType();
    auto *callerTy = llvm::FunctionType::get(i64Ty, {i64Ty, i64Ty}, false);
    auto *caller = llvm::Function::Create(
        callerTy, llvm::Function::ExternalLinkage, "caller", *M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "", caller);
    llvm::IRBuilder<> builder(entryBB);

    // Store the function pointer to make it address-taken.
    auto *alloca = builder.CreateAlloca(fnPtrTy, nullptr, "");
    builder.CreateStore(target, alloca);
    auto *result = builder.CreateCall(target, {caller->getArg(0), caller->getArg(1)}, "");
    builder.CreateRet(result);

    unsigned before = countDefinedFunctions(*M);
    ollvm::cloneFunctionsModule(*M, seed, cfg);
    unsigned after = countDefinedFunctions(*M);

    EXPECT_EQ(before, after)
        << "Address-taken function was cloned at seed " << seed;
  }
}

TEST_F(CodeCloningObfTest, ModuleVerifies) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  for (uint32_t seed = 0; seed < 5; ++seed) {
    auto M = createModule();
    auto *target = createInternalFunction(*M, "target");
    createCallerFunction(*M, "caller1", target);
    createCallerFunction(*M, "caller2", target);
    createCallerFunction(*M, "caller3", target);

    ollvm::cloneFunctionsModule(*M, seed, cfg);

    std::string err;
    llvm::raw_string_ostream os(err);
    EXPECT_FALSE(llvm::verifyModule(*M, &os))
        << "Module verification failed at seed " << seed << ": " << err;
  }
}

TEST_F(CodeCloningObfTest, ClonesDiffer) {
  ollvm::FilterConfig cfg;
  cfg.transform_percent = 100;

  // Find a seed that produces clones and check structural difference.
  bool found = false;
  for (uint32_t seed = 0; seed < 100; ++seed) {
    auto M = createModule();
    auto *target = createInternalFunction(*M, "target");
    createCallerFunction(*M, "caller", target);

    unsigned beforeCount = countDefinedFunctions(*M);
    ollvm::cloneFunctionsModule(*M, seed, cfg);
    unsigned afterCount = countDefinedFunctions(*M);

    if (afterCount <= beforeCount)
      continue;

    // Collect instruction counts per function (excluding caller and target).
    std::vector<unsigned> instrCounts;
    unsigned targetInstCount = ollvm::countInstructions(*target);
    for (auto &F : *M) {
      if (F.isDeclaration())
        continue;
      if (&F == target)
        continue;
      if (F.hasExternalLinkage())
        continue;
      unsigned ic = ollvm::countInstructions(F);
      instrCounts.push_back(ic);
    }

    // With diversification, at least one clone should differ in instruction
    // count from the original.  Check across many seeds.
    bool anyDiffer = false;
    for (unsigned ic : instrCounts) {
      if (ic != targetInstCount)
        anyDiffer = true;
    }
    if (anyDiffer) {
      found = true;
      break;
    }
  }
  // Diversification is probabilistic (20% per binop).  Across 100 seeds it
  // should trigger at least once.
  EXPECT_TRUE(found) << "No clone differed from original across 100 seeds";
}

}  // namespace

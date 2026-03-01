#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/StringEncryption.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class StringEncryptionObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_strenc", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a global constant string and return it.
  llvm::GlobalVariable *createGlobalString(llvm::Module &M,
                                           const std::string &name,
                                           const std::string &value) {
    auto *init = llvm::ConstantDataArray::getString(Ctx, value,
                                                    /*AddNull=*/true);
    auto *gv = new llvm::GlobalVariable(
        M, init->getType(), /*isConstant=*/true,
        llvm::GlobalValue::PrivateLinkage, init, name);
    return gv;
  }

  /// Create a global constant byte array (no null terminator).
  llvm::GlobalVariable *createGlobalByteArray(llvm::Module &M,
                                              const std::string &name,
                                              llvm::ArrayRef<uint8_t> data) {
    auto *init = llvm::ConstantDataArray::get(Ctx, data);
    auto *gv = new llvm::GlobalVariable(
        M, init->getType(), /*isConstant=*/true,
        llvm::GlobalValue::PrivateLinkage, init, name);
    return gv;
  }

  /// Create a function that uses a global via GEP + load of first byte.
  llvm::Function *createFunctionUsingGlobal(llvm::Module &M,
                                            const std::string &fnName,
                                            llvm::GlobalVariable *gv) {
    auto *i8Ty = llvm::Type::getInt8Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i8Ty, {}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     fnName, M);
    auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> builder(entryBB);

    auto *gep = builder.CreateConstInBoundsGEP2_32(
        gv->getValueType(), gv, 0, 0, "ptr");
    auto *load = builder.CreateLoad(i8Ty, gep, "ch");
    builder.CreateRet(load);
    return F;
  }

  /// Count AllocaInst in a function.
  unsigned countAllocas(llvm::Function &F) {
    unsigned count = 0;
    for (auto &BB : F)
      for (auto &I : BB)
        if (llvm::isa<llvm::AllocaInst>(&I))
          ++count;
    return count;
  }

  /// Check if any block in the function contains a PHI node (excludes entry).
  bool hasPHINodes(llvm::Function &F) {
    for (auto &BB : F) {
      if (&BB == &F.getEntryBlock())
        continue;
      if (BB.phis().begin() != BB.phis().end())
        return true;
    }
    return false;
  }

  /// Check if a global variable still exists in the module.
  bool globalExists(llvm::Module &M, const std::string &name) {
    return M.getNamedGlobal(name) != nullptr;
  }

  std::string serializeModule(llvm::Module &M) {
    std::string str;
    llvm::raw_string_ostream os(str);
    M.print(os, nullptr);
    return str;
  }
};

TEST_F(StringEncryptionObfTest, BasicEncryption) {
  auto M = createModule();
  auto *gv = createGlobalString(*M, "hello_str", "Hello, World!");
  createFunctionUsingGlobal(*M, "use_fn", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Original global should be removed (all uses replaced).
  EXPECT_FALSE(globalExists(*M, "hello_str"))
      << "Original string global should be removed after encryption";

  // The function should now have an alloca for the decryption buffer.
  auto *F = M->getFunction("use_fn");
  ASSERT_NE(F, nullptr);
  EXPECT_GE(countAllocas(*F), 1u)
      << "Function should have alloca for decryption buffer";
}

TEST_F(StringEncryptionObfTest, ShortStringSkipped) {
  auto M = createModule();
  // "abc" + null = 4 bytes, which is <= 4 threshold.
  auto *gv = createGlobalString(*M, "short_str", "abc");
  createFunctionUsingGlobal(*M, "use_fn", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // String with 4 bytes (including null) should NOT be encrypted.
  EXPECT_TRUE(globalExists(*M, "short_str"))
      << "Short string (<=4 bytes) should not be encrypted";
}

TEST_F(StringEncryptionObfTest, NoNullTerminatorSkipped) {
  auto M = createModule();
  // Create a byte array without null terminator.
  uint8_t data[] = {'H', 'e', 'l', 'l', 'o', '!'};
  auto *gv = createGlobalByteArray(*M, "no_null_str", data);
  createFunctionUsingGlobal(*M, "use_fn", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Array without null terminator is not isString() — should be untouched.
  EXPECT_TRUE(globalExists(*M, "no_null_str"))
      << "Array without null terminator should not be encrypted";
}

TEST_F(StringEncryptionObfTest, MultipleStrings) {
  auto M = createModule();
  auto *gv1 = createGlobalString(*M, "str_one", "First string here");
  auto *gv2 = createGlobalString(*M, "str_two", "Second string here");
  createFunctionUsingGlobal(*M, "use_fn1", gv1);
  createFunctionUsingGlobal(*M, "use_fn2", gv2);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Both globals should be removed.
  EXPECT_FALSE(globalExists(*M, "str_one"))
      << "First string should be encrypted and removed";
  EXPECT_FALSE(globalExists(*M, "str_two"))
      << "Second string should be encrypted and removed";
}

TEST_F(StringEncryptionObfTest, SameStringMultipleFunctions) {
  auto M = createModule();
  auto *gv = createGlobalString(*M, "shared_str", "Shared string data!");

  // Two functions using the same global.
  createFunctionUsingGlobal(*M, "fn_a", gv);
  createFunctionUsingGlobal(*M, "fn_b", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Each function should have its own alloca for the decryption buffer.
  auto *fnA = M->getFunction("fn_a");
  auto *fnB = M->getFunction("fn_b");
  ASSERT_NE(fnA, nullptr);
  ASSERT_NE(fnB, nullptr);
  EXPECT_GE(countAllocas(*fnA), 1u)
      << "fn_a should have its own decryption buffer";
  EXPECT_GE(countAllocas(*fnB), 1u)
      << "fn_b should have its own decryption buffer";

  // Original global should be removed.
  EXPECT_FALSE(globalExists(*M, "shared_str"));
}

TEST_F(StringEncryptionObfTest, LongStringUsesLoop) {
  auto M = createModule();
  // 40 chars + null = 41 bytes, > 32 threshold.
  std::string longStr(40, 'A');
  auto *gv = createGlobalString(*M, "long_str", longStr);
  createFunctionUsingGlobal(*M, "use_fn", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *F = M->getFunction("use_fn");
  ASSERT_NE(F, nullptr);

  // Loop-based decryption creates PHI nodes for index and state.
  EXPECT_TRUE(hasPHINodes(*F))
      << "Long string (>32 bytes) should use loop-based decryption with PHIs";

  EXPECT_FALSE(globalExists(*M, "long_str"));
}

TEST_F(StringEncryptionObfTest, ShortStringUnrolled) {
  auto M = createModule();
  // 10 chars + null = 11 bytes, > 4 but <= 32.
  auto *gv = createGlobalString(*M, "medium_str", "HelloWorld");
  createFunctionUsingGlobal(*M, "use_fn", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *F = M->getFunction("use_fn");
  ASSERT_NE(F, nullptr);

  // Unrolled decryption should NOT create PHI nodes (all in entry block).
  EXPECT_FALSE(hasPHINodes(*F))
      << "Short string (<=32 bytes) should use unrolled decryption without PHIs";

  EXPECT_FALSE(globalExists(*M, "medium_str"));
}

TEST_F(StringEncryptionObfTest, NonStringGlobalUntouched) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *arrTy = llvm::ArrayType::get(i32Ty, 4);
  llvm::Constant *elts[] = {
      llvm::ConstantInt::get(i32Ty, 1), llvm::ConstantInt::get(i32Ty, 2),
      llvm::ConstantInt::get(i32Ty, 3), llvm::ConstantInt::get(i32Ty, 4)};
  auto *init = llvm::ConstantArray::get(arrTy, elts);
  auto *gv = new llvm::GlobalVariable(*M, arrTy, true,
                                      llvm::GlobalValue::PrivateLinkage,
                                      init, "int_array");

  // Create a trivial function so the module isn't empty.
  auto *voidTy = llvm::Type::getVoidTy(Ctx);
  auto *fnTy = llvm::FunctionType::get(voidTy, {}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "dummy_fn", *M);
  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> builder(entryBB);
  builder.CreateRetVoid();

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // i32 array is not a ConstantDataArray string — should be untouched.
  EXPECT_TRUE(globalExists(*M, "int_array"))
      << "Non-string global should not be encrypted";
}

TEST_F(StringEncryptionObfTest, SectionedGlobalSkipped) {
  auto M = createModule();
  auto *gv = createGlobalString(*M, "sectioned_str", "This has a section");
  gv->setSection(".mysection");
  createFunctionUsingGlobal(*M, "use_fn", gv);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Global with section attribute should be skipped.
  EXPECT_TRUE(globalExists(*M, "sectioned_str"))
      << "Global with section attribute should not be encrypted";
}

TEST_F(StringEncryptionObfTest, ModuleVerifiesMultipleSeeds) {
  for (uint32_t seed = 0; seed < 10; ++seed) {
    auto M = createModule();
    auto *gv = createGlobalString(*M, "test_str", "Verify across seeds!");
    createFunctionUsingGlobal(*M, "use_fn", gv);

    ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    ollvm::encryptStringsModule(*M, seed);

    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    EXPECT_FALSE(llvm::verifyModule(*M, &errOS))
        << "Module verification failed with seed " << seed << ": " << errStr;
  }
}

TEST_F(StringEncryptionObfTest, EmptyModuleNoOp) {
  auto M = createModule();

  // No globals, no functions — should not crash.
  ollvm::encryptStringsModule(*M, 42);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

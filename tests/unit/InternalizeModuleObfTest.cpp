#include <gtest/gtest.h>

#include <llvm/IR/Comdat.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <string>
#include <vector>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/private/InternalizeModule.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class InternalizeModuleObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_internalize", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a minimal function with one block: `ret void`.
  llvm::Function *createVoidFunction(llvm::Module &M, const std::string &name,
                                     llvm::GlobalValue::LinkageTypes linkage) {
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, false);
    auto *F =
        llvm::Function::Create(fnTy, linkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    B.CreateRetVoid();
    return F;
  }

  /// Create a declaration (no body).
  llvm::Function *createDeclaration(llvm::Module &M, const std::string &name,
                                    llvm::GlobalValue::LinkageTypes linkage) {
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, false);
    return llvm::Function::Create(fnTy, linkage, name, M);
  }
};

TEST_F(InternalizeModuleObfTest, LinkOnceODR) {
  auto M = createModule();
  createVoidFunction(*M, "odr_func",
                     llvm::GlobalValue::LinkOnceODRLinkage);

  ollvm::internalizeModule(*M, 42, {});

  auto *F = M->getFunction("odr_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::InternalLinkage)
      << "LinkOnceODR should become internal";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, WeakODR) {
  auto M = createModule();
  createVoidFunction(*M, "weak_odr_func",
                     llvm::GlobalValue::WeakODRLinkage);

  ollvm::internalizeModule(*M, 42, {});

  auto *F = M->getFunction("weak_odr_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::InternalLinkage)
      << "WeakODR should become internal";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, ExternalUntouched) {
  auto M = createModule();
  createVoidFunction(*M, "ext_func",
                     llvm::GlobalValue::ExternalLinkage);

  ollvm::internalizeModule(*M, 42, {});

  auto *F = M->getFunction("ext_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::ExternalLinkage)
      << "External linkage should remain unchanged in non-aggressive mode";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, AggressiveMode) {
  auto M = createModule();
  createVoidFunction(*M, "ext_func",
                     llvm::GlobalValue::ExternalLinkage);

  ollvm::internalizeModule(*M, 42, {}, /*aggressiveMode=*/true);

  auto *F = M->getFunction("ext_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::InternalLinkage)
      << "Aggressive mode should internalize external functions";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, PreservePatterns) {
  auto M = createModule();
  createVoidFunction(*M, "my_preserved_func",
                     llvm::GlobalValue::LinkOnceODRLinkage);

  std::vector<std::string> patterns = {"my_preserved*"};
  ollvm::internalizeModule(*M, 42, patterns);

  auto *F = M->getFunction("my_preserved_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::LinkOnceODRLinkage)
      << "Preserved pattern should prevent internalization";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, SkipsDeclarations) {
  auto M = createModule();
  createDeclaration(*M, "decl_func",
                    llvm::GlobalValue::LinkOnceODRLinkage);

  ollvm::internalizeModule(*M, 42, {});

  auto *F = M->getFunction("decl_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::LinkOnceODRLinkage)
      << "Declarations should not be internalized";
}

TEST_F(InternalizeModuleObfTest, SkipsLocalLinkage) {
  auto M = createModule();
  createVoidFunction(*M, "internal_func",
                     llvm::GlobalValue::InternalLinkage);

  ollvm::internalizeModule(*M, 42, {});

  auto *F = M->getFunction("internal_func");
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::InternalLinkage)
      << "Already-internal functions should remain internal";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, GlobalVariableODR) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *GV = new llvm::GlobalVariable(
      *M, i32Ty, /*isConstant=*/false,
      llvm::GlobalValue::LinkOnceODRLinkage,
      llvm::ConstantInt::get(i32Ty, 42), "odr_global");

  ollvm::internalizeModule(*M, 42, {});

  EXPECT_EQ(GV->getLinkage(), llvm::GlobalValue::InternalLinkage)
      << "LinkOnceODR global variable should become internal";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, ComatStripped) {
  auto M = createModule();
  auto *F = createVoidFunction(*M, "comdat_func",
                               llvm::GlobalValue::LinkOnceODRLinkage);
  auto *CD = M->getOrInsertComdat("comdat_func");
  F->setComdat(CD);
  ASSERT_NE(F->getComdat(), nullptr);

  ollvm::internalizeModule(*M, 42, {});

  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::InternalLinkage);
  EXPECT_EQ(F->getComdat(), nullptr)
      << "Comdat should be stripped on internalization";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(InternalizeModuleObfTest, SkipsSectioned) {
  auto M = createModule();
  auto *F = createVoidFunction(*M, "sectioned_func",
                               llvm::GlobalValue::LinkOnceODRLinkage);
  F->setSection(".my_section");

  ollvm::internalizeModule(*M, 42, {});

  EXPECT_EQ(F->getLinkage(), llvm::GlobalValue::LinkOnceODRLinkage)
      << "Functions with custom sections should not be internalized";

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace

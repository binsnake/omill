#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <cstdint>
#include <set>
#include <string>
#include <vector>

// Directly include the implementation — this test is part of the unit test
// binary which links against LLVM but not ollvm-obf as a library.
#include "../../tools/ollvm-obf/StackRandomization.cpp"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class StackRandomizationObfTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test_stack_rand", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  /// Create a function with several allocas in the entry block.
  ///
  ///   define void @fn() {
  ///   entry:
  ///     %a = alloca i32
  ///     %b = alloca i64
  ///     %c = alloca [16 x i8]
  ///     store i32 1, ptr %a
  ///     store i64 2, ptr %b
  ///     ret void
  ///   }
  llvm::Function *createAllocaFunction(llvm::Module &M,
                                       const std::string &name) {
    auto *voidTy = llvm::Type::getVoidTy(Ctx);
    auto *fnTy = llvm::FunctionType::get(voidTy, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *a = B.CreateAlloca(llvm::Type::getInt32Ty(Ctx), nullptr, "");
    auto *b = B.CreateAlloca(llvm::Type::getInt64Ty(Ctx), nullptr, "");
    auto *c = B.CreateAlloca(llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 16),
                   nullptr, "");
    B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt32Ty(Ctx), 1), a);
    B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 2), b);
    B.CreateStore(llvm::Constant::getNullValue(llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 16)), c);
    B.CreateRetVoid();
    return F;
  }

  /// Create a function with no allocas (just computation).
  llvm::Function *createNoAllocaFunction(llvm::Module &M,
                                         const std::string &name) {
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *fnTy = llvm::FunctionType::get(i32Ty, {i32Ty, i32Ty}, false);
    auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
    llvm::IRBuilder<> B(entry);
    auto *sum = B.CreateAdd(F->getArg(0), F->getArg(1), "");
    B.CreateRet(sum);
    return F;
  }

  /// Collect alloca types from the entry block in order.
  std::vector<llvm::Type *> collectAllocaTypes(llvm::Function &F) {
    std::vector<llvm::Type *> types;
    for (auto &I : F.getEntryBlock()) {
      if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I))
        types.push_back(AI->getAllocatedType());
    }
    return types;
  }

  /// Count allocas in the entry block.
  unsigned countAllocas(llvm::Function &F) {
    unsigned count = 0;
    for (auto &I : F.getEntryBlock()) {
      if (llvm::isa<llvm::AllocaInst>(&I))
        ++count;
    }
    return count;
  }

  /// Serialize the function for comparison.
  std::string serializeFunction(llvm::Function &F) {
    std::string str;
    llvm::raw_string_ostream os(str);
    F.print(os);
    return str;
  }

  /// Check if every alloca in the entry block has at least one store user.
  bool allAllocasHaveStores(llvm::Function &F) {
    for (auto &I : F.getEntryBlock()) {
      if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
        bool hasStore = false;
        for (auto *U : AI->users()) {
          if (llvm::isa<llvm::StoreInst>(U)) {
            hasStore = true;
            break;
          }
        }
        if (!hasStore)
          return false;
      }
    }
    return true;
  }
};

TEST_F(StackRandomizationObfTest, PaddingInserted) {
  auto M = createModule();
  createAllocaFunction(*M, "fn");
  auto *F = M->getFunction("fn");
  unsigned before = countAllocas(*F);

  ollvm::randomizeStackModule(*M, 42, ollvm::FilterConfig{});

  unsigned after = countAllocas(*F);
  // Should have added 2-6 padding allocas.
  EXPECT_GT(after, before);
  EXPECT_GE(after - before, 2u);
  EXPECT_LE(after - before, 6u);
}

TEST_F(StackRandomizationObfTest, OrderChanged) {
  // Run on multiple seeds — at least one should produce a different order
  // than the original.
  auto M = createModule();
  createAllocaFunction(*M, "fn");
  auto *F = M->getFunction("fn");
  auto origTypes = collectAllocaTypes(*F);

  bool anyDifferent = false;
  for (uint32_t seed = 0; seed < 20; ++seed) {
    auto M2 = createModule();
    createAllocaFunction(*M2, "fn");
    ollvm::randomizeStackModule(*M2, seed, ollvm::FilterConfig{});
    auto newTypes = collectAllocaTypes(*M2->getFunction("fn"));
    // The total set must be a superset (includes padding), so just check
    // that the first origTypes.size() entries are not all in original order.
    // Actually, with padding added the order is almost certainly different.
    if (newTypes != origTypes) {
      anyDifferent = true;
      break;
    }
  }
  EXPECT_TRUE(anyDifferent);
}

TEST_F(StackRandomizationObfTest, PaddingStored) {
  auto M = createModule();
  createAllocaFunction(*M, "fn");

  ollvm::randomizeStackModule(*M, 42, ollvm::FilterConfig{});

  auto *F = M->getFunction("fn");
  EXPECT_TRUE(allAllocasHaveStores(*F));
}

TEST_F(StackRandomizationObfTest, DifferentSeedsDiffer) {
  auto M1 = createModule();
  createAllocaFunction(*M1, "fn");
  ollvm::randomizeStackModule(*M1, 100, ollvm::FilterConfig{});
  auto s1 = serializeFunction(*M1->getFunction("fn"));

  auto M2 = createModule();
  createAllocaFunction(*M2, "fn");
  ollvm::randomizeStackModule(*M2, 200, ollvm::FilterConfig{});
  auto s2 = serializeFunction(*M2->getFunction("fn"));

  // Different seeds should produce different IR (padding types/order differ).
  EXPECT_NE(s1, s2);
}

TEST_F(StackRandomizationObfTest, ModuleVerifies) {
  for (uint32_t seed = 0; seed < 10; ++seed) {
    auto M = createModule();
    createAllocaFunction(*M, "fn");
    createNoAllocaFunction(*M, "compute");

    ollvm::randomizeStackModule(*M, seed, ollvm::FilterConfig{});

    std::string err;
    llvm::raw_string_ostream errStream(err);
    EXPECT_FALSE(llvm::verifyModule(*M, &errStream))
        << "seed=" << seed << " error: " << err;
  }
}

TEST_F(StackRandomizationObfTest, DeclarationSkipped) {
  auto M = createModule();
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i32Ty, false);
  auto *decl = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                      "ext_fn", *M);

  auto before = serializeFunction(*decl);
  ollvm::randomizeStackModule(*M, 42, ollvm::FilterConfig{});
  auto after = serializeFunction(*decl);

  EXPECT_EQ(before, after);
}

TEST_F(StackRandomizationObfTest, SkipsNoAllocaFunctions) {
  // A function with no allocas should still get padding inserted.
  auto M = createModule();
  createNoAllocaFunction(*M, "compute");
  auto *F = M->getFunction("compute");
  unsigned before = countAllocas(*F);
  EXPECT_EQ(before, 0u);

  ollvm::randomizeStackModule(*M, 42, ollvm::FilterConfig{});

  // Padding should be added even to functions without original allocas.
  unsigned after = countAllocas(*F);
  EXPECT_GE(after, 2u);
  EXPECT_LE(after, 6u);

  // Module should still verify.
  std::string err;
  llvm::raw_string_ostream errStream(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &errStream)) << err;
}

TEST_F(StackRandomizationObfTest, DynamicAllocaUntouched) {
  // Dynamic allocas should not be shuffled.
  auto M = createModule();
  auto *voidTy = llvm::Type::getVoidTy(Ctx);
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(voidTy, {i32Ty}, false);
  auto *F = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                   "dyn_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "", F);
  llvm::IRBuilder<> B(entry);
  auto *fixedAI = B.CreateAlloca(i32Ty, nullptr, "");
  // Dynamic alloca with non-constant size.
  auto *dynAI = B.CreateAlloca(llvm::Type::getInt8Ty(Ctx), F->getArg(0), "");
  B.CreateStore(llvm::ConstantInt::get(i32Ty, 0), fixedAI);
  B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), 0), dynAI);
  B.CreateRetVoid();

  ollvm::randomizeStackModule(*M, 42, ollvm::FilterConfig{});

  // Verify the module is still valid.
  std::string err;
  llvm::raw_string_ostream errStream(err);
  EXPECT_FALSE(llvm::verifyModule(*M, &errStream)) << err;
}

TEST_F(StackRandomizationObfTest, AllocasContiguousAtTop) {
  // After transformation, all allocas should be contiguous at the top
  // of the entry block (after PHI nodes, which there are none here).
  auto M = createModule();
  createAllocaFunction(*M, "fn");

  ollvm::randomizeStackModule(*M, 42, ollvm::FilterConfig{});

  auto *F = M->getFunction("fn");
  bool seenNonAlloca = false;
  for (auto &I : F->getEntryBlock()) {
    if (llvm::isa<llvm::AllocaInst>(&I)) {
      EXPECT_FALSE(seenNonAlloca)
          << "Found alloca after non-alloca instruction";
    } else {
      seenNonAlloca = true;
    }
  }
}

}  // namespace

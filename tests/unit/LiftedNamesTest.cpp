#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Utils/LiftedNames.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>

#include <gtest/gtest.h>

namespace {

class LiftedNamesTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Remill lifted function type: (ptr, i64, ptr) -> ptr
  llvm::FunctionType *liftedFnTy() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  /// Create a lifted function with a body (entry block returning arg2).
  llvm::Function *createLiftedFunction(llvm::Module &M, llvm::StringRef name) {
    auto *F = llvm::Function::Create(liftedFnTy(),
                                     llvm::Function::ExternalLinkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(F->getArg(2));
    return F;
  }

  /// Create a lifted function declaration (no body).
  llvm::Function *createLiftedDecl(llvm::Module &M, llvm::StringRef name) {
    return llvm::Function::Create(liftedFnTy(),
                                  llvm::Function::ExternalLinkage, name, M);
  }
};

// ===----------------------------------------------------------------------===
// extractEntryVA
// ===----------------------------------------------------------------------===

TEST_F(LiftedNamesTest, ExtractEntryVA_ValidName) {
  EXPECT_EQ(omill::extractEntryVA("sub_180001000"), 0x180001000ULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_WithSuffix) {
  EXPECT_EQ(omill::extractEntryVA("sub_180001000.2"), 0x180001000ULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_InvalidPrefix) {
  EXPECT_EQ(omill::extractEntryVA("func_180001000"), 0ULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_EmptyString) {
  EXPECT_EQ(omill::extractEntryVA(""), 0ULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_SubPrefixOnly) {
  EXPECT_EQ(omill::extractEntryVA("sub_"), 0ULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_NonHexAfterPrefix) {
  EXPECT_EQ(omill::extractEntryVA("sub_ZZZZ"), 0ULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_DotSuffix) {
  EXPECT_EQ(omill::extractEntryVA("sub_DEAD.i"), 0xDEADULL);
}

TEST_F(LiftedNamesTest, ExtractEntryVA_DemergedCloneSuffix) {
  EXPECT_EQ(omill::extractEntryVA("sub_180001000__vm_abcdef"),
            0x180001000ULL);
}

TEST_F(LiftedNamesTest, DemergedHandlerCloneName_IsCanonical) {
  EXPECT_EQ(omill::demergedHandlerCloneName(0x180001000ULL, 0xABCDEFULL),
            "sub_180001000__vm_abcdef");
}

TEST_F(LiftedNamesTest, ExtractStructuralCodeTargetPC_ParsesKnownPrefixes) {
  EXPECT_EQ(omill::extractStructuralCodeTargetPC("sub_401230"), 0x401230ULL);
  EXPECT_EQ(omill::extractStructuralCodeTargetPC("blk_401030"), 0x401030ULL);
  EXPECT_EQ(omill::extractStructuralCodeTargetPC("block_401145"), 0x401145ULL);
  EXPECT_EQ(omill::extractStructuralCodeTargetPC("omill_native_target_401250"),
            0x401250ULL);
  EXPECT_EQ(
      omill::extractStructuralCodeTargetPC("omill_native_boundary_401260"),
      0x401260ULL);
  EXPECT_EQ(
      omill::extractStructuralCodeTargetPC("omill_executable_target_401270"),
      0x401270ULL);
  EXPECT_EQ(omill::extractStructuralCodeTargetPC("omill_vm_enter_target_401280"),
            0x401280ULL);
}

TEST_F(LiftedNamesTest, ExtractStructuralCodeTargetPC_PrefersAttrsOverName) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedDecl(*M, "blk_401030");
  F->addFnAttr("omill.vm_enter_target_pc", "401155");
  F->addFnAttr("omill.executable_target_pc", "401145");
  EXPECT_EQ(omill::extractStructuralCodeTargetPC(*F), 0x401145ULL);
}

TEST_F(LiftedNamesTest,
       ExtractStructuralCodeTargetPC_PrefersNativePlaceholderNameOverBoundaryFact) {
  auto M = std::make_unique<llvm::Module>("test_boundary_placeholder", Ctx);
  auto *F = createLiftedDecl(*M, "omill_native_target_401250");
  omill::BoundaryFact fact;
  fact.boundary_pc = 0x4012A0ULL;
  fact.native_target_pc = 0x4012B0ULL;
  omill::writeBoundaryFact(*F, fact);
  EXPECT_EQ(omill::extractStructuralCodeTargetPC(*F), 0x401250ULL);
}


// ===----------------------------------------------------------------------===
// extractBlockPC
// ===----------------------------------------------------------------------===

TEST_F(LiftedNamesTest, ExtractBlockPC_ValidName) {
  EXPECT_EQ(omill::extractBlockPC("block_180001010"), 0x180001010ULL);
}

TEST_F(LiftedNamesTest, ExtractBlockPC_WithLLVMSuffix) {
  EXPECT_EQ(omill::extractBlockPC("block_180001010.i"), 0x180001010ULL);
}

TEST_F(LiftedNamesTest, ExtractBlockPC_NumericSuffix) {
  EXPECT_EQ(omill::extractBlockPC("block_180001010.123"), 0x180001010ULL);
}

TEST_F(LiftedNamesTest, ExtractBlockPC_NonBlockName) {
  EXPECT_EQ(omill::extractBlockPC("entry"), 0ULL);
}

TEST_F(LiftedNamesTest, ExtractBlockPC_BlockPrefixNoHex) {
  EXPECT_EQ(omill::extractBlockPC("block_"), 0ULL);
}

TEST_F(LiftedNamesTest, ExtractBlockPC_EmptyString) {
  EXPECT_EQ(omill::extractBlockPC(""), 0ULL);
}

// ===----------------------------------------------------------------------===
// isLiftedFunction
// ===----------------------------------------------------------------------===

TEST_F(LiftedNamesTest, IsLiftedFunction_ValidWithBody) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");
  EXPECT_TRUE(omill::isLiftedFunction(*F));
}

TEST_F(LiftedNamesTest, IsLiftedFunction_DeclarationReturnsFalse) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedDecl(*M, "sub_180001000");
  EXPECT_FALSE(omill::isLiftedFunction(*F));
}

TEST_F(LiftedNamesTest, IsLiftedFunction_RemillPrefixReturnsFalse) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "__remill_jump");
  EXPECT_FALSE(omill::isLiftedFunction(*F));
}

TEST_F(LiftedNamesTest, IsLiftedFunction_OmillPrefixReturnsFalse) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "__omill_helper");
  EXPECT_FALSE(omill::isLiftedFunction(*F));
}

TEST_F(LiftedNamesTest, IsLiftedFunction_NativeSuffixReturnsFalse) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000_native");
  EXPECT_FALSE(omill::isLiftedFunction(*F));
}

TEST_F(LiftedNamesTest, IsLiftedFunction_WrongArgCount) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *bad_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
  auto *F = llvm::Function::Create(bad_ty, llvm::Function::ExternalLinkage,
                                   "sub_180001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(0));
  EXPECT_FALSE(omill::isLiftedFunction(*F));
}

TEST_F(LiftedNamesTest, IsLiftedFunction_WrongParamType) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  // (ptr, i32, ptr) -> ptr — wrong second param
  auto *bad_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i32_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(bad_ty, llvm::Function::ExternalLinkage,
                                   "sub_180001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(2));
  EXPECT_FALSE(omill::isLiftedFunction(*F));
}

// ===----------------------------------------------------------------------===
// hasLiftedSignature
// ===----------------------------------------------------------------------===

TEST_F(LiftedNamesTest, HasLiftedSignature_DeclarationReturnsTrue) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedDecl(*M, "sub_180001000");
  EXPECT_TRUE(omill::hasLiftedSignature(*F));
}

TEST_F(LiftedNamesTest, HasLiftedSignature_DefinitionReturnsTrue) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "__remill_jump");
  // hasLiftedSignature doesn't care about name or body
  EXPECT_TRUE(omill::hasLiftedSignature(*F));
}

TEST_F(LiftedNamesTest, HasLiftedSignature_WrongArgCount) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *bad_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty}, false);
  auto *F = llvm::Function::Create(bad_ty, llvm::Function::ExternalLinkage,
                                   "foo", *M);
  EXPECT_FALSE(omill::hasLiftedSignature(*F));
}

TEST_F(LiftedNamesTest, HasLiftedSignature_WrongReturnType) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *bad_ty = llvm::FunctionType::get(void_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(bad_ty, llvm::Function::ExternalLinkage,
                                   "foo", *M);
  EXPECT_FALSE(omill::hasLiftedSignature(*F));
}

// ===----------------------------------------------------------------------===
// findBlockForPC
// ===----------------------------------------------------------------------===

TEST_F(LiftedNamesTest, FindBlockForPC_FindsDisconnectedBlock) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");

  auto *block_a = llvm::BasicBlock::Create(Ctx, "block_180001010", F);
  llvm::IRBuilder<> B(block_a);
  B.CreateRet(F->getArg(2));

  auto *found = omill::findBlockForPC(*F, 0x180001010ULL);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found, block_a);
}

TEST_F(LiftedNamesTest, FindBlockForPC_ReturnsNullForMissingPC) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");

  auto *found = omill::findBlockForPC(*F, 0xDEADBEEFULL);
  EXPECT_EQ(found, nullptr);
}

// ===----------------------------------------------------------------------===
// collectBlockPCMap
// ===----------------------------------------------------------------------===

TEST_F(LiftedNamesTest, CollectBlockPCMap_MapsMultipleBlocks) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");

  auto *b1 = llvm::BasicBlock::Create(Ctx, "block_180001010", F);
  llvm::IRBuilder<> B1(b1);
  B1.CreateRet(F->getArg(2));

  auto *b2 = llvm::BasicBlock::Create(Ctx, "block_180001020", F);
  llvm::IRBuilder<> B2(b2);
  B2.CreateRet(F->getArg(2));

  auto map = omill::collectBlockPCMap(*F);
  EXPECT_EQ(map.size(), 2u);
  EXPECT_EQ(map[0x180001010ULL], b1);
  EXPECT_EQ(map[0x180001020ULL], b2);
}

TEST_F(LiftedNamesTest, CollectBlockPCMap_EmptyForNoBlocks) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");

  auto map = omill::collectBlockPCMap(*F);
  // Entry block has name "entry", not "block_...", so map should be empty.
  EXPECT_TRUE(map.empty());
}

TEST_F(LiftedNamesTest, CollectBlockPCMap_BlockWithLLVMSuffix) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");

  auto *b = llvm::BasicBlock::Create(Ctx, "block_180001010.i", F);
  llvm::IRBuilder<> B(b);
  B.CreateRet(F->getArg(2));

  auto map = omill::collectBlockPCMap(*F);
  EXPECT_EQ(map.size(), 1u);
  EXPECT_EQ(map[0x180001010ULL], b);
}

TEST_F(LiftedNamesTest, FindLiftedOrCoveredFunctionByPC_FindsCoveredBlockPc) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001000");

  auto *b = llvm::BasicBlock::Create(Ctx, "block_180001239", F);
  llvm::IRBuilder<> B(b);
  B.CreateRet(F->getArg(2));

  auto *found = omill::findLiftedOrCoveredFunctionByPC(*M, 0x180001239ULL);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found, F);
}

TEST_F(LiftedNamesTest, FindNearestCoveredLiftedOrBlockPC_FindsNearbyEntry) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "blk_180001220");
  auto *b = llvm::BasicBlock::Create(Ctx, "block_180001240", F);
  llvm::IRBuilder<> B(b);
  B.CreateRet(F->getArg(2));

  auto found = omill::findNearestCoveredLiftedOrBlockPC(*M, 0x180001249ULL);
  ASSERT_TRUE(found.has_value());
  EXPECT_EQ(*found, 0x180001240ULL);
}

TEST_F(LiftedNamesTest,
       FindLiftedOrCoveredFunctionByPC_IgnoresInferredMidInstructionPC) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001800");

  auto *named = llvm::BasicBlock::Create(Ctx, "block_180001840", F);
  llvm::IRBuilder<> NamedB(named);
  NamedB.CreateRet(F->getArg(2));

  auto *plain = llvm::BasicBlock::Create(Ctx, "plain", F);
  llvm::IRBuilder<> PlainB(plain);
  auto *pc_plus =
      PlainB.CreateAdd(F->getArg(1), llvm::ConstantInt::get(
                                         llvm::Type::getInt64Ty(Ctx), 0x92));
  (void)pc_plus;
  PlainB.CreateRet(F->getArg(2));

  auto *found = omill::findLiftedOrCoveredFunctionByPC(*M, 0x180001892ULL);
  EXPECT_EQ(found, nullptr);
}

TEST_F(LiftedNamesTest,
       FindNearestCoveredLiftedOrBlockPC_IgnoresInferredMidInstructionPC) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedFunction(*M, "sub_180001800");

  auto *named = llvm::BasicBlock::Create(Ctx, "block_180001840", F);
  llvm::IRBuilder<> NamedB(named);
  NamedB.CreateRet(F->getArg(2));

  auto *plain = llvm::BasicBlock::Create(Ctx, "plain", F);
  llvm::IRBuilder<> PlainB(plain);
  auto *pc_plus =
      PlainB.CreateAdd(F->getArg(1), llvm::ConstantInt::get(
                                         llvm::Type::getInt64Ty(Ctx), 0x92));
  (void)pc_plus;
  PlainB.CreateRet(F->getArg(2));

  auto found =
      omill::findNearestCoveredLiftedOrBlockPC(*M, 0x180001892ULL, 0x80);
  ASSERT_TRUE(found.has_value());
  EXPECT_EQ(*found, 0x180001840ULL);
}

TEST_F(LiftedNamesTest, FindStructuralCodeTargetFunctionByPC_FindsPlaceholderDecl) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *F = createLiftedDecl(*M, "omill_executable_target_1801F7733");
  F->addFnAttr("omill.executable_target_pc", "1801F7733");

  auto *found =
      omill::findStructuralCodeTargetFunctionByPC(*M, 0x1801F7733ULL);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found, F);
}

}  // namespace

#include "omill/Devirtualization/ExecutableTargetFact.h"

#include <gtest/gtest.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

namespace {

TEST(ExecutableTargetFactTest, RoundTripsCallMetadata) {
  llvm::LLVMContext ctx;
  llvm::Module module("fact_call", ctx);
  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *fn = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                    "sub_401000", module);
  auto *callee = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_missing_block",
      module);
  auto *entry = llvm::BasicBlock::Create(ctx, "entry", fn);
  llvm::IRBuilder<> b(entry);
  auto *call = b.CreateCall(
      callee, {fn->getArg(0), llvm::ConstantInt::get(i64_ty, 0x401230),
               fn->getArg(2)});
  b.CreateRet(fn->getArg(2));

  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230;
  fact.effective_target_pc = 0x401240;
  fact.canonical_owner_pc = 0x401220;
  fact.kind = omill::ExecutableTargetKind::kCanonicalOwner;
  fact.trust = omill::ExecutableTargetTrust::kNearbyOwner;
  fact.exact_fallthrough_target = true;
  fact.invalidated_executable_entry = true;
  fact.invalidated_entry_source_pc = 0x401230;
  fact.invalidated_entry_failed_pc = 0x40123A;

  omill::writeExecutableTargetFact(*call, fact);
  auto roundtrip = omill::readExecutableTargetFact(*call);
  ASSERT_TRUE(roundtrip.has_value());
  EXPECT_EQ(*roundtrip, fact);
}

TEST(ExecutableTargetFactTest, RoundTripsFunctionAttrs) {
  llvm::LLVMContext ctx;
  llvm::Module module("fact_function", ctx);
  auto *ptr_ty = llvm::PointerType::getUnqual(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *fn = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", module);

  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230;
  fact.effective_target_pc = 0x401230;
  fact.kind = omill::ExecutableTargetKind::kExactFallthroughEntry;
  fact.trust = omill::ExecutableTargetTrust::kExactFallthrough;
  fact.exact_fallthrough_target = true;

  omill::writeExecutableTargetFact(*fn, fact);
  auto roundtrip = omill::readExecutableTargetFact(*fn);
  ASSERT_TRUE(roundtrip.has_value());
  EXPECT_EQ(*roundtrip, fact);
}

TEST(ExecutableTargetFactTest, ConvertsLiftTargetDecision) {
  omill::LiftTargetDecision decision;
  decision.raw_target_pc = 0x401230;
  decision.effective_target_pc = 0x401240;
  decision.classification = omill::LiftTargetClassification::kCanonicalOwner;
  decision.trust = omill::LiftTargetTrust::kNearbyOwner;
  decision.owner_pc = 0x401220;
  decision.is_exact_fallthrough = false;

  auto fact = omill::executableTargetFactFromDecision(decision);
  ASSERT_TRUE(fact.has_value());
  EXPECT_EQ(fact->raw_target_pc, 0x401230u);
  EXPECT_EQ(fact->effective_target_pc, 0x401240u);
  EXPECT_EQ(fact->canonical_owner_pc, 0x401220u);
  EXPECT_EQ(fact->kind, omill::ExecutableTargetKind::kCanonicalOwner);
  EXPECT_EQ(fact->trust, omill::ExecutableTargetTrust::kNearbyOwner);
}

}  // namespace

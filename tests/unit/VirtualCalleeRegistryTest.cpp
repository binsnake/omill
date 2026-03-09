#include "omill/Analysis/VirtualCalleeRegistry.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

TEST(VirtualCalleeRegistryTest, ReadsRegistryMetadata) {
  llvm::LLVMContext ctx;
  llvm::Module M("test", ctx);

  std::vector<omill::VirtualCalleeRecord> records = {
      {"sub_401000_native__caller_0_habcdef", "sub_401000_native",
       "caller_native", "hash_resolved", 0xABCDEFULL, 2,
       0x401000ULL, 0xABCDEFULL},
      {"sub_402000_native__caller_1", "sub_402000_native", "caller_native",
       "nested_helper", std::nullopt, 3,
       0x402000ULL, std::nullopt},
  };
  omill::setVirtualCalleeRegistryMetadata(M, records);

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
  MAM.registerPass([&] { return omill::VirtualCalleeRegistryAnalysis(); });

  auto &registry = MAM.getResult<omill::VirtualCalleeRegistryAnalysis>(M);
  ASSERT_EQ(registry.size(), 2u);
  EXPECT_EQ(registry.countKind("hash_resolved"), 1u);
  EXPECT_EQ(registry.countKind("nested_helper"), 1u);

  auto resolved = registry.lookup("sub_401000_native__caller_0_habcdef");
  ASSERT_TRUE(resolved.has_value());
  EXPECT_EQ(resolved->base_name, "sub_401000_native");
  EXPECT_EQ(resolved->caller_name, "caller_native");
  ASSERT_TRUE(resolved->hash.has_value());
  EXPECT_EQ(*resolved->hash, 0xABCDEFULL);
  EXPECT_EQ(resolved->first_round, 2u);
  EXPECT_EQ(resolved->handler_va, 0x401000ULL);
  ASSERT_TRUE(resolved->trace_hash.has_value());
  EXPECT_EQ(*resolved->trace_hash, 0xABCDEFULL);
  EXPECT_FALSE(resolved->trace_linked);

  auto nested = registry.lookup("sub_402000_native__caller_1");
  ASSERT_TRUE(nested.has_value());
  EXPECT_EQ(nested->kind, "nested_helper");
  EXPECT_FALSE(nested->hash.has_value());
  EXPECT_EQ(nested->handler_va, 0x402000ULL);
  EXPECT_FALSE(nested->trace_hash.has_value());
  EXPECT_FALSE(nested->trace_linked);
}

TEST(VirtualCalleeRegistryTest, ClearsMetadataWhenEmpty) {
  llvm::LLVMContext ctx;
  llvm::Module M("test", ctx);

  std::vector<omill::VirtualCalleeRecord> records = {
      {"sub_401000_native__caller_0_habcdef", "sub_401000_native",
       "caller_native", "hash_resolved", 0xABCDEFULL, 2,
       0x401000ULL, 0xABCDEFULL},
  };
  omill::setVirtualCalleeRegistryMetadata(M, records);
  omill::setVirtualCalleeRegistryMetadata(M, {});

  EXPECT_EQ(M.getNamedMetadata("omill.vm_virtual_callees"), nullptr);
}

// Helper to build a registry from records via metadata round-trip.
static omill::VirtualCalleeRegistry buildRegistry(
    llvm::Module &M,
    const std::vector<omill::VirtualCalleeRecord> &records) {
  omill::setVirtualCalleeRegistryMetadata(M, records);
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
  MAM.registerPass([&] { return omill::VirtualCalleeRegistryAnalysis(); });
  return MAM.getResult<omill::VirtualCalleeRegistryAnalysis>(M);
}

TEST(VirtualCalleeRegistryTest, LookupByTraceKey) {
  llvm::LLVMContext ctx;
  llvm::Module M("test", ctx);

  std::vector<omill::VirtualCalleeRecord> records = {
      {"clone_a", "base_a", "caller_a", "hash_resolved",
       0x111ULL, 1, 0x401000ULL, 0xAAAAULL},
      {"clone_b", "base_b", "caller_b", "hash_resolved",
       0x222ULL, 1, 0x402000ULL, 0xBBBBULL},
      {"clone_c", "base_c", "caller_c", "nested_helper",
       std::nullopt, 1, 0x403000ULL, std::nullopt},
  };

  auto registry = buildRegistry(M, records);

  // Exact match.
  auto found = registry.lookupByTraceKey(0x401000ULL, 0xAAAAULL);
  ASSERT_TRUE(found.has_value());
  EXPECT_EQ(found->clone_name, "clone_a");

  auto found2 = registry.lookupByTraceKey(0x402000ULL, 0xBBBBULL);
  ASSERT_TRUE(found2.has_value());
  EXPECT_EQ(found2->clone_name, "clone_b");

  // Wrong trace_hash for a valid handler_va.
  EXPECT_FALSE(registry.lookupByTraceKey(0x401000ULL, 0xBBBBULL).has_value());

  // Completely unknown handler_va.
  EXPECT_FALSE(registry.lookupByTraceKey(0x999999ULL, 0xAAAAULL).has_value());
}

TEST(VirtualCalleeRegistryTest, LookupByBase) {
  llvm::LLVMContext ctx;
  llvm::Module M("test", ctx);

  std::vector<omill::VirtualCalleeRecord> records = {
      {"clone_a1", "base_shared", "caller_x", "hash_resolved",
       0x111ULL, 1, 0x401000ULL, 0xAAAAULL},
      {"clone_a2", "base_shared", "caller_y", "nested_helper",
       std::nullopt, 2, 0x402000ULL, std::nullopt},
      {"clone_b1", "base_other", "caller_x", "hash_resolved",
       0x333ULL, 1, 0x403000ULL, 0xCCCCULL},
  };

  auto registry = buildRegistry(M, records);

  auto shared = registry.lookupByBase("base_shared");
  ASSERT_EQ(shared.size(), 2u);
  // Order should match insertion order.
  EXPECT_EQ(shared[0]->clone_name, "clone_a1");
  EXPECT_EQ(shared[1]->clone_name, "clone_a2");

  auto other = registry.lookupByBase("base_other");
  ASSERT_EQ(other.size(), 1u);
  EXPECT_EQ(other[0]->clone_name, "clone_b1");

  auto none = registry.lookupByBase("nonexistent");
  EXPECT_TRUE(none.empty());
}

TEST(VirtualCalleeRegistryTest, LookupByCaller) {
  llvm::LLVMContext ctx;
  llvm::Module M("test", ctx);

  std::vector<omill::VirtualCalleeRecord> records = {
      {"clone_a1", "base_a", "caller_shared", "hash_resolved",
       0x111ULL, 1, 0x401000ULL, 0xAAAAULL},
      {"clone_a2", "base_b", "caller_shared", "nested_helper",
       std::nullopt, 2, 0x402000ULL, std::nullopt},
      {"clone_b1", "base_c", "caller_other", "hash_resolved",
       0x333ULL, 1, 0x403000ULL, 0xCCCCULL},
  };

  auto registry = buildRegistry(M, records);

  auto shared = registry.lookupByCaller("caller_shared");
  ASSERT_EQ(shared.size(), 2u);
  EXPECT_EQ(shared[0]->clone_name, "clone_a1");
  EXPECT_EQ(shared[1]->clone_name, "clone_a2");

  auto other = registry.lookupByCaller("caller_other");
  ASSERT_EQ(other.size(), 1u);
  EXPECT_EQ(other[0]->clone_name, "clone_b1");

  auto none = registry.lookupByCaller("nonexistent");
  EXPECT_TRUE(none.empty());
}

TEST(VirtualCalleeRegistryTest, CountTraceLinked) {
  llvm::LLVMContext ctx;
  llvm::Module M("test", ctx);

  std::vector<omill::VirtualCalleeRecord> records = {
      {"clone_a", "base_a", "caller_a", "hash_resolved",
       0x111ULL, 1, 0x401000ULL, 0xAAAAULL, true},
      {"clone_b", "base_b", "caller_b", "hash_resolved",
       0x222ULL, 1, 0x402000ULL, 0xBBBBULL, true},
      {"clone_c", "base_c", "caller_c", "nested_helper",
       std::nullopt, 1, 0x403000ULL, std::nullopt, false},
  };

  auto registry = buildRegistry(M, records);

  EXPECT_EQ(registry.countTraceLinked(), 2u);
}

}  // namespace

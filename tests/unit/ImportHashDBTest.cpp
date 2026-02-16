#include "omill/Utils/ImportHashDB.h"

#include <gtest/gtest.h>

namespace {

TEST(ImportHashDBTest, ComputeHashDeterministic) {
  // Same input, same offset => same hash.
  uint32_t h1 = omill::ImportHashDB::computeHash("CreateFileW", 0x811c9dc5u);
  uint32_t h2 = omill::ImportHashDB::computeHash("CreateFileW", 0x811c9dc5u);
  EXPECT_EQ(h1, h2);
}

TEST(ImportHashDBTest, ComputeHashDifferentOffsetsYieldDifferentHashes) {
  uint32_t h1 = omill::ImportHashDB::computeHash("CreateFileW", 0);
  uint32_t h2 = omill::ImportHashDB::computeHash("CreateFileW", 0x811c9dc5u);
  EXPECT_NE(h1, h2);
}

TEST(ImportHashDBTest, ComputeHashDifferentNamesDifferentHashes) {
  uint32_t h1 = omill::ImportHashDB::computeHash("CreateFileW", 0x811c9dc5u);
  uint32_t h2 = omill::ImportHashDB::computeHash("CreateFileA", 0x811c9dc5u);
  EXPECT_NE(h1, h2);
}

TEST(ImportHashDBTest, ResolveFindsCorrectAPI) {
  omill::ImportHashDB db;
  db.addExport("kernel32.dll", "CreateFileW");
  db.addExport("kernel32.dll", "VirtualAlloc");

  uint32_t offset = 0x811c9dc5u;
  uint32_t hash =
      omill::ImportHashDB::computeHash("VirtualAlloc", offset);

  auto result = db.resolve(offset, hash);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(result->module, "kernel32.dll");
  EXPECT_EQ(result->function, "VirtualAlloc");
}

TEST(ImportHashDBTest, ResolveReturnsNulloptForUnknown) {
  omill::ImportHashDB db;
  db.addExport("kernel32.dll", "CreateFileW");

  auto result = db.resolve(0, 0xDEADDEADu);
  EXPECT_FALSE(result.has_value());
}

TEST(ImportHashDBTest, BuiltinsContainCommonAPIs) {
  omill::ImportHashDB db;
  db.loadBuiltins();

  // Should have a substantial number of entries.
  EXPECT_GT(db.size(), 500u);

  // Verify some well-known APIs are resolvable.
  uint32_t offset = 0x811c9dc5u;

  auto check = [&](const char *name) {
    uint32_t hash = omill::ImportHashDB::computeHash(name, offset);
    auto result = db.resolve(offset, hash);
    ASSERT_TRUE(result.has_value()) << "Failed to resolve: " << name;
    EXPECT_EQ(result->function, name);
  };

  check("CreateFileW");
  check("VirtualAlloc");
  check("LoadLibraryA");
  check("GetProcAddress");
  check("CloseHandle");
  check("NtAllocateVirtualMemory");
  check("MessageBoxA");
  check("WSAStartup");
  check("RegOpenKeyExA");
}

TEST(ImportHashDBTest, ComputeHashMatchesFNV1aSpec) {
  // FNV-1a with offset basis 0x811c9dc5:
  // For empty string, hash = offset basis (no chars to process).
  uint32_t empty_hash =
      omill::ImportHashDB::computeHash("", 0x811c9dc5u);
  EXPECT_EQ(empty_hash, 0x811c9dc5u);

  // For single char 'a' (0x61):
  // value = (0x811c9dc5 ^ 0x61) * 0x01000193
  uint32_t expected = (0x811c9dc5u ^ 0x61u) * 0x01000193u;
  uint32_t actual = omill::ImportHashDB::computeHash("a", 0x811c9dc5u);
  EXPECT_EQ(actual, expected);
}

TEST(ImportHashDBTest, MultiAlgorithmComputeHash) {
  using HA = omill::HashAlgorithm;

  // FNV1a32 via new API should match legacy API.
  uint32_t fnv_legacy = omill::ImportHashDB::computeHash("VirtualAlloc",
                                                          0x811c9dc5u);
  uint32_t fnv_new = omill::ImportHashDB::computeHash("VirtualAlloc",
                                                       HA::FNV1a32,
                                                       0x811c9dc5u);
  EXPECT_EQ(fnv_legacy, fnv_new);

  // FNV1a32_Lowercase should differ from case-sensitive for mixed-case names.
  uint32_t fnv_lower = omill::ImportHashDB::computeHash("VirtualAlloc",
                                                         HA::FNV1a32_Lowercase,
                                                         0x811c9dc5u);
  EXPECT_NE(fnv_new, fnv_lower);

  // FNV1a32_Lowercase should be the same for already-lowercase names.
  uint32_t fnv_cs = omill::ImportHashDB::computeHash("connect",
                                                      HA::FNV1a32,
                                                      0x811c9dc5u);
  uint32_t fnv_ci = omill::ImportHashDB::computeHash("connect",
                                                      HA::FNV1a32_Lowercase,
                                                      0x811c9dc5u);
  EXPECT_EQ(fnv_cs, fnv_ci);

  // DJB2 should produce a different value from FNV1a32.
  uint32_t djb2 = omill::ImportHashDB::computeHash("VirtualAlloc",
                                                     HA::DJB2, 5381u);
  EXPECT_NE(djb2, fnv_new);

  // DJB2 empty string should equal seed.
  uint32_t djb2_empty = omill::ImportHashDB::computeHash("", HA::DJB2, 5381u);
  EXPECT_EQ(djb2_empty, 5381u);
}

TEST(ImportHashDBTest, TryResolveFindsAcrossAlgorithms) {
  omill::ImportHashDB db;
  db.addExport("kernel32.dll", "VirtualAlloc");
  db.buildLookupTables();

  using HA = omill::HashAlgorithm;

  // Should resolve FNV1a32 hash.
  uint32_t fnv_hash = omill::ImportHashDB::computeHash("VirtualAlloc",
                                                        HA::FNV1a32,
                                                        0x811c9dc5u);
  auto result = db.tryResolve(fnv_hash);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(result->entry.function, "VirtualAlloc");
  EXPECT_EQ(result->algorithm, HA::FNV1a32);
  EXPECT_EQ(result->seed, 0x811c9dc5u);

  // Should resolve DJB2 hash.
  uint32_t djb2_hash = omill::ImportHashDB::computeHash("VirtualAlloc",
                                                         HA::DJB2, 5381u);
  result = db.tryResolve(djb2_hash);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(result->entry.function, "VirtualAlloc");
  EXPECT_EQ(result->algorithm, HA::DJB2);

  // Unknown hash should return nullopt.
  result = db.tryResolve(0xDEADDEADu);
  EXPECT_FALSE(result.has_value());
}

TEST(ImportHashDBTest, ResolveModuleNameFindsKernel32) {
  omill::ImportHashDB db;
  db.loadBuiltins();

  // Compute the case-insensitive FNV1a32 hash of "kernel32.dll".
  uint32_t hash = omill::ImportHashDB::computeHash(
      "kernel32.dll", omill::HashAlgorithm::FNV1a32_Lowercase, 0x811c9dc5u);

  auto result = db.resolveModuleName(hash);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(*result, "kernel32.dll");
}

TEST(ImportHashDBTest, ResolveModuleNameReturnsNulloptForUnknown) {
  omill::ImportHashDB db;
  db.loadBuiltins();

  auto result = db.resolveModuleName(0xDEADDEADu);
  EXPECT_FALSE(result.has_value());
}

TEST(ImportHashDBTest, ResolveInModuleFindsVirtualAlloc) {
  omill::ImportHashDB db;
  db.loadBuiltins();

  uint32_t func_hash = omill::ImportHashDB::computeHash(
      "VirtualAlloc", omill::HashAlgorithm::FNV1a32, 0x811c9dc5u);

  auto result = db.resolveInModule("kernel32.dll", func_hash);
  ASSERT_TRUE(result.has_value());
  EXPECT_EQ(result->module, "kernel32.dll");
  EXPECT_EQ(result->function, "VirtualAlloc");
}

TEST(ImportHashDBTest, ResolveInModuleReturnsNulloptForWrongModule) {
  omill::ImportHashDB db;
  db.loadBuiltins();

  uint32_t func_hash = omill::ImportHashDB::computeHash(
      "VirtualAlloc", omill::HashAlgorithm::FNV1a32, 0x811c9dc5u);

  // VirtualAlloc is in kernel32, not ntdll.
  auto result = db.resolveInModule("ntdll.dll", func_hash);
  EXPECT_FALSE(result.has_value());
}

TEST(ImportHashDBTest, ResolveInModuleReturnsNulloptForUnknownHash) {
  omill::ImportHashDB db;
  db.loadBuiltins();

  auto result = db.resolveInModule("kernel32.dll", 0xDEADDEADu);
  EXPECT_FALSE(result.has_value());
}

}  // namespace

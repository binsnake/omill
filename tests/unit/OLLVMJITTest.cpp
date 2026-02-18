#include <gtest/gtest.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/TargetSelect.h>

#include <cstdint>
#include <cstring>
#include <string>

#ifndef OLLVM_CLEAN_BC_PATH
#error "OLLVM_CLEAN_BC_PATH must be defined"
#endif

#ifndef OLLVM_OBF_BC_PATH
#error "OLLVM_OBF_BC_PATH must be defined"
#endif

namespace {

/// JIT-compile a bitcode file and look up a function by name.
class OLLVMJITTest : public ::testing::Test {
 protected:
  static void SetUpTestSuite() {
    static bool once = [] {
      llvm::InitializeNativeTarget();
      llvm::InitializeNativeTargetAsmPrinter();
      return true;
    }();
    (void)once;
  }

  /// Load a .bc file, JIT it, and return the address of the named function.
  /// Returns nullptr and records a GTest failure on error.
  void *jitFunction(const char *bc_path, const std::string &func_name) {
    // Load bitcode.
    auto buf_or = llvm::MemoryBuffer::getFile(bc_path);
    EXPECT_TRUE(!!buf_or) << "Failed to open: " << bc_path;
    if (!buf_or) return nullptr;

    auto ctx = std::make_unique<llvm::LLVMContext>();
    auto mod_or =
        llvm::parseBitcodeFile(buf_or.get()->getMemBufferRef(), *ctx);
    EXPECT_TRUE(!!mod_or) << "Failed to parse bitcode: " << bc_path;
    if (!mod_or) {
      llvm::consumeError(mod_or.takeError());
      return nullptr;
    }

    // Verify module.
    EXPECT_FALSE(llvm::verifyModule(**mod_or, &llvm::errs()))
        << "Module verification failed: " << bc_path;

    // Create LLJIT.
    auto jit_or = llvm::orc::LLJITBuilder().create();
    EXPECT_TRUE(!!jit_or) << "Failed to create LLJIT";
    if (!jit_or) {
      std::string err;
      llvm::raw_string_ostream os(err);
      os << jit_or.takeError();
      ADD_FAILURE() << err;
      return nullptr;
    }
    jit_ = std::move(*jit_or);

    // Add host process symbols (memcpy, memset, etc.).
    auto gen =
        llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(
            jit_->getDataLayout().getGlobalPrefix());
    if (gen)
      jit_->getMainJITDylib().addGenerator(std::move(*gen));
    else
      llvm::consumeError(gen.takeError());

    // Add module.
    llvm::orc::ThreadSafeContext ts_ctx(std::move(ctx));
    auto err = jit_->addIRModule(
        llvm::orc::ThreadSafeModule(std::move(*mod_or), ts_ctx));
    EXPECT_FALSE(!!err) << "Failed to add module to JIT";
    if (err) {
      llvm::consumeError(std::move(err));
      return nullptr;
    }

    // Look up the function.
    auto sym_or = jit_->lookup(func_name);
    EXPECT_TRUE(!!sym_or) << "Failed to look up: " << func_name;
    if (!sym_or) {
      llvm::consumeError(sym_or.takeError());
      return nullptr;
    }
    return reinterpret_cast<void *>(sym_or->getValue());
  }

  std::unique_ptr<llvm::orc::LLJIT> jit_;
};

// =============================================================================
// SHA-256 expected digest for "Hello, World!" (13 bytes).
// =============================================================================
static const uint8_t kSHA256Expected[32] = {
    0xdf, 0xfd, 0x60, 0x21, 0xbb, 0x2b, 0xd5, 0xb0, 0xaf, 0x67, 0x62,
    0x90, 0x80, 0x9e, 0xc3, 0xa5, 0x31, 0x91, 0xdd, 0x81, 0xc7, 0xf7,
    0x0a, 0x4b, 0x28, 0x68, 0x8a, 0x36, 0x21, 0x82, 0x98, 0x6f};

static std::string hexDigest(const uint8_t *d, size_t n) {
  std::string s;
  for (size_t i = 0; i < n; i++) {
    char buf[4];
    snprintf(buf, sizeof(buf), "%02x", d[i]);
    s += buf;
  }
  return s;
}

// =============================================================================
// Clean (non-obfuscated) JIT tests
// =============================================================================

TEST_F(OLLVMJITTest, Clean_Branch) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_branch");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(20), 40);
  EXPECT_EQ(fn(5), 10);
  EXPECT_EQ(fn(-3), 3);
}

TEST_F(OLLVMJITTest, Clean_Arithmetic) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_arithmetic");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int, int)>(addr);
  EXPECT_EQ(fn(5, 3), (5 + 3) ^ (5 - 3));
  EXPECT_EQ(fn(0, 0), 0);
  EXPECT_EQ(fn(100, 200), (100 + 200) ^ (100 - 200));
}

TEST_F(OLLVMJITTest, Clean_LoopSum) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_loop_sum");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(10), 55);
  EXPECT_EQ(fn(0), 0);
  EXPECT_EQ(fn(100), 5050);
}

TEST_F(OLLVMJITTest, Clean_Constants) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_constants");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(10), (((10 + 42) * 7) ^ 0xDEAD) - 100);
}

TEST_F(OLLVMJITTest, Clean_VectorArith) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_vector_arith");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int, int)>(addr);
  EXPECT_EQ(fn(5, 3), ((5 + 3) * (5 - 3)) ^ (5 & 3));
  EXPECT_EQ(fn(10, 7), ((10 + 7) * (10 - 7)) ^ (10 & 7));
}

TEST_F(OLLVMJITTest, Clean_CRC32) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_crc32");
  if (!addr) return;
  auto fn = reinterpret_cast<uint32_t (*)(const uint8_t *, uint32_t)>(addr);
  const uint8_t input[] = "Hello, World!";
  EXPECT_EQ(fn(input, 13), 0xEC4AC3D0u);
}

TEST_F(OLLVMJITTest, Clean_SHA256) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_sha256");
  if (!addr) return;
  auto fn =
      reinterpret_cast<void (*)(const uint8_t *, uint32_t, uint8_t *)>(addr);
  const uint8_t input[] = "Hello, World!";
  uint8_t digest[32] = {};
  fn(input, 13, digest);
  EXPECT_EQ(std::memcmp(digest, kSHA256Expected, 32), 0)
      << "SHA-256 mismatch:\n  got:      " << hexDigest(digest, 32)
      << "\n  expected: " << hexDigest(kSHA256Expected, 32);
}

TEST_F(OLLVMJITTest, Clean_CopyGreeting) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_copy_greeting");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(char *, int)>(addr);
  char buf[64] = {};
  int len = fn(buf, sizeof(buf));
  EXPECT_EQ(len, 18);
  EXPECT_STREQ(buf, "OLLVM Test String!");
}

// =============================================================================
// Obfuscated JIT tests — same functions after ollvm-obf.
// =============================================================================

TEST_F(OLLVMJITTest, Obfuscated_Branch) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_branch");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(20), 40);
  EXPECT_EQ(fn(5), 10);
  EXPECT_EQ(fn(-3), 3);
}

TEST_F(OLLVMJITTest, Obfuscated_Arithmetic) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_arithmetic");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int, int)>(addr);
  EXPECT_EQ(fn(5, 3), (5 + 3) ^ (5 - 3));
  EXPECT_EQ(fn(0, 0), 0);
  EXPECT_EQ(fn(100, 200), (100 + 200) ^ (100 - 200));
}

TEST_F(OLLVMJITTest, Obfuscated_LoopSum) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_loop_sum");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(10), 55);
  EXPECT_EQ(fn(0), 0);
  EXPECT_EQ(fn(100), 5050);
}

TEST_F(OLLVMJITTest, Obfuscated_Constants) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_constants");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(10), (((10 + 42) * 7) ^ 0xDEAD) - 100);
}

TEST_F(OLLVMJITTest, Obfuscated_VectorArith) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_vector_arith");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int, int)>(addr);
  EXPECT_EQ(fn(5, 3), ((5 + 3) * (5 - 3)) ^ (5 & 3));
  EXPECT_EQ(fn(10, 7), ((10 + 7) * (10 - 7)) ^ (10 & 7));
}

TEST_F(OLLVMJITTest, Obfuscated_CRC32) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_crc32");
  if (!addr) return;
  auto fn = reinterpret_cast<uint32_t (*)(const uint8_t *, uint32_t)>(addr);
  const uint8_t input[] = "Hello, World!";
  EXPECT_EQ(fn(input, 13), 0xEC4AC3D0u);
}

TEST_F(OLLVMJITTest, Obfuscated_SHA256) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_sha256");
  if (!addr) return;
  auto fn =
      reinterpret_cast<void (*)(const uint8_t *, uint32_t, uint8_t *)>(addr);
  const uint8_t input[] = "Hello, World!";
  uint8_t digest[32] = {};
  fn(input, 13, digest);
  EXPECT_EQ(std::memcmp(digest, kSHA256Expected, 32), 0)
      << "SHA-256 (obfuscated) mismatch:\n  got:      "
      << hexDigest(digest, 32)
      << "\n  expected: " << hexDigest(kSHA256Expected, 32);
}

TEST_F(OLLVMJITTest, Obfuscated_CopyGreeting) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_copy_greeting");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(char *, int)>(addr);
  char buf[64] = {};
  int len = fn(buf, sizeof(buf));
  EXPECT_EQ(len, 18);
  EXPECT_STREQ(buf, "OLLVM Test String!");
}

}  // namespace

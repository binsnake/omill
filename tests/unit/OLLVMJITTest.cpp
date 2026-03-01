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

#ifndef OLLVM_VEC_CONST_CLEAN_BC_PATH
#error "OLLVM_VEC_CONST_CLEAN_BC_PATH must be defined"
#endif

#ifndef OLLVM_VEC_CONST_OBF_BC_PATH
#error "OLLVM_VEC_CONST_OBF_BC_PATH must be defined"
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

static uint32_t refRol32(uint32_t v, unsigned n) {
  n &= 31u;
  if (n == 0u) return v;
  return (v << n) | (v >> (32u - n));
}


static uint32_t refBitwise(uint32_t x, uint32_t y) {
  uint32_t a = x ^ y;
  uint32_t b = (x & y) | (~x & ~y);
  uint32_t c = (a ^ b) & 0xFF00FF00u;
  return c ^ (x | y);
}

static int refStackHeavy(int a, int b, int c, int d) {
  int x = a + b;
  int y = c - d;
  int z = x * y;
  int w = z ^ (a | d);
  int v = w + (b & c);
  int u = v - (x ^ z);
  return u + (y | w);
}
static uint32_t refVecConstMix(const uint32_t *in) {
  const uint32_t x0 = in[0];
  const uint32_t x1 = in[1];
  const uint32_t x2 = in[2];

  uint32_t d0 = 3u * x0 + 5u * x1 + 7u * x2;
  uint32_t d1 = 11u * x0 + 13u * x1 + 17u * x2;
  uint32_t d2 = 19u * x0 + 23u * x1 + 29u * x2;

  uint32_t lanes[4];
  lanes[0] = d0;
  lanes[1] = d1;
  lanes[2] = d2;
  lanes[3] = d0 ^ d1 ^ d2;

  if (((d0 ^ d1) & 1u) != 0u) {
    uint32_t t = lanes[0];
    lanes[0] = lanes[2];
    lanes[2] = t;
    lanes[3] ^= lanes[1];
  } else {
    lanes[1] += lanes[3];
    lanes[2] ^= lanes[0];
  }

  static const uint32_t kMask[4] = {
      0xA3B1BAC6u, 0x56AA3350u, 0x677D9197u, 0xB27022DCu};
  for (unsigned i = 0; i < 4; ++i) {
    uint32_t v = lanes[i];
    v = refRol32(v ^ kMask[i], i + 3u);
    v ^= (v >> (i + 1u));
    lanes[i] = v;
  }

  uint32_t moved[4];
  moved[0] = lanes[1] ^ refRol32(lanes[3], 5u);
  moved[1] = lanes[2] + (lanes[0] & 0x00FF00FFu);
  moved[2] = lanes[3] ^ (lanes[1] >> 3u);
  moved[3] = lanes[0] + lanes[2] + 0x9E3779B9u;

  uint32_t out = moved[0];
  out = refRol32(out + moved[1], 7u);
  out ^= moved[2];
  out += (moved[3] ^ 0x85EBCA6Bu);
  return out;
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


TEST_F(OLLVMJITTest, Clean_Bitwise) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_bitwise");
  if (!addr) return;
  auto fn = reinterpret_cast<uint32_t (*)(uint32_t, uint32_t)>(addr);
  EXPECT_EQ(fn(0xA5A5A5A5u, 0x5A5A5A5Au), refBitwise(0xA5A5A5A5u, 0x5A5A5A5Au));
  EXPECT_EQ(fn(0u, 0u), refBitwise(0u, 0u));
  EXPECT_EQ(fn(123u, 456u), refBitwise(123u, 456u));
}

TEST_F(OLLVMJITTest, Clean_NestedLoops) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_nested_loops");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(0), 0);
  EXPECT_EQ(fn(1), 1);
  EXPECT_EQ(fn(4), 22);
  EXPECT_EQ(fn(5), 49);
}

TEST_F(OLLVMJITTest, Clean_Switch) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_switch");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(10), 31);   // 10%5=0 -> 10*3=30 -> 31
  EXPECT_EQ(fn(6), 14);    // 6%5=1  -> 6+7=13  -> 14
  EXPECT_EQ(fn(7), 173);   // 7%5=2  -> 7^0xAB=172 -> 173
  EXPECT_EQ(fn(8), -4);    // 8%5=3  -> 8-13=-5 -> -4
  EXPECT_EQ(fn(9), 10);    // 9%5=4  -> 9       -> 10
}

TEST_F(OLLVMJITTest, Clean_StackHeavy) {
  auto *addr = jitFunction(OLLVM_CLEAN_BC_PATH, "ollvm_stack_heavy");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int, int, int, int)>(addr);
  EXPECT_EQ(fn(1, 2, 3, 4), refStackHeavy(1, 2, 3, 4));
  EXPECT_EQ(fn(10, 20, 30, 40), refStackHeavy(10, 20, 30, 40));
  EXPECT_EQ(fn(0, 0, 0, 0), refStackHeavy(0, 0, 0, 0));
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


TEST_F(OLLVMJITTest, Obfuscated_Bitwise) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_bitwise");
  if (!addr) return;
  auto fn = reinterpret_cast<uint32_t (*)(uint32_t, uint32_t)>(addr);
  EXPECT_EQ(fn(0xA5A5A5A5u, 0x5A5A5A5Au), refBitwise(0xA5A5A5A5u, 0x5A5A5A5Au));
  EXPECT_EQ(fn(0u, 0u), refBitwise(0u, 0u));
  EXPECT_EQ(fn(123u, 456u), refBitwise(123u, 456u));
}

TEST_F(OLLVMJITTest, Obfuscated_NestedLoops) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_nested_loops");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(0), 0);
  EXPECT_EQ(fn(1), 1);
  EXPECT_EQ(fn(4), 22);
  EXPECT_EQ(fn(5), 49);
}

TEST_F(OLLVMJITTest, Obfuscated_Switch) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_switch");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int)>(addr);
  EXPECT_EQ(fn(10), 31);
  EXPECT_EQ(fn(6), 14);
  EXPECT_EQ(fn(7), 173);
  EXPECT_EQ(fn(8), -4);
  EXPECT_EQ(fn(9), 10);
}

TEST_F(OLLVMJITTest, Obfuscated_StackHeavy) {
  auto *addr = jitFunction(OLLVM_OBF_BC_PATH, "ollvm_stack_heavy");
  if (!addr) return;
  auto fn = reinterpret_cast<int (*)(int, int, int, int)>(addr);
  EXPECT_EQ(fn(1, 2, 3, 4), refStackHeavy(1, 2, 3, 4));
  EXPECT_EQ(fn(10, 20, 30, 40), refStackHeavy(10, 20, 30, 40));
  EXPECT_EQ(fn(0, 0, 0, 0), refStackHeavy(0, 0, 0, 0));
}
TEST_F(OLLVMJITTest, Clean_VectorConstMix) {
  auto *addr = jitFunction(OLLVM_VEC_CONST_CLEAN_BC_PATH, "ollvm_vec_const_mix");
  if (!addr) return;
  auto fn = reinterpret_cast<uint32_t (*)(const uint32_t *)>(addr);

  const uint32_t in0[3] = {1u, 2u, 3u};
  const uint32_t in1[3] = {0x11111111u, 0x22222222u, 0x33333333u};
  const uint32_t in2[3] = {123456789u, 42u, 987654321u};

  EXPECT_EQ(fn(in0), refVecConstMix(in0));
  EXPECT_EQ(fn(in1), refVecConstMix(in1));
  EXPECT_EQ(fn(in2), refVecConstMix(in2));
}

TEST_F(OLLVMJITTest, Obfuscated_VectorConstMix_VectorAndConstOnly) {
  auto *addr = jitFunction(OLLVM_VEC_CONST_OBF_BC_PATH, "ollvm_vec_const_mix");
  if (!addr) return;
  auto fn = reinterpret_cast<uint32_t (*)(const uint32_t *)>(addr);

  const uint32_t in0[3] = {1u, 2u, 3u};
  const uint32_t in1[3] = {0x11111111u, 0x22222222u, 0x33333333u};
  const uint32_t in2[3] = {123456789u, 42u, 987654321u};

  EXPECT_EQ(fn(in0), refVecConstMix(in0));
  EXPECT_EQ(fn(in1), refVecConstMix(in1));
  EXPECT_EQ(fn(in2), refVecConstMix(in2));
}

}  // namespace

#include "LiftAndOptFixture.h"
#include "X86Disassembler.h"

#include <gtest/gtest.h>

namespace {

using omill::e2e::LiftAndOptFixture;

class MBAPatternTest : public LiftAndOptFixture {};

/// MBA obfuscation: (x ^ y) + 2*(x & y) is equivalent to x + y.
///
/// x86_64 machine code for a function implementing this pattern:
///   mov rax, rcx      ; rax = x (first Win64 param)
///   xor rax, rdx      ; rax = x ^ y
///   mov r8, rcx       ; r8 = x
///   and r8, rdx       ; r8 = x & y
///   shl r8, 1         ; r8 = 2*(x & y)
///   add rax, r8       ; rax = (x ^ y) + 2*(x & y) = x + y
///   ret
TEST_F(MBAPatternTest, XorAndToAdd) {
  // Assembled bytes for the above sequence:
  static const uint8_t code[] = {
      0x48, 0x89, 0xc8,              // mov rax, rcx
      0x48, 0x31, 0xd0,              // xor rax, rdx
      0x49, 0x89, 0xc8,              // mov r8, rcx
      0x49, 0x21, 0xd0,              // and r8, rdx
      0x49, 0xd1, 0xe0,              // shl r8, 1
      0x4c, 0x01, 0xc0,              // add rax, r8
      0xc3,                           // ret
  };

  setCode(code, sizeof(code), 0x401000);

  // Verify disassembly works
  auto disasm = omill::e2e::disassemble(code, sizeof(code), 0x401000);
  ASSERT_FALSE(disasm.empty());
  EXPECT_EQ(disasm.back().text, "ret");

  // Lift with remill
  auto *M = lift();
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  // Run full omill pipeline (stages 1-4, no ABI recovery yet)
  omill::PipelineOptions opts;
  opts.recover_abi = false;
  optimize(opts);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // The function should still exist
  EXPECT_FALSE(traceManager().traces().empty());
}

/// MBA pattern: x * 2 implemented as (x << 1) + 0
///
///   mov rax, rcx
///   shl rax, 1
///   add rax, 0
///   ret
TEST_F(MBAPatternTest, ShiftAddZero) {
  static const uint8_t code[] = {
      0x48, 0x89, 0xc8,              // mov rax, rcx
      0x48, 0xd1, 0xe0,              // shl rax, 1
      0x48, 0x83, 0xc0, 0x00,        // add rax, 0
      0xc3,                           // ret
  };

  setCode(code, sizeof(code), 0x402000);

  auto *M = lift();
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule());

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  optimize(opts);

  EXPECT_TRUE(verifyModule());
}

}  // namespace

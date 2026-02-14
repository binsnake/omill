#include "LiftAndOptFixture.h"
#include "X86Disassembler.h"

#include <gtest/gtest.h>

namespace {

using omill::e2e::LiftAndOptFixture;

class OpaquePredicateTest : public LiftAndOptFixture {};

/// Opaque predicate: x*(x+1) is always even, so (x*(x+1)) & 1 == 0 always.
///
/// x86_64 machine code:
///   mov rax, rcx       ; rax = x
///   lea rdx, [rcx+1]   ; rdx = x + 1
///   imul rax, rdx       ; rax = x * (x + 1)
///   test al, 1          ; check if bit 0 is set
///   jnz .fake_path      ; always-false branch (opaque predicate)
///   mov eax, 1          ; true path: return 1
///   ret
/// .fake_path:
///   mov eax, 0          ; fake path: return 0
///   ret
TEST_F(OpaquePredicateTest, AlwaysEvenProduct) {
  static const uint8_t code[] = {
      0x48, 0x89, 0xc8,              // mov rax, rcx
      0x48, 0x8d, 0x51, 0x01,        // lea rdx, [rcx+1]
      0x48, 0x0f, 0xaf, 0xc2,        // imul rax, rdx
      0xa8, 0x01,                     // test al, 1
      0x75, 0x06,                     // jnz +6 (to fake_path)
      0xb8, 0x01, 0x00, 0x00, 0x00,  // mov eax, 1
      0xc3,                           // ret
      0xb8, 0x00, 0x00, 0x00, 0x00,  // mov eax, 0
      0xc3,                           // ret
  };

  setCode(code, sizeof(code), 0x401000);

  auto disasm = omill::e2e::disassemble(code, sizeof(code), 0x401000);
  ASSERT_FALSE(disasm.empty());

  auto *M = lift();
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  // Run omill pipeline — pipeline should handle both paths cleanly
  omill::PipelineOptions opts;
  opts.recover_abi = false;
  optimize(opts);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
}

/// Simple always-true predicate: x | ~x == -1, so always jumps.
///
///   mov rax, rcx
///   mov rdx, rcx
///   not rdx
///   or rax, rdx         ; rax = x | ~x = 0xFFFF...
///   cmp rax, -1
///   je .true_path        ; always taken
///   xor eax, eax         ; dead path
///   ret
/// .true_path:
///   mov eax, 42
///   ret
TEST_F(OpaquePredicateTest, OrNotAlwaysTrue) {
  static const uint8_t code[] = {
      0x48, 0x89, 0xc8,              // mov rax, rcx
      0x48, 0x89, 0xca,              // mov rdx, rcx
      0x48, 0xf7, 0xd2,              // not rdx
      0x48, 0x09, 0xd0,              // or rax, rdx
      0x48, 0x83, 0xf8, 0xff,        // cmp rax, -1
      0x74, 0x04,                     // je +4 (to true_path)
      0x31, 0xc0,                     // xor eax, eax
      0xc3,                           // ret
      0xb8, 0x2a, 0x00, 0x00, 0x00,  // mov eax, 42
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

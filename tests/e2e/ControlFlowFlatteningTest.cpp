#include "LiftAndOptFixture.h"
#include "X86Disassembler.h"

#include <gtest/gtest.h>

namespace {

using omill::e2e::LiftAndOptFixture;

class ControlFlowFlatteningTest : public LiftAndOptFixture {};

/// Simple control flow flattening pattern: a switch-based dispatcher that
/// selects between different "state" blocks.
///
/// Simplified version — a function with a basic compare-and-branch chain
/// that simulates a state machine:
///
///   mov eax, 1          ; state_var = 1
/// .dispatcher:
///   cmp eax, 1
///   je .block1
///   cmp eax, 2
///   je .block2
///   ret
/// .block1:
///   add ecx, 10         ; do work
///   mov eax, 2          ; transition to state 2
///   jmp .dispatcher
/// .block2:
///   add ecx, 20         ; do work
///   mov eax, ecx        ; return value
///   ret
TEST_F(ControlFlowFlatteningTest, SimpleDispatcher) {
  static const uint8_t code[] = {
      // mov eax, 1
      0xb8, 0x01, 0x00, 0x00, 0x00,
      // .dispatcher (+5):
      // cmp eax, 1
      0x83, 0xf8, 0x01,
      // je .block1 (+14) -> offset = +6
      0x74, 0x06,
      // cmp eax, 2
      0x83, 0xf8, 0x02,
      // je .block2 (+24) -> offset = +10
      0x74, 0x0a,
      // ret
      0xc3,
      // .block1 (+16):
      // add ecx, 10
      0x83, 0xc1, 0x0a,
      // mov eax, 2
      0xb8, 0x02, 0x00, 0x00, 0x00,
      // jmp .dispatcher -> offset = -(24-5) = -19 (0xed)
      0xeb, 0xed,
      // .block2 (+26):
      // add ecx, 20
      0x83, 0xc1, 0x14,
      // mov eax, ecx
      0x89, 0xc8,
      // ret
      0xc3,
  };

  setCode(code, sizeof(code), 0x401000);

  auto disasm = omill::e2e::disassemble(code, sizeof(code), 0x401000);
  ASSERT_FALSE(disasm.empty());

  auto *M = lift();
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  // Run omill pipeline — should handle the back-edge and multiple blocks
  omill::PipelineOptions opts;
  opts.recover_abi = false;
  optimize(opts);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
}

/// Linear control flow with no branches — simplest possible function.
/// This exercises the pipeline with a single basic block.
///
///   mov rax, rcx
///   add rax, rdx
///   ret
TEST_F(ControlFlowFlatteningTest, LinearControlFlow) {
  static const uint8_t code[] = {
      0x48, 0x89, 0xc8,  // mov rax, rcx
      0x48, 0x01, 0xd0,  // add rax, rdx
      0xc3,              // ret
  };

  setCode(code, sizeof(code), 0x401000);

  auto *M = lift();
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule());

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  optimize(opts);

  EXPECT_TRUE(verifyModule());
}

}  // namespace

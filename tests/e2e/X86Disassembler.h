#pragma once

#include <Zydis/Zydis.h>

#include <cstdint>
#include <string>
#include <vector>

namespace omill::e2e {

/// A single disassembled instruction.
struct DisasmInsn {
  uint64_t addr;
  uint8_t len;
  std::string text;
};

/// Thin Zydis wrapper for disassembling x86_64 code.
/// Used for displaying/debugging, not for lifting (remill handles that).
inline std::vector<DisasmInsn> disassemble(const uint8_t *data, size_t size,
                                            uint64_t base_addr) {
  std::vector<DisasmInsn> result;

  ZydisDecoder decoder;
  ZydisDecoderInit(&decoder, ZYDIS_MACHINE_MODE_LONG_64,
                   ZYDIS_STACK_WIDTH_64);

  ZydisFormatter formatter;
  ZydisFormatterInit(&formatter, ZYDIS_FORMATTER_STYLE_INTEL);

  ZydisDecodedInstruction instruction;
  ZydisDecodedOperand operands[ZYDIS_MAX_OPERAND_COUNT];

  uint64_t offset = 0;
  while (offset < size) {
    if (ZYAN_SUCCESS(ZydisDecoderDecodeFull(&decoder, data + offset,
                                             size - offset, &instruction,
                                             operands))) {
      char buffer[256];
      ZydisFormatterFormatInstruction(&formatter, &instruction, operands,
                                      instruction.operand_count_visible,
                                      buffer, sizeof(buffer),
                                      base_addr + offset, ZYAN_NULL);

      DisasmInsn insn;
      insn.addr = base_addr + offset;
      insn.len = instruction.length;
      insn.text = buffer;
      result.push_back(std::move(insn));

      offset += instruction.length;
    } else {
      // Skip invalid byte
      DisasmInsn insn;
      insn.addr = base_addr + offset;
      insn.len = 1;
      insn.text = "db 0x" + std::to_string(data[offset]);
      result.push_back(std::move(insn));
      offset++;
    }
  }

  return result;
}

}  // namespace omill::e2e

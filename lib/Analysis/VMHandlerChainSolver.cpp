#include "omill/Analysis/VMHandlerChainSolver.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <array>
#include <cassert>
#include <cstring>
#include <deque>
#include <unordered_map>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

// ============================================================================
// x86-64 Mini-Emulator
// ============================================================================

namespace {

/// Register indices matching x86 encoding order.
enum RegIdx : uint8_t {
  RAX = 0, RCX, RDX, RBX, RSP, RBP, RSI, RDI,
  R8, R9, R10, R11, R12, R13, R14, R15,
  REG_COUNT
};

/// Sentinel value for register-derived vmcontext slots.
static constexpr uint64_t kSentinel = 0xDEADBEEFDEADBEEF;

/// x86 flags we track.
struct Flags {
  bool CF = false;
  bool ZF = false;
  bool SF = false;
  bool OF = false;
};

/// Emulator state: registers, flags, rip, and memory.
struct EmuState {
  uint64_t regs[REG_COUNT] = {};
  Flags flags;
  uint64_t rip = 0;

  /// Flat memory buffer for vmcontext + handler stack.
  /// The stack grows downward from stack_top toward stack_base.
  static constexpr uint64_t kStackBase = 0x7FFE00000000ULL;
  static constexpr size_t kStackSize = 0x10000;  // 64 KB
  std::array<uint8_t, kStackSize> stack_mem = {};

  bool isStackAddr(uint64_t addr) const {
    return addr >= kStackBase && addr < kStackBase + kStackSize;
  }

  uint8_t *stackPtr(uint64_t addr) {
    return &stack_mem[static_cast<size_t>(addr - kStackBase)];
  }

  const uint8_t *stackPtr(uint64_t addr) const {
    return &stack_mem[static_cast<size_t>(addr - kStackBase)];
  }
};

/// Decoded operand.
struct Operand {
  enum Kind { REG, IMM, MEM } kind = REG;
  uint8_t reg = 0;       ///< Register index for REG operands.
  uint64_t imm = 0;      ///< Immediate value.
  uint8_t size = 8;      ///< Operand size in bytes (1/2/4/8).

  // For MEM operands: [base + index*scale + disp]
  uint8_t base_reg = 0;
  uint8_t index_reg = 0;
  uint8_t scale = 1;
  int64_t disp = 0;
  bool has_base = false;
  bool has_index = false;
  bool rip_relative = false;
};

/// Read an integer from state memory or binary memory.
static uint64_t readMem(const EmuState &state, const BinaryMemoryMap &mem,
                        uint64_t addr, unsigned size) {
  uint64_t val = 0;
  if (state.isStackAddr(addr) &&
      state.isStackAddr(addr + size - 1)) {
    std::memcpy(&val, state.stackPtr(addr), size);
  } else {
    // Try binary memory.
    if (!mem.read(addr, reinterpret_cast<uint8_t *>(&val), size))
      val = 0;  // Unknown memory returns 0.
  }
  return val;
}

/// Write an integer to state memory.
static void writeMem(EmuState &state, uint64_t addr, uint64_t val,
                     unsigned size) {
  if (state.isStackAddr(addr) &&
      state.isStackAddr(addr + size - 1)) {
    std::memcpy(state.stackPtr(addr), &val, size);
  }
  // Writes to non-stack addresses are silently dropped.
}

/// Compute effective address for a memory operand.
static uint64_t computeEA(const EmuState &state, const Operand &op) {
  uint64_t addr = 0;
  if (op.has_base)
    addr += state.regs[op.base_reg];
  if (op.has_index)
    addr += state.regs[op.index_reg] * op.scale;
  addr += static_cast<uint64_t>(op.disp);
  if (op.rip_relative)
    addr += state.rip;  // rip already advanced past instruction
  return addr;
}

/// Read operand value.
static uint64_t readOp(const EmuState &state, const BinaryMemoryMap &mem,
                       const Operand &op) {
  switch (op.kind) {
    case Operand::REG: {
      uint64_t val = state.regs[op.reg];
      if (op.size == 4) return val & 0xFFFFFFFF;
      if (op.size == 2) return val & 0xFFFF;
      if (op.size == 1) {
        // AL/CL/DL/BL for reg < 4, else SPL/BPL/SIL/DIL or R8B..R15B
        return val & 0xFF;
      }
      return val;
    }
    case Operand::IMM:
      return op.imm;
    case Operand::MEM: {
      uint64_t addr = computeEA(state, op);
      return readMem(state, mem, addr, op.size);
    }
  }
  return 0;
}

/// Write operand value.
static void writeOp(EmuState &state, const Operand &op, uint64_t val) {
  switch (op.kind) {
    case Operand::REG:
      if (op.size == 4)
        state.regs[op.reg] = val & 0xFFFFFFFF;  // zero-extend to 64
      else if (op.size == 2)
        state.regs[op.reg] =
            (state.regs[op.reg] & ~0xFFFFULL) | (val & 0xFFFF);
      else if (op.size == 1)
        state.regs[op.reg] =
            (state.regs[op.reg] & ~0xFFULL) | (val & 0xFF);
      else
        state.regs[op.reg] = val;
      break;
    case Operand::MEM: {
      uint64_t addr = computeEA(state, op);
      writeMem(state, addr, val, op.size);
      break;
    }
    case Operand::IMM:
      break;  // Can't write to immediate.
  }
}

/// Mask value to operand size bits.
static uint64_t maskToSize(uint64_t val, unsigned size) {
  switch (size) {
    case 1: return val & 0xFF;
    case 2: return val & 0xFFFF;
    case 4: return val & 0xFFFFFFFF;
    default: return val;
  }
}

/// Sign-extend a value from the given byte width to 64 bits.
static int64_t signExtend(uint64_t val, unsigned size) {
  switch (size) {
    case 1: return static_cast<int64_t>(static_cast<int8_t>(val));
    case 2: return static_cast<int64_t>(static_cast<int16_t>(val));
    case 4: return static_cast<int64_t>(static_cast<int32_t>(val));
    default: return static_cast<int64_t>(val);
  }
}

/// Update arithmetic flags for ADD/SUB results.
static void updateFlagsArith(Flags &f, uint64_t a, uint64_t b, uint64_t res,
                             unsigned size, bool is_sub) {
  uint64_t msb = 1ULL << (size * 8 - 1);
  res = maskToSize(res, size);
  a = maskToSize(a, size);
  b = maskToSize(b, size);

  f.ZF = (res == 0);
  f.SF = (res & msb) != 0;

  if (is_sub) {
    f.CF = a < b;
    f.OF = (((a ^ b) & (a ^ res)) & msb) != 0;
  } else {
    f.CF = (res < a) || (res < b);
    f.OF = (((~(a ^ b)) & (a ^ res)) & msb) != 0;
  }
}

/// Update logical flags (AND/OR/XOR/TEST).
static void updateFlagsLogical(Flags &f, uint64_t res, unsigned size) {
  uint64_t msb = 1ULL << (size * 8 - 1);
  res = maskToSize(res, size);
  f.ZF = (res == 0);
  f.SF = (res & msb) != 0;
  f.CF = false;
  f.OF = false;
}

/// Evaluate a SETcc condition code.
static bool evaluateCC(uint8_t cc, const Flags &f) {
  switch (cc & 0x0F) {
    case 0x0: return f.OF;                     // O
    case 0x1: return !f.OF;                    // NO
    case 0x2: return f.CF;                     // B/C/NAE
    case 0x3: return !f.CF;                    // NB/NC/AE
    case 0x4: return f.ZF;                     // Z/E
    case 0x5: return !f.ZF;                    // NZ/NE
    case 0x6: return f.CF || f.ZF;             // BE/NA
    case 0x7: return !f.CF && !f.ZF;           // NBE/A
    case 0x8: return f.SF;                     // S
    case 0x9: return !f.SF;                    // NS
    case 0xA: return false;                    // P (not tracked)
    case 0xB: return false;                    // NP (not tracked)
    case 0xC: return f.SF != f.OF;             // L/NGE
    case 0xD: return f.SF == f.OF;             // NL/GE
    case 0xE: return f.ZF || (f.SF != f.OF);  // LE/NG
    case 0xF: return !f.ZF && (f.SF == f.OF); // NLE/G
    default: return false;
  }
}

// ============================================================================
// x86-64 Instruction Decoder + Executor
// ============================================================================

/// Decode ModRM byte and optional SIB + displacement into an Operand.
/// Returns number of bytes consumed (including ModRM).
static unsigned decodeModRM(const uint8_t *bytes, unsigned size,
                            bool has_rex, uint8_t rex, unsigned op_size,
                            Operand &op, uint8_t &reg_field) {
  if (size < 1) return 0;

  uint8_t modrm = bytes[0];
  uint8_t mod = (modrm >> 6) & 3;
  reg_field = (modrm >> 3) & 7;
  uint8_t rm = modrm & 7;

  // REX.R extends reg_field.
  if (has_rex && (rex & 0x04))
    reg_field |= 8;

  unsigned consumed = 1;

  if (mod == 3) {
    // Register direct.
    op.kind = Operand::REG;
    op.reg = rm;
    if (has_rex && (rex & 0x01))
      op.reg |= 8;
    op.size = op_size;
    return consumed;
  }

  // Memory operand.
  op.kind = Operand::MEM;
  op.size = op_size;
  op.has_base = true;
  op.has_index = false;
  op.disp = 0;
  op.rip_relative = false;

  if (rm == 4) {
    // SIB byte follows.
    if (consumed >= size) return 0;
    uint8_t sib = bytes[consumed++];
    uint8_t sib_scale = (sib >> 6) & 3;
    uint8_t sib_index = (sib >> 3) & 7;
    uint8_t sib_base = sib & 7;

    if (has_rex && (rex & 0x01))
      sib_base |= 8;
    if (has_rex && (rex & 0x02))
      sib_index |= 8;

    op.scale = 1 << sib_scale;

    if (sib_index != 4) {  // RSP can't be index
      op.has_index = true;
      op.index_reg = sib_index;
    }

    if (mod == 0 && (sib_base & 7) == 5) {
      // disp32 with no base.
      op.has_base = false;
      if (consumed + 4 > size) return 0;
      int32_t d32;
      std::memcpy(&d32, &bytes[consumed], 4);
      consumed += 4;
      op.disp = d32;
    } else {
      op.base_reg = sib_base;
    }
  } else if (mod == 0 && rm == 5) {
    // RIP-relative (disp32).
    op.has_base = false;
    op.rip_relative = true;
    if (consumed + 4 > size) return 0;
    int32_t d32;
    std::memcpy(&d32, &bytes[consumed], 4);
    consumed += 4;
    op.disp = d32;
    return consumed;
  } else {
    op.base_reg = rm;
    if (has_rex && (rex & 0x01))
      op.base_reg |= 8;
  }

  // Displacement.
  if (mod == 1) {
    if (consumed >= size) return 0;
    op.disp = static_cast<int8_t>(bytes[consumed++]);
  } else if (mod == 2) {
    if (consumed + 4 > size) return 0;
    int32_t d32;
    std::memcpy(&d32, &bytes[consumed], 4);
    consumed += 4;
    op.disp = d32;
  }

  return consumed;
}

/// Result of executing one instruction.
enum class ExecResult {
  Continue,     ///< Normal execution, advance to next instruction.
  Jump,         ///< rip was modified by the instruction.
  IndirectJump, ///< Indirect jump (jmp reg) — potential dispatch.
  Call,         ///< Direct call instruction.
  Ret,          ///< Return instruction.
  Unsupported,  ///< Unhandled instruction form.
};

/// Decode and execute one instruction at state.rip.
/// Returns the execution result and advances rip.
static ExecResult stepInstruction(EmuState &state,
                                  const BinaryMemoryMap &mem) {
  uint8_t buf[15];
  if (!mem.read(state.rip, buf, 15))
    return ExecResult::Unsupported;

  unsigned pos = 0;
  uint64_t inst_start = state.rip;

  // --- Prefix parsing ---
  bool has_rex = false;
  uint8_t rex = 0;
  bool has_66 = false;  // operand size override

  // Check for 66h prefix.
  if (buf[pos] == 0x66) {
    has_66 = true;
    pos++;
  }

  // Check for REX prefix (40h-4Fh).
  if ((buf[pos] & 0xF0) == 0x40) {
    has_rex = true;
    rex = buf[pos++];
  }

  bool rex_w = has_rex && (rex & 0x08);
  unsigned default_op_size = rex_w ? 8 : (has_66 ? 2 : 4);

  uint8_t opcode = buf[pos++];

  // ---- Two-byte opcode (0F xx) ----
  if (opcode == 0x0F) {
    uint8_t opcode2 = buf[pos++];

    // SETcc r/m8: 0F 9x
    if ((opcode2 & 0xF0) == 0x90) {
      uint8_t reg_field;
      Operand dst;
      unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex, 1,
                               dst, reg_field);
      if (n == 0) return ExecResult::Unsupported;
      pos += n;
      state.rip = inst_start + pos;

      bool cond = evaluateCC(opcode2, state.flags);
      writeOp(state, dst, cond ? 1 : 0);
      return ExecResult::Continue;
    }

    // MOVUPS xmm, xmm/m128: 0F 10
    // MOVUPS xmm/m128, xmm: 0F 11
    if (opcode2 == 0x10 || opcode2 == 0x11) {
      uint8_t reg_field;
      Operand rm;
      unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex, 16,
                               rm, reg_field);
      if (n == 0) return ExecResult::Unsupported;
      pos += n;
      state.rip = inst_start + pos;

      if (rm.kind == Operand::MEM) {
        uint64_t addr = computeEA(state, rm);
        if (opcode2 == 0x10) {
          // Load xmm — we don't track XMM, just skip.
        } else {
          // Store xmm — write 16 zero bytes (we don't track XMM).
          uint64_t zero = 0;
          writeMem(state, addr, zero, 8);
          writeMem(state, addr + 8, zero, 8);
        }
      }
      return ExecResult::Continue;
    }

    // IMUL r64, r/m64: 0F AF
    if (opcode2 == 0xAF) {
      uint8_t reg_field;
      Operand src;
      unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                               default_op_size, src, reg_field);
      if (n == 0) return ExecResult::Unsupported;
      pos += n;
      state.rip = inst_start + pos;

      uint64_t a = state.regs[reg_field];
      uint64_t b = readOp(state, mem, src);
      uint64_t res = a * b;
      if (default_op_size == 4) res &= 0xFFFFFFFF;
      state.regs[reg_field] = (default_op_size == 4) ? (res & 0xFFFFFFFF) : res;
      return ExecResult::Continue;
    }

    // Jcc rel32: 0F 8x
    if ((opcode2 & 0xF0) == 0x80) {
      if (pos + 4 > 15) return ExecResult::Unsupported;
      int32_t rel32;
      std::memcpy(&rel32, &buf[pos], 4);
      pos += 4;
      state.rip = inst_start + pos;

      bool cond = evaluateCC(opcode2, state.flags);
      if (cond)
        state.rip = state.rip + static_cast<int64_t>(rel32);
      return ExecResult::Jump;
    }

    // MOVZX r32/64, r/m8: 0F B6
    // MOVZX r32/64, r/m16: 0F B7
    if (opcode2 == 0xB6 || opcode2 == 0xB7) {
      uint8_t src_size = (opcode2 == 0xB6) ? 1 : 2;
      uint8_t reg_field;
      Operand src;
      unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                               src_size, src, reg_field);
      if (n == 0) return ExecResult::Unsupported;
      pos += n;
      state.rip = inst_start + pos;

      uint64_t val = readOp(state, mem, src);
      // MOVZX to 32 or 64 bit: if no REX.W, result is zero-extended 32→64.
      state.regs[reg_field] = maskToSize(val, src_size);
      return ExecResult::Continue;
    }

    return ExecResult::Unsupported;
  }

  // ---- One-byte opcodes ----

  // NOP (0x90) / XCHG eax, eax
  if (opcode == 0x90 && !has_rex) {
    state.rip = inst_start + pos;
    return ExecResult::Continue;
  }

  // MOV r64, imm64: B8+rd (REX.W B8+r)
  // MOV r32, imm32: B8+rd
  if (opcode >= 0xB8 && opcode <= 0xBF) {
    uint8_t reg = (opcode - 0xB8);
    if (has_rex && (rex & 0x01))
      reg |= 8;
    if (rex_w) {
      // 64-bit immediate.
      if (pos + 8 > 15) return ExecResult::Unsupported;
      uint64_t imm64;
      std::memcpy(&imm64, &buf[pos], 8);
      pos += 8;
      state.regs[reg] = imm64;
    } else {
      // 32-bit immediate, zero-extended.
      if (pos + 4 > 15) return ExecResult::Unsupported;
      uint32_t imm32;
      std::memcpy(&imm32, &buf[pos], 4);
      pos += 4;
      state.regs[reg] = imm32;
    }
    state.rip = inst_start + pos;
    return ExecResult::Continue;
  }

  // MOV r8, imm8: B0+rb
  if (opcode >= 0xB0 && opcode <= 0xB7) {
    uint8_t reg = (opcode - 0xB0);
    if (has_rex && (rex & 0x01))
      reg |= 8;
    if (pos >= 15) return ExecResult::Unsupported;
    uint8_t imm8 = buf[pos++];
    state.rip = inst_start + pos;
    Operand dst;
    dst.kind = Operand::REG;
    dst.reg = reg;
    dst.size = 1;
    writeOp(state, dst, imm8);
    return ExecResult::Continue;
  }

  // PUSH r64: 50+rd
  if (opcode >= 0x50 && opcode <= 0x57) {
    uint8_t reg = (opcode - 0x50);
    if (has_rex && (rex & 0x01))
      reg |= 8;
    state.rip = inst_start + pos;
    state.regs[RSP] -= 8;
    writeMem(state, state.regs[RSP], state.regs[reg], 8);
    return ExecResult::Continue;
  }

  // POP r64: 58+rd
  if (opcode >= 0x58 && opcode <= 0x5F) {
    uint8_t reg = (opcode - 0x58);
    if (has_rex && (rex & 0x01))
      reg |= 8;
    state.rip = inst_start + pos;
    state.regs[reg] = readMem(state, mem, state.regs[RSP], 8);
    state.regs[RSP] += 8;
    return ExecResult::Continue;
  }

  // RET: C3
  if (opcode == 0xC3) {
    state.rip = readMem(state, mem, state.regs[RSP], 8);
    state.regs[RSP] += 8;
    return ExecResult::Ret;
  }

  // CALL rel32: E8
  if (opcode == 0xE8) {
    if (pos + 4 > 15) return ExecResult::Unsupported;
    int32_t rel32;
    std::memcpy(&rel32, &buf[pos], 4);
    pos += 4;
    uint64_t ret_addr = inst_start + pos;
    state.rip = ret_addr + static_cast<int64_t>(rel32);
    state.regs[RSP] -= 8;
    writeMem(state, state.regs[RSP], ret_addr, 8);
    return ExecResult::Call;
  }

  // JMP rel32: E9
  if (opcode == 0xE9) {
    if (pos + 4 > 15) return ExecResult::Unsupported;
    int32_t rel32;
    std::memcpy(&rel32, &buf[pos], 4);
    pos += 4;
    state.rip = inst_start + pos + static_cast<int64_t>(rel32);
    return ExecResult::Jump;
  }

  // JMP rel8: EB
  if (opcode == 0xEB) {
    if (pos >= 15) return ExecResult::Unsupported;
    int8_t rel8 = static_cast<int8_t>(buf[pos++]);
    state.rip = inst_start + pos + static_cast<int64_t>(rel8);
    return ExecResult::Jump;
  }

  // Jcc rel8: 70-7F
  if (opcode >= 0x70 && opcode <= 0x7F) {
    if (pos >= 15) return ExecResult::Unsupported;
    int8_t rel8 = static_cast<int8_t>(buf[pos++]);
    state.rip = inst_start + pos;
    bool cond = evaluateCC(opcode, state.flags);
    if (cond)
      state.rip = state.rip + static_cast<int64_t>(rel8);
    return ExecResult::Jump;
  }

  // PUSHFQ: 9C
  if (opcode == 0x9C) {
    state.rip = inst_start + pos;
    uint64_t rflags = 0x202;  // Reserved bit 1 always set, IF set.
    if (state.flags.CF) rflags |= 0x001;
    if (state.flags.ZF) rflags |= 0x040;
    if (state.flags.SF) rflags |= 0x080;
    if (state.flags.OF) rflags |= 0x800;
    state.regs[RSP] -= 8;
    writeMem(state, state.regs[RSP], rflags, 8);
    return ExecResult::Continue;
  }

  // POPFQ: 9D
  if (opcode == 0x9D) {
    state.rip = inst_start + pos;
    uint64_t rflags = readMem(state, mem, state.regs[RSP], 8);
    state.regs[RSP] += 8;
    state.flags.CF = (rflags & 0x001) != 0;
    state.flags.ZF = (rflags & 0x040) != 0;
    state.flags.SF = (rflags & 0x080) != 0;
    state.flags.OF = (rflags & 0x800) != 0;
    return ExecResult::Continue;
  }

  // ---- ALU ops with ModRM: opcode r/m, reg  or  opcode reg, r/m ----
  // ADD: 01/03, SUB: 29/2B, XOR: 31/33, AND: 21/23, OR: 09/0B, CMP: 39/3B
  // ADC: 11/13
  auto handleALU = [&](uint8_t op_type, bool dir_reg_to_rm) -> ExecResult {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    state.rip = inst_start + pos;

    Operand reg_op;
    reg_op.kind = Operand::REG;
    reg_op.reg = reg_field;
    reg_op.size = default_op_size;

    Operand &dst = dir_reg_to_rm ? rm : reg_op;
    Operand &src = dir_reg_to_rm ? reg_op : rm;

    uint64_t a = readOp(state, mem, dst);
    uint64_t b = readOp(state, mem, src);
    uint64_t res;

    switch (op_type) {
      case 0:  // ADD
        res = a + b;
        updateFlagsArith(state.flags, a, b, res, dst.size, false);
        break;
      case 1:  // SUB
        res = a - b;
        updateFlagsArith(state.flags, a, b, res, dst.size, true);
        break;
      case 2:  // XOR
        res = a ^ b;
        updateFlagsLogical(state.flags, res, dst.size);
        break;
      case 3:  // AND
        res = a & b;
        updateFlagsLogical(state.flags, res, dst.size);
        break;
      case 4:  // OR
        res = a | b;
        updateFlagsLogical(state.flags, res, dst.size);
        break;
      case 5:  // CMP (SUB without write)
        res = a - b;
        updateFlagsArith(state.flags, a, b, res, dst.size, true);
        return ExecResult::Continue;
      case 6:  // ADC
        res = a + b + (state.flags.CF ? 1 : 0);
        updateFlagsArith(state.flags, a, b + (state.flags.CF ? 1 : 0),
                         res, dst.size, false);
        break;
      default:
        return ExecResult::Unsupported;
    }

    writeOp(state, dst, maskToSize(res, dst.size));
    return ExecResult::Continue;
  };

  // Dispatch ALU by opcode.
  // Byte forms (0x00/02/08/0A/...) force 1-byte operand size.
  auto handleALU_byte = [&](uint8_t op_type, bool dir) -> ExecResult {
    // Force byte operand size: override default_op_size for this call.
    unsigned saved = default_op_size;
    default_op_size = 1;
    auto r = handleALU(op_type, dir);
    default_op_size = saved;
    return r;
  };

  switch (opcode) {
    case 0x00: return handleALU_byte(0, true);  // ADD r/m8, reg8
    case 0x01: return handleALU(0, true);       // ADD r/m, reg
    case 0x02: return handleALU_byte(0, false); // ADD reg8, r/m8
    case 0x03: return handleALU(0, false);      // ADD reg, r/m
    case 0x08: return handleALU_byte(4, true);  // OR r/m8, reg8
    case 0x09: return handleALU(4, true);       // OR r/m, reg
    case 0x0A: return handleALU_byte(4, false); // OR reg8, r/m8
    case 0x0B: return handleALU(4, false);      // OR reg, r/m
    case 0x10: return handleALU_byte(6, true);  // ADC r/m8, reg8
    case 0x11: return handleALU(6, true);       // ADC r/m, reg
    case 0x12: return handleALU_byte(6, false); // ADC reg8, r/m8
    case 0x13: return handleALU(6, false);      // ADC reg, r/m
    case 0x20: return handleALU_byte(3, true);  // AND r/m8, reg8
    case 0x21: return handleALU(3, true);       // AND r/m, reg
    case 0x22: return handleALU_byte(3, false); // AND reg8, r/m8
    case 0x23: return handleALU(3, false);      // AND reg, r/m
    case 0x28: return handleALU_byte(1, true);  // SUB r/m8, reg8
    case 0x29: return handleALU(1, true);       // SUB r/m, reg
    case 0x2A: return handleALU_byte(1, false); // SUB reg8, r/m8
    case 0x2B: return handleALU(1, false);      // SUB reg, r/m
    case 0x30: return handleALU_byte(2, true);  // XOR r/m8, reg8
    case 0x31: return handleALU(2, true);       // XOR r/m, reg
    case 0x32: return handleALU_byte(2, false); // XOR reg8, r/m8
    case 0x33: return handleALU(2, false);      // XOR reg, r/m
    case 0x38: return handleALU_byte(5, true);  // CMP r/m8, reg8
    case 0x39: return handleALU(5, true);       // CMP r/m, reg
    case 0x3A: return handleALU_byte(5, false); // CMP reg8, r/m8
    case 0x3B: return handleALU(5, false);      // CMP reg, r/m
    default: break;
  }

  // Accumulator-immediate ALU forms: OP AL/AX/EAX/RAX, imm8/imm16/imm32
  // 04/05=ADD, 0C/0D=OR, 14/15=ADC, 24/25=AND, 2C/2D=SUB, 34/35=XOR, 3C/3D=CMP
  {
    int alu_op = -1;
    bool is_byte = false;
    switch (opcode) {
      case 0x04: alu_op = 0; is_byte = true; break;  // ADD AL, imm8
      case 0x05: alu_op = 0; break;                   // ADD EAX, imm32
      case 0x0C: alu_op = 4; is_byte = true; break;  // OR AL, imm8
      case 0x0D: alu_op = 4; break;                   // OR EAX, imm32
      case 0x14: alu_op = 6; is_byte = true; break;  // ADC AL, imm8
      case 0x15: alu_op = 6; break;                   // ADC EAX, imm32
      case 0x24: alu_op = 3; is_byte = true; break;  // AND AL, imm8
      case 0x25: alu_op = 3; break;                   // AND EAX, imm32
      case 0x2C: alu_op = 1; is_byte = true; break;  // SUB AL, imm8
      case 0x2D: alu_op = 1; break;                   // SUB EAX, imm32
      case 0x34: alu_op = 2; is_byte = true; break;  // XOR AL, imm8
      case 0x35: alu_op = 2; break;                   // XOR EAX, imm32
      case 0x3C: alu_op = 5; is_byte = true; break;  // CMP AL, imm8
      case 0x3D: alu_op = 5; break;                   // CMP EAX, imm32
      default: break;
    }
    if (alu_op >= 0) {
      unsigned op_size = is_byte ? 1 : default_op_size;
      unsigned imm_bytes = is_byte ? 1 : (default_op_size == 8 ? 4 : default_op_size);
      if (pos + imm_bytes > 15) return ExecResult::Unsupported;

      uint64_t imm = 0;
      std::memcpy(&imm, &buf[pos], imm_bytes);
      // Sign-extend imm32 to 64-bit when REX.W is set.
      if (default_op_size == 8 && imm_bytes == 4)
        imm = static_cast<uint64_t>(static_cast<int64_t>(
            static_cast<int32_t>(imm & 0xFFFFFFFF)));
      pos += imm_bytes;
      state.rip = inst_start + pos;

      uint64_t a = (op_size == 1) ? (state.regs[RAX] & 0xFF)
                 : (op_size == 2) ? (state.regs[RAX] & 0xFFFF)
                 : (op_size == 4) ? (state.regs[RAX] & 0xFFFFFFFF)
                 : state.regs[RAX];
      uint64_t b = imm;
      uint64_t res;
      bool is_cmp = false;

      switch (alu_op) {
        case 0: res = a + b; updateFlagsArith(state.flags, a, b, res, op_size, false); break;
        case 1: res = a - b; updateFlagsArith(state.flags, a, b, res, op_size, true); break;
        case 2: res = a ^ b; updateFlagsLogical(state.flags, res, op_size); break;
        case 3: res = a & b; updateFlagsLogical(state.flags, res, op_size); break;
        case 4: res = a | b; updateFlagsLogical(state.flags, res, op_size); break;
        case 5: res = a - b; updateFlagsArith(state.flags, a, b, res, op_size, true); is_cmp = true; break;
        case 6: res = a + b + (state.flags.CF ? 1 : 0);
                updateFlagsArith(state.flags, a, b + (state.flags.CF ? 1 : 0), res, op_size, false); break;
        default: return ExecResult::Unsupported;
      }

      if (!is_cmp) {
        res = maskToSize(res, op_size);
        if (op_size == 1)
          state.regs[RAX] = (state.regs[RAX] & ~0xFFULL) | res;
        else if (op_size == 2)
          state.regs[RAX] = (state.regs[RAX] & ~0xFFFFULL) | res;
        else if (op_size == 4)
          state.regs[RAX] = res;  // zero-extend to 64
        else
          state.regs[RAX] = res;
      }
      return ExecResult::Continue;
    }
  }

  // TEST r/m, reg: 85
  if (opcode == 0x85) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    state.rip = inst_start + pos;

    uint64_t a = readOp(state, mem, rm);
    uint64_t b = state.regs[reg_field];
    uint64_t res = a & b;
    updateFlagsLogical(state.flags, res, default_op_size);
    return ExecResult::Continue;
  }

  // TEST al, imm8: A8
  if (opcode == 0xA8) {
    if (pos >= 15) return ExecResult::Unsupported;
    uint8_t imm8 = buf[pos++];
    state.rip = inst_start + pos;
    uint64_t res = (state.regs[RAX] & 0xFF) & imm8;
    updateFlagsLogical(state.flags, res, 1);
    return ExecResult::Continue;
  }

  // TEST rax, imm32: A9
  if (opcode == 0xA9) {
    if (pos + 4 > 15) return ExecResult::Unsupported;
    uint32_t imm32;
    std::memcpy(&imm32, &buf[pos], 4);
    pos += 4;
    state.rip = inst_start + pos;
    uint64_t ext = rex_w ? static_cast<uint64_t>(static_cast<int64_t>(
                               static_cast<int32_t>(imm32)))
                         : static_cast<uint64_t>(imm32);
    uint64_t res = state.regs[RAX] & ext;
    updateFlagsLogical(state.flags, res, default_op_size);
    return ExecResult::Continue;
  }

  // MOV r/m, reg (89) / MOV reg, r/m (8B)
  if (opcode == 0x89 || opcode == 0x8B) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    state.rip = inst_start + pos;

    Operand reg_op;
    reg_op.kind = Operand::REG;
    reg_op.reg = reg_field;
    reg_op.size = default_op_size;

    if (opcode == 0x89) {
      // MOV r/m, reg
      uint64_t val = readOp(state, mem, reg_op);
      writeOp(state, rm, val);
    } else {
      // MOV reg, r/m
      uint64_t val = readOp(state, mem, rm);
      writeOp(state, reg_op, val);
    }
    return ExecResult::Continue;
  }

  // MOV r/m8, reg8 (88) / MOV reg8, r/m8 (8A)
  if (opcode == 0x88 || opcode == 0x8A) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex, 1,
                             rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    state.rip = inst_start + pos;

    Operand reg_op;
    reg_op.kind = Operand::REG;
    reg_op.reg = reg_field;
    reg_op.size = 1;

    if (opcode == 0x88) {
      uint64_t val = readOp(state, mem, reg_op);
      writeOp(state, rm, val);
    } else {
      uint64_t val = readOp(state, mem, rm);
      writeOp(state, reg_op, val);
    }
    return ExecResult::Continue;
  }

  // LEA reg, [mem]: 8D
  if (opcode == 0x8D) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    state.rip = inst_start + pos;

    // For RIP-relative, the RIP value is the address of the NEXT instruction.
    if (rm.rip_relative) {
      rm.disp += static_cast<int64_t>(state.rip);
      rm.rip_relative = false;
    }

    uint64_t ea = computeEA(state, rm);
    if (default_op_size == 4)
      state.regs[reg_field] = ea & 0xFFFFFFFF;
    else
      state.regs[reg_field] = ea;
    return ExecResult::Continue;
  }

  // Group 1: ALU r/m, imm32/imm8 — opcodes 81, 83
  if (opcode == 0x81 || opcode == 0x83) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;

    int64_t imm;
    if (opcode == 0x83) {
      if (pos >= 15) return ExecResult::Unsupported;
      imm = static_cast<int8_t>(buf[pos++]);
    } else {
      if (pos + 4 > 15) return ExecResult::Unsupported;
      int32_t imm32;
      std::memcpy(&imm32, &buf[pos], 4);
      pos += 4;
      imm = imm32;
    }
    state.rip = inst_start + pos;

    uint64_t a = readOp(state, mem, rm);
    uint64_t b = static_cast<uint64_t>(imm);
    uint64_t res;

    switch (reg_field & 7) {
      case 0:  // ADD
        res = a + b;
        updateFlagsArith(state.flags, a, b, res, rm.size, false);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 1:  // OR
        res = a | b;
        updateFlagsLogical(state.flags, res, rm.size);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 2:  // ADC
        res = a + b + (state.flags.CF ? 1 : 0);
        updateFlagsArith(state.flags, a,
                         b + (state.flags.CF ? 1 : 0), res, rm.size, false);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 3:  // SBB
        res = a - b - (state.flags.CF ? 1 : 0);
        updateFlagsArith(state.flags, a,
                         b + (state.flags.CF ? 1 : 0), res, rm.size, true);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 4:  // AND
        res = a & b;
        updateFlagsLogical(state.flags, res, rm.size);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 5:  // SUB
        res = a - b;
        updateFlagsArith(state.flags, a, b, res, rm.size, true);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 6:  // XOR
        res = a ^ b;
        updateFlagsLogical(state.flags, res, rm.size);
        writeOp(state, rm, maskToSize(res, rm.size));
        break;
      case 7:  // CMP
        res = a - b;
        updateFlagsArith(state.flags, a, b, res, rm.size, true);
        break;
      default:
        return ExecResult::Unsupported;
    }
    return ExecResult::Continue;
  }

  // Group 1: ALU r/m8, imm8 — opcode 80
  if (opcode == 0x80) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex, 1,
                             rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;

    if (pos >= 15) return ExecResult::Unsupported;
    uint8_t imm8 = buf[pos++];
    state.rip = inst_start + pos;

    uint64_t a = readOp(state, mem, rm);
    uint64_t b = imm8;
    uint64_t res;

    switch (reg_field & 7) {
      case 0: res = a + b; updateFlagsArith(state.flags, a, b, res, 1, false);
        writeOp(state, rm, res & 0xFF); break;
      case 1: res = a | b; updateFlagsLogical(state.flags, res, 1);
        writeOp(state, rm, res & 0xFF); break;
      case 2: res = a + b + (state.flags.CF ? 1 : 0);
        updateFlagsArith(state.flags, a, b + (state.flags.CF ? 1 : 0), res, 1, false);
        writeOp(state, rm, res & 0xFF); break;
      case 3: res = a - b - (state.flags.CF ? 1 : 0);
        updateFlagsArith(state.flags, a, b + (state.flags.CF ? 1 : 0), res, 1, true);
        writeOp(state, rm, res & 0xFF); break;
      case 4: res = a & b; updateFlagsLogical(state.flags, res, 1);
        writeOp(state, rm, res & 0xFF); break;
      case 5: res = a - b; updateFlagsArith(state.flags, a, b, res, 1, true);
        writeOp(state, rm, res & 0xFF); break;
      case 6: res = a ^ b; updateFlagsLogical(state.flags, res, 1);
        writeOp(state, rm, res & 0xFF); break;
      case 7: res = a - b; updateFlagsArith(state.flags, a, b, res, 1, true);
        break;
      default: return ExecResult::Unsupported;
    }
    return ExecResult::Continue;
  }

  // MOV r/m, imm32: C7 /0
  if (opcode == 0xC7) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    if ((reg_field & 7) != 0)
      return ExecResult::Unsupported;

    if (pos + 4 > 15) return ExecResult::Unsupported;
    int32_t imm32;
    std::memcpy(&imm32, &buf[pos], 4);
    pos += 4;
    state.rip = inst_start + pos;

    uint64_t val = rex_w ? static_cast<uint64_t>(
                               static_cast<int64_t>(imm32))
                         : static_cast<uint64_t>(
                               static_cast<uint32_t>(imm32));
    writeOp(state, rm, val);
    return ExecResult::Continue;
  }

  // MOV r/m8, imm8: C6 /0
  if (opcode == 0xC6) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex, 1,
                             rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    if ((reg_field & 7) != 0)
      return ExecResult::Unsupported;
    if (pos >= 15) return ExecResult::Unsupported;
    uint8_t imm8 = buf[pos++];
    state.rip = inst_start + pos;
    writeOp(state, rm, imm8);
    return ExecResult::Continue;
  }

  // IMUL reg, r/m, imm32: 69
  if (opcode == 0x69) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    if (pos + 4 > 15) return ExecResult::Unsupported;
    int32_t imm32;
    std::memcpy(&imm32, &buf[pos], 4);
    pos += 4;
    state.rip = inst_start + pos;

    int64_t a = signExtend(readOp(state, mem, rm), rm.size);
    int64_t b = static_cast<int64_t>(imm32);
    uint64_t res = static_cast<uint64_t>(a * b);
    if (default_op_size == 4) res &= 0xFFFFFFFF;
    state.regs[reg_field] = res;
    return ExecResult::Continue;
  }

  // IMUL reg, r/m, imm8: 6B
  if (opcode == 0x6B) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    if (pos >= 15) return ExecResult::Unsupported;
    int8_t imm8 = static_cast<int8_t>(buf[pos++]);
    state.rip = inst_start + pos;

    int64_t a = signExtend(readOp(state, mem, rm), rm.size);
    int64_t b = static_cast<int64_t>(imm8);
    uint64_t res = static_cast<uint64_t>(a * b);
    if (default_op_size == 4) res &= 0xFFFFFFFF;
    state.regs[reg_field] = res;
    return ExecResult::Continue;
  }

  // Group 3: TEST/NOT/NEG/MUL/IMUL/DIV — F7 (32/64-bit), F6 (8-bit)
  if (opcode == 0xF7 || opcode == 0xF6) {
    unsigned op_sz = (opcode == 0xF6) ? 1 : default_op_size;
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             op_sz, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;

    switch (reg_field & 7) {
      case 0: {  // TEST r/m, imm
        unsigned imm_size = (opcode == 0xF6) ? 1 : 4;
        if (pos + imm_size > 15) return ExecResult::Unsupported;
        uint64_t imm = 0;
        std::memcpy(&imm, &buf[pos], imm_size);
        pos += imm_size;
        state.rip = inst_start + pos;
        if (rex_w && opcode == 0xF7) {
          imm = static_cast<uint64_t>(
              static_cast<int64_t>(static_cast<int32_t>(imm)));
        }
        uint64_t a = readOp(state, mem, rm);
        uint64_t res = a & imm;
        updateFlagsLogical(state.flags, res, op_sz);
        return ExecResult::Continue;
      }
      case 2: {  // NOT r/m
        state.rip = inst_start + pos;
        uint64_t val = readOp(state, mem, rm);
        writeOp(state, rm, maskToSize(~val, op_sz));
        return ExecResult::Continue;
      }
      case 3: {  // NEG r/m
        state.rip = inst_start + pos;
        uint64_t val = readOp(state, mem, rm);
        uint64_t res = maskToSize(-val, op_sz);
        updateFlagsArith(state.flags, 0, val, res, op_sz, true);
        writeOp(state, rm, res);
        return ExecResult::Continue;
      }
      default:
        state.rip = inst_start + pos;
        return ExecResult::Unsupported;
    }
  }

  // Group 2: SHL/SHR/SAR — D1 (by 1), D3 (by CL), C1 (by imm8)
  if (opcode == 0xD1 || opcode == 0xD3 || opcode == 0xC1) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             default_op_size, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;

    uint8_t count;
    if (opcode == 0xD1) {
      count = 1;
    } else if (opcode == 0xD3) {
      count = static_cast<uint8_t>(state.regs[RCX] & 0x3F);
    } else {  // C1
      if (pos >= 15) return ExecResult::Unsupported;
      count = buf[pos++] & 0x3F;
    }
    state.rip = inst_start + pos;

    uint64_t val = readOp(state, mem, rm);
    uint64_t res;

    switch (reg_field & 7) {
      case 4:  // SHL
        res = val << count;
        break;
      case 5:  // SHR
        res = maskToSize(val, rm.size) >> count;
        break;
      case 7:  // SAR
        res = static_cast<uint64_t>(
            signExtend(val, rm.size) >> count);
        break;
      default:
        return ExecResult::Unsupported;
    }
    writeOp(state, rm, maskToSize(res, rm.size));
    if (count > 0) {
      updateFlagsLogical(state.flags, res, rm.size);
      // CF = last bit shifted out (approximate).
      if ((reg_field & 7) == 5 || (reg_field & 7) == 7)
        state.flags.CF =
            (maskToSize(val, rm.size) >> (count - 1)) & 1;
      else
        state.flags.CF =
            (val >> (rm.size * 8 - count)) & 1;
    }
    return ExecResult::Continue;
  }

  // Group 2 for 8-bit: D0 (by 1), D2 (by CL), C0 (by imm8)
  if (opcode == 0xD0 || opcode == 0xD2 || opcode == 0xC0) {
    uint8_t reg_field;
    Operand rm;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex, 1,
                             rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;

    uint8_t count;
    if (opcode == 0xD0) count = 1;
    else if (opcode == 0xD2) count = static_cast<uint8_t>(state.regs[RCX] & 0x3F);
    else { if (pos >= 15) return ExecResult::Unsupported; count = buf[pos++] & 0x3F; }
    state.rip = inst_start + pos;

    uint64_t val = readOp(state, mem, rm) & 0xFF;
    uint64_t res;
    switch (reg_field & 7) {
      case 4: res = (val << count) & 0xFF; break;
      case 5: res = val >> count; break;
      case 7: res = static_cast<uint64_t>(static_cast<int8_t>(val) >> count) & 0xFF; break;
      default: return ExecResult::Unsupported;
    }
    writeOp(state, rm, res);
    if (count > 0) updateFlagsLogical(state.flags, res, 1);
    return ExecResult::Continue;
  }

  // JMP r/m64: FF /4
  // CALL r/m64: FF /2
  if (opcode == 0xFF || opcode == 0xFE) {
    // Peek at modrm to figure out the reg field first.
    if (pos >= 15) return ExecResult::Unsupported;
    uint8_t modrm_byte = buf[pos];
    uint8_t reg_peek = (modrm_byte >> 3) & 7;

    uint8_t reg_field;
    Operand rm;
    // For FF: INC/DEC (/0,/1) use default_op_size, JMP/CALL (/2,/4) use 8.
    // For FE: always byte.
    unsigned op_sz;
    if (opcode == 0xFE)
      op_sz = 1;
    else if (reg_peek == 2 || reg_peek == 4)
      op_sz = 8;  // CALL/JMP always 64-bit in long mode
    else
      op_sz = default_op_size;
    unsigned n = decodeModRM(&buf[pos], 15 - pos, has_rex, rex,
                             op_sz, rm, reg_field);
    if (n == 0) return ExecResult::Unsupported;
    pos += n;
    state.rip = inst_start + pos;

    if ((reg_field & 7) == 0) {
      // INC r/m
      uint64_t val = readOp(state, mem, rm);
      uint64_t res = val + 1;
      // INC doesn't affect CF, but updates OF/SF/ZF/AF/PF.
      bool old_cf = state.flags.CF;
      updateFlagsArith(state.flags, val, 1, res, rm.size, false);
      state.flags.CF = old_cf;
      writeOp(state, rm, maskToSize(res, rm.size));
      return ExecResult::Continue;
    }

    if ((reg_field & 7) == 1) {
      // DEC r/m
      uint64_t val = readOp(state, mem, rm);
      uint64_t res = val - 1;
      bool old_cf = state.flags.CF;
      updateFlagsArith(state.flags, val, 1, res, rm.size, true);
      state.flags.CF = old_cf;
      writeOp(state, rm, maskToSize(res, rm.size));
      return ExecResult::Continue;
    }

    if (opcode == 0xFF && (reg_field & 7) == 4) {
      // JMP r/m64
      uint64_t target = readOp(state, mem, rm);
      state.rip = target;
      if (rm.kind == Operand::REG)
        return ExecResult::IndirectJump;
      return ExecResult::Jump;
    }

    if (opcode == 0xFF && (reg_field & 7) == 2) {
      // CALL r/m64
      uint64_t ret_addr = inst_start + pos;
      uint64_t target = readOp(state, mem, rm);
      state.regs[RSP] -= 8;
      writeMem(state, state.regs[RSP], ret_addr, 8);
      state.rip = target;
      return ExecResult::Call;
    }

    return ExecResult::Unsupported;
  }

  // XCHG reg, rax: 90+rd (but 90 is NOP, handled above)
  // We shouldn't hit this for the VM handlers normally.

  // CDQ/CQO: 99
  if (opcode == 0x99) {
    state.rip = inst_start + pos;
    if (rex_w) {
      // CQO: sign-extend RAX into RDX:RAX
      state.regs[RDX] = (static_cast<int64_t>(state.regs[RAX]) < 0)
                             ? UINT64_MAX : 0;
    } else {
      // CDQ: sign-extend EAX into EDX:EAX
      state.regs[RDX] = (static_cast<int32_t>(state.regs[RAX]) < 0)
                             ? 0xFFFFFFFF : 0;
    }
    return ExecResult::Continue;
  }

  return ExecResult::Unsupported;
}

}  // anonymous namespace

// ============================================================================
// VMHandlerChainSolver Implementation
// ============================================================================

VMHandlerChainSolver::VMHandlerChainSolver(const BinaryMemoryMap &mem,
                                           uint64_t image_base,
                                           uint64_t vmenter_va,
                                           uint64_t vmexit_va)
    : mem_(mem),
      image_base_(image_base),
      vmenter_va_(vmenter_va),
      vmexit_va_(vmexit_va) {
  (void)image_base_;  // May be used for validation in future.
}

std::optional<uint64_t>
VMHandlerChainSolver::computeDelta(uint64_t subfunc_va,
                                   uint64_t return_addr) {
  // Pattern:
  //   push rax; push rbx;
  //   mov rax, <imm64>;
  //   mov rbx, [rsp+10h];    — gets the return address
  //   lea rbx, [rbx+rax];    — delta = return_addr + const
  //   mov [rsp+X], rbx;      — store result
  //   pop rbx; pop rax; ret

  // Just extract the imm64 from the mov rax instruction.
  // The sub-function starts: push rax (0x50), push rbx (0x53),
  // then REX.W mov rax, imm64 (48 B8 <8 bytes>).
  uint8_t buf[16];
  if (!mem_.read(subfunc_va, buf, 16))
    return std::nullopt;

  // Skip push rax (0x50) + push rbx (0x53) = 2 bytes.
  unsigned off = 0;
  if (buf[off] == 0x50) off++;
  if (off < 16 && buf[off] == 0x53) off++;

  // Pattern A: 48 B8 <imm64>  — REX.W MOV RAX, imm64
  if (off + 10 <= 16 && buf[off] == 0x48 && buf[off + 1] == 0xB8) {
    uint64_t imm64;
    std::memcpy(&imm64, &buf[off + 2], 8);
    return (return_addr + imm64) & UINT64_MAX;
  }

  // Pattern B: 48 C7 C0 <imm32>  — REX.W MOV RAX, sign-extended imm32
  if (off + 7 <= 16 && buf[off] == 0x48 && buf[off + 1] == 0xC7 &&
      buf[off + 2] == 0xC0) {
    int32_t imm32;
    std::memcpy(&imm32, &buf[off + 3], 4);
    uint64_t imm64 = static_cast<uint64_t>(static_cast<int64_t>(imm32));
    return (return_addr + imm64) & UINT64_MAX;
  }

  return std::nullopt;
}

VMHandlerChainSolver::WrapperInfo
VMHandlerChainSolver::parseEntryWrapper(uint64_t wrapper_va) {
  WrapperInfo info;

  // Read enough bytes for the wrapper (typically < 80 bytes).
  uint8_t buf[128];
  if (!mem_.read(wrapper_va, buf, sizeof(buf)))
    return info;

  unsigned pos = 0;

  // 1) lea rsp, [rsp - N]: 48 8D A4 24 <disp32>
  //    or: 48 8D 64 24 <disp8>
  if (pos + 8 <= sizeof(buf) &&
      buf[pos] == 0x48 && buf[pos + 1] == 0x8D &&
      buf[pos + 2] == 0xA4 && buf[pos + 3] == 0x24) {
    pos += 8;  // 48 8D A4 24 + 4-byte disp
  } else if (pos + 5 <= sizeof(buf) &&
             buf[pos] == 0x48 && buf[pos + 1] == 0x8D &&
             buf[pos + 2] == 0x64 && buf[pos + 3] == 0x24) {
    pos += 5;  // 48 8D 64 24 + 1-byte disp
  } else {
    // Try without LEA (some wrappers may use SUB RSP).
    // sub rsp, imm32: 48 81 EC <imm32>
    if (pos + 7 <= sizeof(buf) &&
        buf[pos] == 0x48 && buf[pos + 1] == 0x81 && buf[pos + 2] == 0xEC) {
      pos += 7;
    }
  }

  // 2) call <vmentry>: E8 <rel32>
  if (pos + 5 > sizeof(buf) || buf[pos] != 0xE8)
    return info;

  int32_t call_rel;
  std::memcpy(&call_rel, &buf[pos + 1], 4);
  uint64_t call_addr = wrapper_va + pos;
  uint64_t call_target = call_addr + 5 + static_cast<int64_t>(call_rel);
  pos += 5;

  // Verify it calls vmentry (or a vmentry variant).
  // For now, accept any call target in the vmentry vicinity.
  // A vmentry variant has a sub-function call inside it that computes delta.

  // Find the sub-function call inside vmentry.
  // vmentry pattern: saves registers, then calls a sub-function.
  // The sub-function call is typically at vmentry + 0x90.
  uint8_t vmentry_buf[256];
  if (!mem_.read(call_target, vmentry_buf, sizeof(vmentry_buf)))
    return info;

  // Scan for the CALL inside vmentry (E8 xx xx xx xx).
  uint64_t subfunc_va = 0;
  uint64_t subfunc_ret = 0;
  for (unsigned i = 0; i + 5 <= sizeof(vmentry_buf); ++i) {
    if (vmentry_buf[i] == 0xE8) {
      int32_t rel;
      std::memcpy(&rel, &vmentry_buf[i + 1], 4);
      uint64_t target = call_target + i + 5 + static_cast<int64_t>(rel);
      // The sub-function should be nearby.
      if (target > call_target && target < call_target + 0x1000) {
        subfunc_va = target;
        subfunc_ret = call_target + i + 5;
        break;
      }
    }
  }

  if (subfunc_va == 0)
    return info;

  auto delta = computeDelta(subfunc_va, subfunc_ret);
  if (!delta)
    return info;

  info.delta = *delta;

  // 3) After the call, find: jmp <somewhere> → handler preamble.
  // The preamble contains: mov rax, <hash>; mov [r12+0x190], rax;
  // mov eax, <rva>; add rax, [r12+0xE0]; jmp rax

  // Follow jumps from pos to find the preamble.
  // Use the emulator to execute the wrapper from the current position.
  EmuState state;
  state.regs[RSP] = EmuState::kStackBase + EmuState::kStackSize - 0x2000;
  state.regs[R12] = EmuState::kStackBase + 0x200;  // vmcontext base

  // Pre-fill vmcontext with sentinel.
  for (unsigned off = 0; off < 0x200; off += 8) {
    writeMem(state, state.regs[R12] + off, kSentinel, 8);
  }

  // Store the computed delta at [r12+0xE0].
  writeMem(state, state.regs[R12] + 0xE0, info.delta, 8);

  // Set rip to the instruction after the vmentry call in the wrapper.
  // But we need to emulate from the wrapper's post-call code, which
  // includes the jmp to scattered preamble code.
  state.rip = wrapper_va + pos;

  // Emulate until we hit an indirect jump (the dispatch to first handler).
  for (unsigned step = 0; step < 200; ++step) {
    ExecResult res = stepInstruction(state, mem_);

    if (res == ExecResult::IndirectJump) {
      // state.rip is the dispatch target.
      info.first_handler_va = state.rip;

      // Read the hash from [r12+0x190].
      info.initial_hash =
          readMem(state, mem_, state.regs[R12] + 0x190, 8);

      info.valid = true;
      return info;
    }

    if (res == ExecResult::Unsupported || res == ExecResult::Ret)
      return info;

    // For calls within the preamble (shouldn't happen but be safe),
    // skip them.
    if (res == ExecResult::Call) {
      // If it's calling vmentry again, something is wrong.
      return info;
    }
  }

  return info;
}

std::vector<VMHandlerChainSolver::ChainEntry>
VMHandlerChainSolver::solveFromWrapper(uint64_t wrapper_va) {
  auto info = parseEntryWrapper(wrapper_va);
  if (!info.valid) {
    llvm::errs() << "VMHandlerChainSolver: failed to parse wrapper at "
                 << llvm::utohexstr(wrapper_va) << "\n";
    return {};
  }

  llvm::errs() << "VMHandlerChainSolver: wrapper at "
               << llvm::utohexstr(wrapper_va)
               << " → delta=" << llvm::utohexstr(info.delta)
               << " hash=" << llvm::utohexstr(info.initial_hash)
               << " first=" << llvm::utohexstr(info.first_handler_va)
               << "\n";

  last_delta_ = info.delta;

  auto results = solveFromHandler(info.first_handler_va, info.delta,
                                  info.initial_hash);

  // Prepend a chain entry for the wrapper → first handler mapping.
  // This lets VMDispatchResolutionPass resolve the wrapper's dispatch.
  ChainEntry wrapper_entry;
  wrapper_entry.handler_va = wrapper_va;
  wrapper_entry.successors.push_back(info.first_handler_va);
  results.insert(results.begin(), wrapper_entry);

  // Add wrapper to discovered handlers.
  if (discovered_set_.insert(wrapper_va).second)
    discovered_handlers_.push_back(wrapper_va);

  last_chain_results_ = results;
  return results;
}

std::vector<VMHandlerChainSolver::ChainEntry>
VMHandlerChainSolver::solveFromHandler(uint64_t handler_va,
                                       uint64_t delta,
                                       uint64_t initial_hash) {
  std::vector<ChainEntry> results;

  struct WorkItem {
    uint64_t handler_va;
    uint64_t hash;  // Hash accumulator state entering this handler.
  };

  std::deque<WorkItem> queue;
  // Track (handler_va, hash) pairs — the same handler visited with a
  // different hash processes different VM bytecode and dispatches to a
  // different successor.  Keying only on handler_va would prematurely
  // terminate chains that revisit the same handler (common in EAC's
  // dispatcher-style handlers that route multiple VM opcodes).
  llvm::DenseSet<std::pair<uint64_t, uint64_t>> visited;

  queue.push_back({handler_va, initial_hash});

  while (!queue.empty() && results.size() < max_handlers_) {
    auto item = queue.front();
    queue.pop_front();

    auto key = std::make_pair(item.handler_va, item.hash);
    if (visited.count(key))
      continue;
    visited.insert(key);

    // Record this handler.
    if (discovered_set_.insert(item.handler_va).second)
      discovered_handlers_.push_back(item.handler_va);

    ChainEntry entry;
    entry.handler_va = item.handler_va;

    // Set up emulator state.
    EmuState state;
    state.stack_mem.fill(0);
    state.regs[RSP] = EmuState::kStackBase + EmuState::kStackSize - 0x2000;
    state.regs[R12] = EmuState::kStackBase + 0x200;
    state.rip = item.handler_va;

    // Fill vmcontext with sentinel for register slots.
    for (unsigned off = 0; off < 0x200; off += 8)
      writeMem(state, state.regs[R12] + off, kSentinel, 8);

    // Set known vmcontext slots.
    writeMem(state, state.regs[R12] + 0xE0, delta, 8);
    writeMem(state, state.regs[R12] + 0x190, item.hash, 8);

    // Emulate the handler.
    bool dispatched = false;
    for (unsigned step = 0; step < max_steps_per_handler_; ++step) {
      ExecResult res = stepInstruction(state, mem_);

      if (res == ExecResult::Unsupported) {
        llvm::errs() << "VMHandlerChainSolver: unsupported instruction at "
                     << llvm::utohexstr(state.rip) << " in handler "
                     << llvm::utohexstr(item.handler_va)
                     << " (step " << step << ")\n";
        entry.is_error = true;
        dispatched = true;
        break;
      }

      if (res == ExecResult::IndirectJump) {
        uint64_t target = state.rip;

        // If we already passed through vmexit and are in the trampoline
        // code, an indirect jump means we've gone through the preamble
        // and are dispatching to the first handler of the NEXT chain.
        if (entry.is_vmexit && target >= handler_seg_start_ &&
            target < handler_seg_end_) {
          // Read the new hash from vmcontext (set by the preamble).
          uint64_t new_hash =
              readMem(state, mem_, state.regs[R12] + 0x190, 8);

          // If this (target, hash) pair is already visited, the chain
          // has genuinely cycled — same handler with same VM state.
          if (visited.count({target, new_hash})) {
            llvm::errs()
                << "VMHandlerChainSolver: vmexit continuation → "
                << "0x" << llvm::utohexstr(target)
                << " (already visited, treating as terminal vmexit)\n";
            dispatched = true;
            break;
          }

          llvm::errs() << "VMHandlerChainSolver: vmexit continuation → "
                       << "next chain at 0x" << llvm::utohexstr(target)
                       << " hash=" << llvm::utohexstr(new_hash) << "\n";

          entry.successors.push_back(target);
          queue.push_back({target, new_hash});
          dispatched = true;
          break;
        }

        // Check if this is a VM exit.
        if (target == vmexit_va_) {
          entry.is_vmexit = true;
          dispatched = true;
          break;
        }

        // Check if target is a vmentry (re-virtualized call).
        if (target == vmenter_va_) {
          // For now, mark as vmexit (can't follow nested VM).
          entry.is_vmexit = true;
          dispatched = true;
          break;
        }

        // Check if target is in the handler segment.
        if (target >= handler_seg_start_ && target < handler_seg_end_) {
          // EAC dispatch: handlers store the actual next handler VA at
          // [r12+0x198] and jump to a dispatch trampoline.  The trampoline
          // copies vmcontext and then `jmp [rsp+0x198]`.  Check if the
          // handler wrote a valid target at [r12+0x198].
          uint64_t stored_target =
              readMem(state, mem_, state.regs[R12] + 0x198, 8);

          if (stored_target != kSentinel && stored_target != 0 &&
              stored_target >= handler_seg_start_ &&
              stored_target < handler_seg_end_ &&
              stored_target != target) {
            // The handler dispatches through a trampoline. The actual next
            // handler is in [r12+0x198]. Read the updated hash from
            // [r12+0x190].
            uint64_t new_hash =
                readMem(state, mem_, state.regs[R12] + 0x190, 8);

            entry.successors.push_back(stored_target);
            queue.push_back({stored_target, new_hash});
            dispatched = true;
            break;
          }

          // No stored target — treat the jump target itself as the
          // successor (simple dispatch pattern or trampoline IS handler).
          uint64_t new_hash =
              readMem(state, mem_, state.regs[R12] + 0x190, 8);

          entry.successors.push_back(target);
          queue.push_back({target, new_hash});
          dispatched = true;
          break;
        }

        // Unknown target — might be a call to native code.
        llvm::errs() << "VMHandlerChainSolver: unknown indirect target "
                     << llvm::utohexstr(target) << " from handler "
                     << llvm::utohexstr(item.handler_va) << "\n";
        entry.is_error = true;
        dispatched = true;
        break;
      }

      if (res == ExecResult::Call) {
        uint64_t target = state.rip;

        if (target == vmexit_va_) {
          // Skip the vmexit call — pop return address and continue.
          // This lets us follow through the vmexit trampoline to find
          // the next chain's preamble after re-entry.
          uint64_t ret_addr = readMem(state, mem_, state.regs[RSP], 8);
          state.regs[RSP] += 8;
          state.rip = ret_addr;
          entry.is_vmexit = true;  // Mark that we passed through vmexit.
          continue;
        }

        if (target == vmenter_va_) {
          // Skip the vmentry call — pop return address and continue.
          // After this, the trampoline will jmp to the next preamble.
          uint64_t ret_addr = readMem(state, mem_, state.regs[RSP], 8);
          state.regs[RSP] += 8;
          state.rip = ret_addr;

          if (entry.is_vmexit) {
            // Re-entering VM after native call — vmctx still at old R12.
            // Don't relocate R12.  Reset is_vmexit since we're back in VM.
            entry.is_vmexit = false;
          } else {
            // Fresh VM entry (continuation chain).  Relocate R12 to new
            // vmctx on the stack.
            state.regs[R12] = state.regs[RSP];
            writeMem(state, state.regs[R12] + 0xE0, delta, 8);
          }
          continue;
        }

        // If we've already passed through vmexit and encounter a CALL
        // to unknown code (like `call [rsp+8]` for the native function),
        // skip it — we can't emulate arbitrary native code.
        if (entry.is_vmexit) {
          uint64_t ret_addr = readMem(state, mem_, state.regs[RSP], 8);
          state.regs[RSP] += 8;
          state.rip = ret_addr;
          continue;
        }

        // For other calls (e.g., to sub-functions within the handler),
        // continue emulating into the callee. The return address was
        // already pushed by stepInstruction.
        continue;
      }

      if (res == ExecResult::Ret) {
        // If we return and the return address is in the handler segment,
        // it might be a trampoline. Otherwise, it's unusual.
        uint64_t ret_target = state.rip;
        if (ret_target >= handler_seg_start_ &&
            ret_target < handler_seg_end_) {
          // This is a vmexit-style return to another handler.
          uint64_t new_hash =
              readMem(state, mem_, state.regs[R12] + 0x190, 8);

          // Cycle check: if this (target, hash) pair is already visited,
          // the chain has genuinely cycled.
          if (visited.count({ret_target, new_hash})) {
            llvm::errs()
                << "VMHandlerChainSolver: ret to 0x"
                << llvm::utohexstr(ret_target)
                << " (already visited, treating as terminal)\n";
            dispatched = true;
            break;
          }
          entry.successors.push_back(ret_target);
          queue.push_back({ret_target, new_hash});
          dispatched = true;
          break;
        }

        // Check if we're returning to vmexit.
        if (ret_target == vmexit_va_) {
          entry.is_vmexit = true;
          dispatched = true;
          break;
        }

        // Unknown return target.
        llvm::errs() << "VMHandlerChainSolver: handler "
                     << llvm::utohexstr(item.handler_va)
                     << " returned to "
                     << llvm::utohexstr(ret_target) << "\n";
        entry.is_error = true;
        dispatched = true;
        break;
      }

      // Continue, Jump: normal flow.
    }

    if (!dispatched) {
      llvm::errs() << "VMHandlerChainSolver: handler "
                   << llvm::utohexstr(item.handler_va)
                   << " exceeded step limit\n";
      entry.is_error = true;
    }

    results.push_back(std::move(entry));
  }

  // Sort discovered handlers.
  llvm::sort(discovered_handlers_);

  llvm::errs() << "VMHandlerChainSolver: solved " << results.size()
               << " handlers";
  unsigned exits = 0, errors = 0;
  for (auto &e : results) {
    if (e.is_vmexit) exits++;
    if (e.is_error) errors++;
  }
  if (exits > 0)
    llvm::errs() << ", " << exits << " exits";
  if (errors > 0)
    llvm::errs() << ", " << errors << " errors";
  llvm::errs() << "\n";

  // Print chain details.
  for (unsigned i = 0; i < results.size(); ++i) {
    auto &e = results[i];
    llvm::errs() << "  [" << i << "] handler 0x" << llvm::utohexstr(e.handler_va);
    if (e.is_vmexit)
      llvm::errs() << " → vmexit";
    else if (e.is_error)
      llvm::errs() << " → ERROR";
    else {
      llvm::errs() << " → ";
      for (unsigned j = 0; j < e.successors.size(); ++j) {
        if (j > 0) llvm::errs() << ", ";
        llvm::errs() << "0x" << llvm::utohexstr(e.successors[j]);
      }
    }
    llvm::errs() << "\n";
  }

  last_chain_results_ = results;
  return results;
}

}  // namespace omill

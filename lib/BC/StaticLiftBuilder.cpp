#include "omill/BC/StaticLiftBuilder.h"
#include "omill/BC/DecodeInstruction.h"

#include <algorithm>
#include <cctype>
#include <deque>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/LLVMContext.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Analysis/VMTraceMap.h"
#include "omill/BC/LiftTargetPolicy.h"
#include "omill/Support/JumpTableDiscovery.h"
#include "remill/Arch/Arch.h"
#include "remill/Arch/Instruction.h"
#include <windows.h>

namespace omill {
bool DecodeInstruction(const remill::Arch &arch, uint64_t pc,
                       const std::string &inst_bytes,
                       remill::Instruction &instruction) {
  const auto context = arch.CreateInitialContext();
  const bool decode_ok = arch.DecodeInstruction(pc, inst_bytes, instruction, context);

  // Remill can report decode success for an overlap/misaligned entry while
  // still leaving the instruction invalid or zero-sized. Those decodes are
  // not usable for lifting and must be treated as failures everywhere.
  return decode_ok && instruction.IsValid() && instruction.NumBytes() != 0;
}

bool DecodeInstruction(const remill::Arch &arch,
                       const BinaryMemoryMap &memory_map, uint64_t pc,
                       remill::Instruction &instruction) {
  const auto max_bytes = arch.MaxInstructionSize(arch.CreateInitialContext());

  std::string inst_bytes;
  inst_bytes.reserve(static_cast<size_t>(max_bytes));
  for (uint64_t i = 0; i < max_bytes; ++i) {
    uint8_t byte = 0;
    if (!memory_map.isExecutable(pc + i, 1) || !memory_map.read(pc + i, &byte, 1)) {
      break;
    }
    inst_bytes.push_back(static_cast<char>(byte));
  }
  if (inst_bytes.empty()) {
    return false;
  }

  return DecodeInstruction(arch, pc, inst_bytes, instruction);
}

DecodeInstructionStatus ProbeDecodeInstruction(TargetArch target_arch,
                                               const BinaryMemoryMap &memory_map,
                                               uint64_t pc) {
  DecodeInstructionStatus status;
  if (target_arch != TargetArch::kX86_64) {
    return status;
  }

  llvm::LLVMContext context;
  for (const char *arch_name : {"amd64_avx", "amd64"}) {
    auto arch = remill::Arch::Get(context, "windows", arch_name);
    if (!arch) {
      continue;
    }

    const auto max_bytes = arch->MaxInstructionSize(arch->CreateInitialContext());
    std::string inst_bytes;
    inst_bytes.reserve(static_cast<size_t>(max_bytes));
    for (uint64_t i = 0; i < max_bytes; ++i) {
      uint8_t byte = 0;
      if (!memory_map.isExecutable(pc + i, 1) || !memory_map.read(pc + i, &byte, 1)) {
        break;
      }
      inst_bytes.push_back(static_cast<char>(byte));
    }
    if (inst_bytes.empty()) {
      return status;
    }

    remill::Instruction instruction;
    __try {
      status.decoder_succeeded = arch->DecodeInstruction(
          pc, inst_bytes, instruction, arch->CreateInitialContext());
    } __except (EXCEPTION_EXECUTE_HANDLER) {
      continue;
    }

    status.usable = status.decoder_succeeded && instruction.IsValid() &&
                    instruction.NumBytes() != 0;
    if (status.decoder_succeeded || status.usable) {
      return status;
    }
  }

  return status;
}


namespace {

struct StackState {
  bool precise = true;
  int64_t rsp_offset = 0;
  bool rbp_known = false;
  int64_t rbp_offset = 0;
};

struct TransferInfo {
  int64_t stack_pointer_delta = 0;
  bool dynamic_stack_barrier = false;
  std::vector<LiftDbLocation> implicit_uses;
  std::vector<LiftDbLocation> implicit_defs;
  std::vector<LiftDbStackAccessRecord> stack_accesses;
};

using DecodedInstMap = std::map<uint64_t, remill::Instruction>;
using DefSet = std::set<uint64_t>;
using ReachingDefs = std::map<std::string, DefSet>;

template <typename T>
static void PushUnique(std::vector<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

static bool SameStackState(const StackState &lhs, const StackState &rhs) {
  return lhs.precise == rhs.precise && lhs.rsp_offset == rhs.rsp_offset &&
         lhs.rbp_known == rhs.rbp_known && lhs.rbp_offset == rhs.rbp_offset;
}

static std::string HexBytes(std::string_view bytes) {
  std::string out;
  out.reserve(bytes.size() * 2);
  for (auto byte : bytes) {
    const auto value = static_cast<uint8_t>(byte);
    out.push_back(llvm::hexdigit(value >> 4));
    out.push_back(llvm::hexdigit(value & 0x0f));
  }
  return out;
}

static std::string ToUpper(std::string text) {
  std::transform(text.begin(), text.end(), text.begin(),
                 [](unsigned char ch) { return static_cast<char>(std::toupper(ch)); });
  return text;
}

static std::string NormalizeRegName(llvm::StringRef name) {
  return ToUpper(name.str());
}

static bool IsRegisterName(llvm::StringRef lhs, llvm::StringRef rhs) {
  return lhs.equals_insensitive(rhs);
}

static bool IsRSP(llvm::StringRef name) {
  return IsRegisterName(name, "RSP") || IsRegisterName(name, "ESP") ||
         IsRegisterName(name, "SP");
}

static bool IsRBP(llvm::StringRef name) {
  return IsRegisterName(name, "RBP") || IsRegisterName(name, "EBP") ||
         IsRegisterName(name, "BP");
}

static bool IsRIP(llvm::StringRef name) {
  return IsRegisterName(name, "RIP") || IsRegisterName(name, "EIP");
}

static uint32_t BytesFromBits(uint64_t bits) {
  return bits ? static_cast<uint32_t>((bits + 7u) / 8u) : 0u;
}

static LiftDbLocation MakeRegisterLocation(llvm::StringRef reg_name,
                                           uint64_t size_bits) {
  LiftDbLocation location;
  location.kind = LiftDbLocationKind::kRegister;
  location.name = NormalizeRegName(reg_name);
  location.size_bits = static_cast<uint32_t>(size_bits);
  location.precise = true;
  return location;
}

static LiftDbLocation MakeFlagLocation(llvm::StringRef flag_name = "RFLAGS") {
  LiftDbLocation location;
  location.kind = LiftDbLocationKind::kFlag;
  location.name = NormalizeRegName(flag_name);
  location.size_bits = 64;
  location.precise = true;
  return location;
}

static LiftDbLocation MakeStackLocation(int64_t offset,
                                        llvm::StringRef base_register,
                                        uint64_t size_bits) {
  LiftDbLocation location;
  location.kind = LiftDbLocationKind::kStackCell;
  location.name = "STACK";
  location.base_register = NormalizeRegName(base_register);
  location.offset = offset;
  location.size_bits = static_cast<uint32_t>(size_bits);
  location.precise = true;
  return location;
}

static LiftDbLocation MakeMemoryLocation(uint64_t size_bits) {
  LiftDbLocation location;
  location.kind = LiftDbLocationKind::kMemory;
  location.name = "MEMORY";
  location.size_bits = static_cast<uint32_t>(size_bits);
  location.precise = false;
  return location;
}

static LiftDbLocation MakeRipRelativeLocation(int64_t offset,
                                              uint64_t size_bits) {
  LiftDbLocation location;
  location.kind = LiftDbLocationKind::kRipRelative;
  location.name = "RIPREL";
  location.base_register = "RIP";
  location.offset = offset;
  location.size_bits = static_cast<uint32_t>(size_bits);
  location.precise = true;
  return location;
}

static std::string LocationKey(const LiftDbLocation &location) {
  std::string key;
  key.reserve(96);
  key += std::to_string(static_cast<unsigned>(location.kind));
  key += "|";
  key += location.name;
  key += "|";
  key += location.base_register;
  key += "|";
  key += std::to_string(location.offset);
  key += "|";
  key += std::to_string(location.size_bits);
  key += "|";
  key += location.precise ? "1" : "0";
  return key;
}

static bool SameLocation(const LiftDbLocation &lhs, const LiftDbLocation &rhs) {
  return lhs.kind == rhs.kind && lhs.name == rhs.name &&
         lhs.base_register == rhs.base_register && lhs.offset == rhs.offset &&
         lhs.size_bits == rhs.size_bits && lhs.precise == rhs.precise;
}

static void AppendLocationUnique(std::vector<LiftDbLocation> &locations,
                                 const LiftDbLocation &location) {
  auto it = std::find_if(locations.begin(), locations.end(),
                         [&](const LiftDbLocation &existing) {
                           return SameLocation(existing, location);
                         });
  if (it == locations.end()) {
    locations.push_back(location);
  }
}

static bool ShouldTrackUseDef(const LiftDbLocation &location) {
  switch (location.kind) {
    case LiftDbLocationKind::kRegister:
    case LiftDbLocationKind::kFlag:
      return true;
    case LiftDbLocationKind::kStackCell:
      return location.precise;
    default:
      return false;
  }
}

static LiftDbCategory MapCategory(const remill::Instruction &instruction) {
  switch (instruction.category) {
    case remill::Instruction::kCategoryDirectJump:
      return LiftDbCategory::kDirectJump;
    case remill::Instruction::kCategoryIndirectJump:
    case remill::Instruction::kCategoryConditionalIndirectJump:
      return LiftDbCategory::kIndirectJump;
    case remill::Instruction::kCategoryConditionalBranch:
      return LiftDbCategory::kConditionalBranch;
    case remill::Instruction::kCategoryDirectFunctionCall:
    case remill::Instruction::kCategoryConditionalDirectFunctionCall:
      return LiftDbCategory::kDirectCall;
    case remill::Instruction::kCategoryIndirectFunctionCall:
    case remill::Instruction::kCategoryConditionalIndirectFunctionCall:
      return LiftDbCategory::kIndirectCall;
    case remill::Instruction::kCategoryFunctionReturn:
    case remill::Instruction::kCategoryConditionalFunctionReturn:
      return LiftDbCategory::kReturn;
    case remill::Instruction::kCategoryNormal:
    case remill::Instruction::kCategoryNoOp:
    default:
      return LiftDbCategory::kNormal;
  }
}

static std::string ExtractMnemonic(const remill::Instruction &instruction) {
  auto serialized = instruction.Serialize();
  llvm::StringRef text(serialized);
  text = text.trim();
  auto parts = text.split(' ');
  if (!parts.first.empty()) {
    return ToUpper(parts.first.str());
  }
  return ToUpper(instruction.function);
}


static std::optional<std::string> RegisterNameFromOperand(
    const remill::Operand &operand) {
  switch (operand.type) {
    case remill::Operand::kTypeRegister:
    case remill::Operand::kTypeRegisterExpression:
      if (!operand.reg.name.empty()) {
        return operand.reg.name;
      }
      break;
    case remill::Operand::kTypeShiftRegister:
      if (!operand.shift_reg.reg.name.empty()) {
        return operand.shift_reg.reg.name;
      }
      break;
    default:
      break;
  }
  return std::nullopt;
}

static const remill::Operand::Address *AddressFromOperand(
    const remill::Operand &operand) {
  switch (operand.type) {
    case remill::Operand::kTypeAddress:
    case remill::Operand::kTypeAddressExpression:
      return &operand.addr;
    default:
      return nullptr;
  }
}

static bool IsRegisterOperand(const remill::Operand &operand,
                              llvm::StringRef reg_name) {
  auto name = RegisterNameFromOperand(operand);
  return name && IsRegisterName(*name, reg_name);
}

static bool WritesRegister(const remill::Instruction &instruction,
                           llvm::StringRef reg_name) {
  for (const auto &operand : instruction.operands) {
    if (operand.action == remill::Operand::kActionWrite &&
        IsRegisterOperand(operand, reg_name)) {
      return true;
    }
  }
  return false;
}

static bool AddLocationToOperandAndInstruction(
    LiftDbOperandRecord &operand_record, LiftDbInstructionRecord &instruction,
    const LiftDbLocation &location, bool is_read) {
  if (is_read) {
    AppendLocationUnique(operand_record.reads, location);
    AppendLocationUnique(instruction.uses, location);
  } else {
    AppendLocationUnique(operand_record.writes, location);
    AppendLocationUnique(instruction.defs, location);
  }
  return true;
}

static bool TryMakeExactStackLocation(const remill::Operand::Address &address,
                                      const StackState &state,
                                      uint64_t size_bits,
                                      LiftDbLocation &location) {
  if (!state.precise || !address.index_reg.name.empty()) {
    return false;
  }

  if (!address.base_reg.name.empty() && IsRSP(address.base_reg.name)) {
    location = MakeStackLocation(state.rsp_offset + address.displacement,
                                 address.base_reg.name, size_bits);
    return true;
  }

  if (!address.base_reg.name.empty() && IsRBP(address.base_reg.name) &&
      state.rbp_known) {
    location = MakeStackLocation(state.rbp_offset + address.displacement,
                                 address.base_reg.name, size_bits);
    return true;
  }

  return false;
}

static void AddStackAccess(std::vector<LiftDbStackAccessRecord> &accesses,
                           LiftDbStackAccessKind kind, int64_t offset,
                           uint32_t size, bool exact,
                           llvm::StringRef location_name) {
  LiftDbStackAccessRecord record;
  record.kind = kind;
  record.offset = offset;
  record.size = size;
  record.exact = exact;
  record.location_name = location_name.str();
  accesses.push_back(std::move(record));
}

static std::optional<uint64_t> ImmediateValue(const remill::Operand &operand) {
  switch (operand.type) {
    case remill::Operand::kTypeImmediate:
    case remill::Operand::kTypeImmediateExpression:
      return operand.imm.val;
    default:
      return std::nullopt;
  }
}

static bool StartsWithMnemonic(llvm::StringRef mnemonic,
                               llvm::StringRef prefix) {
  return mnemonic.size() >= prefix.size() &&
         mnemonic.take_front(prefix.size()).equals_insensitive(prefix);
}

static bool ShouldUseFlags(llvm::StringRef mnemonic,
                           const remill::Instruction &instruction) {
  if (instruction.IsConditionalBranch()) {
    return true;
  }
  return StartsWithMnemonic(mnemonic, "CMOV") ||
         StartsWithMnemonic(mnemonic, "SET");
}

static bool ShouldDefFlags(llvm::StringRef mnemonic) {
  static constexpr const char *kFlagDefs[] = {
      "ADD",  "ADC", "SUB", "SBB", "CMP", "TEST", "AND", "OR",  "XOR",
      "SHL",  "SAL", "SHR", "SAR", "ROL", "ROR",  "NEG", "INC", "DEC"};
  for (auto prefix : kFlagDefs) {
    if (StartsWithMnemonic(mnemonic, prefix)) {
      return true;
    }
  }
  return false;
}

static bool ApplyStackTransfer(const remill::Instruction &instruction,
                               llvm::StringRef mnemonic, StackState &state,
                               TransferInfo *info) {
  auto add_implicit_use = [&](const LiftDbLocation &location) {
    if (info) {
      AppendLocationUnique(info->implicit_uses, location);
    }
  };
  auto add_implicit_def = [&](const LiftDbLocation &location) {
    if (info) {
      AppendLocationUnique(info->implicit_defs, location);
    }
  };
  auto add_stack_access = [&](LiftDbStackAccessKind kind, int64_t offset,
                              uint32_t size, bool exact,
                              llvm::StringRef location_name) {
    if (info) {
      AddStackAccess(info->stack_accesses, kind, offset, size, exact,
                     location_name);
    }
  };
  auto add_rsp_use_def = [&]() {
    add_implicit_use(MakeRegisterLocation("RSP", 64));
    add_implicit_def(MakeRegisterLocation("RSP", 64));
  };
  auto mark_barrier = [&]() {
    state.precise = false;
    state.rbp_known = false;
    if (info) {
      info->dynamic_stack_barrier = true;
      AddStackAccess(info->stack_accesses, LiftDbStackAccessKind::kBarrier,
                     state.rsp_offset, 0, false, "dynamic_stack_barrier");
    }
  };

  if (ShouldUseFlags(mnemonic, instruction)) {
    add_implicit_use(MakeFlagLocation());
  }
  if (ShouldDefFlags(mnemonic)) {
    add_implicit_def(MakeFlagLocation());
  }

  if (instruction.IsFunctionCall()) {
    add_rsp_use_def();
    if (state.precise) {
      add_stack_access(LiftDbStackAccessKind::kReturnAddress,
                       state.rsp_offset - 8, 8, true, "return_address");
    }
    if (info) {
      info->stack_pointer_delta = 0;
    }
    return true;
  }

  if (instruction.IsFunctionReturn()) {
    add_rsp_use_def();
    if (state.precise) {
      add_stack_access(LiftDbStackAccessKind::kReturnAddress, state.rsp_offset,
                       8, true, "return_address");
      state.rsp_offset += 8;
      if (info) {
        info->stack_pointer_delta = 8;
      }
    } else {
      mark_barrier();
    }
    return true;
  }

  if (StartsWithMnemonic(mnemonic, "PUSH")) {
    add_rsp_use_def();
    if (state.precise) {
      state.rsp_offset -= 8;
      add_stack_access(LiftDbStackAccessKind::kWrite, state.rsp_offset, 8,
                       true, "push");
      if (info) {
        info->stack_pointer_delta = -8;
      }
    } else {
      mark_barrier();
    }
    return true;
  }

  if (StartsWithMnemonic(mnemonic, "POP")) {
    add_rsp_use_def();
    if (state.precise) {
      add_stack_access(LiftDbStackAccessKind::kRead, state.rsp_offset, 8, true,
                       "pop");
      state.rsp_offset += 8;
      if (info) {
        info->stack_pointer_delta = 8;
      }
    } else {
      mark_barrier();
    }
    if (WritesRegister(instruction, "RBP")) {
      state.rbp_known = false;
    }
    return true;
  }

  if (StartsWithMnemonic(mnemonic, "LEAVE")) {
    add_implicit_use(MakeRegisterLocation("RBP", 64));
    add_rsp_use_def();
    if (!state.precise || !state.rbp_known) {
      mark_barrier();
      return true;
    }
    add_stack_access(LiftDbStackAccessKind::kRead, state.rbp_offset, 8, true,
                     "leave");
    if (info) {
      info->stack_pointer_delta = (state.rbp_offset + 8) - state.rsp_offset;
    }
    state.rsp_offset = state.rbp_offset + 8;
    state.rbp_known = false;
    return true;
  }

  if (instruction.operands.size() >= 2 &&
      instruction.operands[0].action == remill::Operand::kActionWrite &&
      IsRegisterOperand(instruction.operands[0], "RSP")) {
    if (StartsWithMnemonic(mnemonic, "ADD") ||
        StartsWithMnemonic(mnemonic, "SUB")) {
      auto imm = ImmediateValue(instruction.operands[1]);
      if (imm && state.precise) {
        const auto signed_imm = static_cast<int64_t>(*imm);
        const auto delta = StartsWithMnemonic(mnemonic, "ADD")
                               ? signed_imm
                               : -signed_imm;
        add_rsp_use_def();
        state.rsp_offset += delta;
        if (info) {
          info->stack_pointer_delta = delta;
        }
        return true;
      }
      mark_barrier();
      return true;
    }

    if (StartsWithMnemonic(mnemonic, "MOV") &&
        IsRegisterOperand(instruction.operands[1], "RBP")) {
      add_implicit_use(MakeRegisterLocation("RBP", 64));
      add_rsp_use_def();
      if (!state.precise || !state.rbp_known) {
        mark_barrier();
        return true;
      }
      if (info) {
        info->stack_pointer_delta = state.rbp_offset - state.rsp_offset;
      }
      state.rsp_offset = state.rbp_offset;
      return true;
    }

    if (StartsWithMnemonic(mnemonic, "LEA")) {
      if (const auto *address = AddressFromOperand(instruction.operands[1])) {
        add_rsp_use_def();
        if (!state.precise || !address->index_reg.name.empty()) {
          mark_barrier();
          return true;
        }
        if (!address->base_reg.name.empty() && IsRSP(address->base_reg.name)) {
          state.rsp_offset += address->displacement;
          if (info) {
            info->stack_pointer_delta = address->displacement;
          }
          return true;
        }
        if (!address->base_reg.name.empty() && IsRBP(address->base_reg.name) &&
            state.rbp_known) {
          const auto new_rsp = state.rbp_offset + address->displacement;
          if (info) {
            info->stack_pointer_delta = new_rsp - state.rsp_offset;
          }
          state.rsp_offset = new_rsp;
          return true;
        }
      }
      mark_barrier();
      return true;
    }

    mark_barrier();
    return true;
  }

  if (instruction.operands.size() >= 2 &&
      instruction.operands[0].action == remill::Operand::kActionWrite &&
      IsRegisterOperand(instruction.operands[0], "RBP")) {
    if (StartsWithMnemonic(mnemonic, "MOV") &&
        IsRegisterOperand(instruction.operands[1], "RSP") && state.precise) {
      state.rbp_known = true;
      state.rbp_offset = state.rsp_offset;
      return true;
    }
    if (StartsWithMnemonic(mnemonic, "LEA")) {
      if (const auto *address = AddressFromOperand(instruction.operands[1])) {
        if (state.precise && address->index_reg.name.empty() &&
            !address->base_reg.name.empty() &&
            IsRSP(address->base_reg.name)) {
          state.rbp_known = true;
          state.rbp_offset = state.rsp_offset + address->displacement;
          return true;
        }
      }
    }
    state.rbp_known = false;
  }

  if (WritesRegister(instruction, "RSP")) {
    mark_barrier();
    return true;
  }

  if (WritesRegister(instruction, "RBP")) {
    state.rbp_known = false;
  }

  return true;
}

static void AnnotateInstruction(const remill::Instruction &decoded,
                                const StackState &entry_state,
                                LiftDbInstructionRecord &record) {
  record.operands.clear();
  record.uses.clear();
  record.defs.clear();
  record.stack_accesses.clear();
  record.stack_pointer_delta = 0;
  record.dynamic_stack_barrier = false;

  const auto mnemonic = ExtractMnemonic(decoded);
  StackState state = entry_state;

  for (const auto &operand : decoded.operands) {
    LiftDbOperandRecord operand_record;
    operand_record.text = operand.Serialize();
    operand_record.size_bits = static_cast<uint32_t>(operand.size);

    if (auto reg_name = RegisterNameFromOperand(operand)) {
      const auto location = MakeRegisterLocation(*reg_name, operand.size);
      if (operand.action == remill::Operand::kActionRead) {
        AddLocationToOperandAndInstruction(operand_record, record, location,
                                           true);
      } else if (operand.action == remill::Operand::kActionWrite) {
        AddLocationToOperandAndInstruction(operand_record, record, location,
                                           false);
      }
    } else if (const auto *address = AddressFromOperand(operand)) {
      if (!address->segment_base_reg.name.empty()) {
        const auto seg_loc = MakeRegisterLocation(address->segment_base_reg.name,
                                                  address->segment_base_reg.size);
        AddLocationToOperandAndInstruction(operand_record, record, seg_loc,
                                           true);
      }
      if (!address->base_reg.name.empty()) {
        const auto base_loc = MakeRegisterLocation(address->base_reg.name,
                                                   address->base_reg.size);
        AddLocationToOperandAndInstruction(operand_record, record, base_loc,
                                           true);
      }
      if (!address->index_reg.name.empty()) {
        const auto index_loc = MakeRegisterLocation(address->index_reg.name,
                                                    address->index_reg.size);
        AddLocationToOperandAndInstruction(operand_record, record, index_loc,
                                           true);
      }

      if (IsRIP(address->base_reg.name) && !address->index_reg.name.size()) {
        const auto rip_loc =
            MakeRipRelativeLocation(address->displacement, operand.size);
        AddLocationToOperandAndInstruction(operand_record, record, rip_loc,
                                           true);
      }

      LiftDbLocation exact_stack_location;
      if (address->IsMemoryAccess() &&
          TryMakeExactStackLocation(*address, state, operand.size,
                                    exact_stack_location)) {
        const bool is_read =
            address->kind == remill::Operand::Address::kMemoryRead;
        AddLocationToOperandAndInstruction(operand_record, record,
                                           exact_stack_location, is_read);
        AddStackAccess(record.stack_accesses,
                       is_read ? LiftDbStackAccessKind::kRead
                               : LiftDbStackAccessKind::kWrite,
                       exact_stack_location.offset, BytesFromBits(operand.size),
                       true, exact_stack_location.name);
      } else if (address->IsMemoryAccess()) {
        const auto memory_location = MakeMemoryLocation(operand.size);
        const bool is_read =
            address->kind == remill::Operand::Address::kMemoryRead;
        AddLocationToOperandAndInstruction(operand_record, record,
                                           memory_location, is_read);
      }
    }

    record.operands.push_back(std::move(operand_record));
  }

  TransferInfo transfer;
  ApplyStackTransfer(decoded, mnemonic, state, &transfer);
  record.stack_pointer_delta = transfer.stack_pointer_delta;
  record.dynamic_stack_barrier = transfer.dynamic_stack_barrier;

  for (const auto &location : transfer.implicit_uses) {
    AppendLocationUnique(record.uses, location);
  }
  for (const auto &location : transfer.implicit_defs) {
    AppendLocationUnique(record.defs, location);
  }
  for (const auto &access : transfer.stack_accesses) {
    record.stack_accesses.push_back(access);
  }
}

static void SortAndUnique(std::vector<uint64_t> &values) {
  std::sort(values.begin(), values.end());
  values.erase(std::unique(values.begin(), values.end()), values.end());
}

static std::optional<StackState> MergePredecessorStates(
    uint64_t block_entry_va, uint64_t function_entry_va, const LiftDatabase &db,
    const std::map<uint64_t, StackState> &out_states) {
  if (block_entry_va == function_entry_va) {
    return StackState{};
  }

  const auto *block = db.block(block_entry_va);
  if (!block || block->predecessors.empty()) {
    return std::nullopt;
  }

  bool found_any = false;
  StackState merged;
  for (auto pred_va : block->predecessors) {
    auto pred_it = out_states.find(pred_va);
    if (pred_it == out_states.end()) {
      continue;
    }
    if (!found_any) {
      merged = pred_it->second;
      found_any = true;
      continue;
    }
    if (!SameStackState(merged, pred_it->second)) {
      merged.precise = false;
      merged.rbp_known = false;
    }
  }

  if (!found_any) {
    return std::nullopt;
  }
  return merged;
}

static void ComputeLoops(uint64_t function_entry_va, LiftDatabase &db) {
  auto *function = db.function(function_entry_va);
  if (!function) {
    return;
  }

  SortAndUnique(function->block_entries);

  std::set<uint64_t> all_blocks(function->block_entries.begin(),
                                function->block_entries.end());
  std::map<uint64_t, std::set<uint64_t>> dominators;
  for (auto block_entry_va : function->block_entries) {
    if (block_entry_va == function_entry_va) {
      dominators[block_entry_va] = {block_entry_va};
    } else {
      dominators[block_entry_va] = all_blocks;
    }
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (auto block_entry_va : function->block_entries) {
      if (block_entry_va == function_entry_va) {
        continue;
      }
      const auto *block = db.block(block_entry_va);
      if (!block) {
        continue;
      }
      std::set<uint64_t> next = all_blocks;
      bool first = true;
      for (auto pred_va : block->predecessors) {
        auto it = dominators.find(pred_va);
        if (it == dominators.end()) {
          continue;
        }
        if (first) {
          next = it->second;
          first = false;
        } else {
          std::set<uint64_t> intersection;
          std::set_intersection(next.begin(), next.end(), it->second.begin(),
                                it->second.end(),
                                std::inserter(intersection, intersection.begin()));
          next = std::move(intersection);
        }
      }
      next.insert(block_entry_va);
      if (next != dominators[block_entry_va]) {
        dominators[block_entry_va] = std::move(next);
        changed = true;
      }
    }
  }

  std::map<uint64_t, LiftDbLoopRecord> loops_by_header;
  for (auto block_entry_va : function->block_entries) {
    const auto *block = db.block(block_entry_va);
    if (!block) {
      continue;
    }
    for (const auto &edge : block->successors) {
      if (!all_blocks.count(edge.target_block_va)) {
        continue;
      }
      const auto dom_it = dominators.find(block_entry_va);
      if (dom_it == dominators.end() ||
          !dom_it->second.count(edge.target_block_va)) {
        continue;
      }

      auto &loop = loops_by_header[edge.target_block_va];
      loop.header_va = edge.target_block_va;
      PushUnique(loop.latch_vas, block_entry_va);

      std::set<uint64_t> body = {edge.target_block_va, block_entry_va};
      std::deque<uint64_t> pending = {block_entry_va};
      while (!pending.empty()) {
        const auto current = pending.front();
        pending.pop_front();
        const auto *current_block = db.block(current);
        if (!current_block) {
          continue;
        }
        for (auto pred_va : current_block->predecessors) {
          if (body.insert(pred_va).second && pred_va != edge.target_block_va) {
            pending.push_back(pred_va);
          }
        }
      }
      loop.body_block_vas.assign(body.begin(), body.end());
    }
  }

  function->loops.clear();
  for (auto &[_, loop] : loops_by_header) {
    SortAndUnique(loop.latch_vas);
    SortAndUnique(loop.body_block_vas);
    function->loops.push_back(std::move(loop));
  }
  std::sort(function->loops.begin(), function->loops.end(),
            [](const LiftDbLoopRecord &lhs, const LiftDbLoopRecord &rhs) {
              return lhs.header_va < rhs.header_va;
            });
}

static void ComputeUseDef(uint64_t function_entry_va, LiftDatabase &db) {
  auto *function = db.function(function_entry_va);
  if (!function) {
    return;
  }

  SortAndUnique(function->block_entries);

  std::map<uint64_t, ReachingDefs> in_defs;
  std::map<uint64_t, ReachingDefs> out_defs;
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto block_entry_va : function->block_entries) {
      ReachingDefs incoming;
      if (block_entry_va != function_entry_va) {
        const auto *block = db.block(block_entry_va);
        if (block) {
          for (auto pred_va : block->predecessors) {
            auto pred_it = out_defs.find(pred_va);
            if (pred_it == out_defs.end()) {
              continue;
            }
            for (const auto &[key, defs] : pred_it->second) {
              auto &merged = incoming[key];
              merged.insert(defs.begin(), defs.end());
            }
          }
        }
      }

      ReachingDefs current = incoming;
      const auto *block = db.block(block_entry_va);
      if (block) {
        for (auto inst_va : block->instruction_vas) {
          const auto *instruction = db.instruction(inst_va);
          if (!instruction) {
            continue;
          }
          for (const auto &location : instruction->defs) {
            if (!ShouldTrackUseDef(location)) {
              continue;
            }
            current[LocationKey(location)] = {inst_va};
          }
        }
      }

      if (in_defs[block_entry_va] != incoming) {
        in_defs[block_entry_va] = std::move(incoming);
        changed = true;
      }
      if (out_defs[block_entry_va] != current) {
        out_defs[block_entry_va] = std::move(current);
        changed = true;
      }
    }
  }

  std::map<std::string, LiftDbLocation> location_by_key;
  std::map<std::string, std::map<uint64_t, std::vector<uint64_t>>> chain_uses;
  for (auto block_entry_va : function->block_entries) {
    ReachingDefs current = in_defs[block_entry_va];
    const auto *block = db.block(block_entry_va);
    if (!block) {
      continue;
    }

    for (auto inst_va : block->instruction_vas) {
      const auto *instruction = db.instruction(inst_va);
      if (!instruction) {
        continue;
      }

      for (const auto &location : instruction->uses) {
        if (!ShouldTrackUseDef(location)) {
          continue;
        }
        const auto key = LocationKey(location);
        location_by_key[key] = location;
        auto defs_it = current.find(key);
        if (defs_it == current.end()) {
          continue;
        }
        for (auto def_va : defs_it->second) {
          PushUnique(chain_uses[key][def_va], inst_va);
        }
      }

      for (const auto &location : instruction->defs) {
        if (!ShouldTrackUseDef(location)) {
          continue;
        }
        const auto key = LocationKey(location);
        location_by_key[key] = location;
        current[key] = {inst_va};
      }
    }
  }

  function->use_def_chains.clear();
  for (const auto &[key, defs_to_uses] : chain_uses) {
    const auto loc_it = location_by_key.find(key);
    if (loc_it == location_by_key.end()) {
      continue;
    }
    for (const auto &[def_va, uses] : defs_to_uses) {
      LiftDbUseDefChainRecord chain;
      chain.location = loc_it->second;
      chain.defining_instruction_va = def_va;
      chain.using_instruction_vas = uses;
      SortAndUnique(chain.using_instruction_vas);
      function->use_def_chains.push_back(std::move(chain));
    }
  }
  std::sort(function->use_def_chains.begin(), function->use_def_chains.end(),
            [](const LiftDbUseDefChainRecord &lhs,
               const LiftDbUseDefChainRecord &rhs) {
              if (lhs.defining_instruction_va != rhs.defining_instruction_va) {
                return lhs.defining_instruction_va < rhs.defining_instruction_va;
              }
              return LocationKey(lhs.location) < LocationKey(rhs.location);
            });
}

}  // namespace

StaticLiftBuilder::StaticLiftBuilder(const remill::Arch *arch,
                                     const BinaryMemoryMap *memory_map,
                                     TargetArch target_arch,
                                     StaticLiftBuilderOptions options)
    : arch_(arch),
      memory_map_(memory_map),
      target_arch_(target_arch),
      options_(options) {}

bool StaticLiftBuilder::buildFunction(uint64_t entry_va, LiftDatabase &db) const {
  if (!entry_va || !arch_ || !memory_map_ ||
      target_arch_ != TargetArch::kX86_64) {
    return false;
  }

  auto lift_target_policy =
      createBinaryLiftTargetPolicy(memory_map_, target_arch_);
  if (!lift_target_policy) {
    return false;
  }

  if (!options_.refresh_existing) {
    if (const auto *existing = db.function(entry_va);
        existing && !existing->block_entries.empty()) {
      return true;
    }
  } else {
    db.clearFunction(entry_va);
  }

  auto &function = db.upsertFunction(entry_va);
  function.entry_va = entry_va;
  function.discovered_from_overlay = false;
  function.block_entries.clear();
  function.loops.clear();
  function.use_def_chains.clear();
  function.unresolved_branch_vas.clear();
  function.dynamic_stack_barrier_vas.clear();

  if (db.manifest().arch == LiftDbArch::kUnknown) {
    db.manifest().arch = LiftDbArch::kX64;
  }

  DecodedInstMap decoded_instructions;
  std::set<uint64_t> discovered_blocks = {entry_va};
  std::set<uint64_t> scanned_blocks;
  std::deque<uint64_t> pending_blocks = {entry_va};

  auto enqueue_block = [&](uint64_t target_va) {
    if (!target_va) {
      return false;
    }
    if (discovered_blocks.insert(target_va).second) {
      pending_blocks.push_back(target_va);
    }
    return true;
  };

  auto resolve_block_target = [&](uint64_t source_va, uint64_t raw_target_va,
                                  LiftTargetEdgeKind edge_kind) {
    if (!raw_target_va) {
      return uint64_t{0};
    }
    const auto decision =
        lift_target_policy->ResolveLiftTarget(source_va, raw_target_va,
                                              edge_kind);
    if (!decision.shouldLift() || !decision.effective_target_pc.has_value()) {
      return uint64_t{0};
    }
    return *decision.effective_target_pc;
  };

  while (!pending_blocks.empty()) {
    const auto block_entry_va = pending_blocks.front();
    pending_blocks.pop_front();
    if (!scanned_blocks.insert(block_entry_va).second) {
      continue;
    }
    if (!isExecutableLiftTarget(memory_map_, block_entry_va)) {
      PushUnique(function.unresolved_branch_vas, block_entry_va);
      continue;
    }

    auto &block = db.upsertBlock(entry_va, block_entry_va);
    block.entry_va = block_entry_va;
    block.function_entry_va = entry_va;
    block.from_overlay_split = false;
    block.instruction_vas.clear();
    block.successors.clear();
    block.predecessors.clear();

    uint64_t current_pc = block_entry_va;
    while (true) {
      if (current_pc != block_entry_va && discovered_blocks.count(current_pc)) {
        block.successors.push_back(
            {LiftDbEdgeKind::kFallthrough, block_entry_va, current_pc, false});
        break;
      }

      remill::Instruction instruction;
      if (!omill::DecodeInstruction(*arch_, *memory_map_, current_pc, instruction)) {
        if (block.instruction_vas.empty()) {
          PushUnique(function.unresolved_branch_vas, block_entry_va);
        } else {
          PushUnique(function.unresolved_branch_vas, current_pc);
        }
        break;
      }

      decoded_instructions[current_pc] = instruction;

      auto &record = db.upsertInstruction(current_pc);
      record.va = current_pc;
      if (!record.function_entry_va) {
        record.function_entry_va = entry_va;
      }
      if (!record.block_entry_va) {
        record.block_entry_va = block_entry_va;
      }
      record.bytes_hex = HexBytes(instruction.bytes);
      record.mnemonic = ExtractMnemonic(instruction);
      record.category = MapCategory(instruction);
      record.size = static_cast<uint32_t>(instruction.NumBytes());
      record.has_fallthrough = false;
      record.fallthrough_va = 0;
      record.has_branch_target = false;
      record.branch_target_va = 0;
      record.dynamic_stack_barrier = false;
      block.instruction_vas.push_back(current_pc);

      const auto fallthrough_pc =
          instruction.branch_not_taken_pc ? instruction.branch_not_taken_pc
                                          : instruction.next_pc;

      auto add_fallthrough = [&](uint64_t target_va) {
        const auto effective_target_va =
            resolve_block_target(current_pc, target_va,
                                 instruction.IsFunctionCall()
                                     ? LiftTargetEdgeKind::kCallFallthrough
                                     : LiftTargetEdgeKind::kConditionalNotTaken);
        if (!effective_target_va) {
          return false;
        }
        record.has_fallthrough = true;
        record.fallthrough_va = effective_target_va;
        block.successors.push_back(
            {LiftDbEdgeKind::kFallthrough, block_entry_va, effective_target_va,
             false});
        enqueue_block(effective_target_va);
        return true;
      };

      auto add_direct_target = [&](LiftDbEdgeKind kind, uint64_t target_va,
                                   bool queue_target) {
        const auto effective_target_va =
            resolve_block_target(current_pc, target_va,
                                 kind == LiftDbEdgeKind::kCall
                                     ? LiftTargetEdgeKind::kDirectCallTarget
                                 : instruction.IsConditionalBranch()
                                     ? LiftTargetEdgeKind::kConditionalTaken
                                     : LiftTargetEdgeKind::kDirectJump);
        if (!effective_target_va) {
          PushUnique(function.unresolved_branch_vas, current_pc);
          return false;
        }
        record.has_branch_target = true;
        record.branch_target_va = effective_target_va;
        block.successors.push_back(
            {kind, block_entry_va, effective_target_va, false});
        if (queue_target) {
          enqueue_block(effective_target_va);
        }
        return true;
      };

      if (instruction.IsFunctionCall()) {
        if (instruction.branch_taken_pc) {
          add_direct_target(LiftDbEdgeKind::kCall, instruction.branch_taken_pc,
                            false);
          if (auto effect = analyzeCallTargetBridgeEffect(
                  *memory_map_, instruction.branch_taken_pc)) {
            LiftDbCallTargetBridge bridge;
            bridge.stack_writes.reserve(effect->stack_writes.size());
            for (const auto &w : effect->stack_writes) {
              LiftDbBridgeStackWrite db_w;
              db_w.rsp_offset = w.rsp_offset;
              db_w.size_bytes = w.size_bytes;
              db_w.value = w.value;
              bridge.stack_writes.push_back(db_w);
            }
            bridge.net_rsp_delta = effect->net_rsp_delta;
            bridge.final_jump_target_pc = effect->final_jump_target_pc;
            bridge.terminator = static_cast<uint8_t>(effect->terminator);
            bridge.instructions_modeled = effect->instructions_modeled;
            record.call_target_bridge = std::move(bridge);
          }
        } else {
          PushUnique(function.unresolved_branch_vas, current_pc);
        }
        if (!add_fallthrough(instruction.next_pc)) {
          PushUnique(function.unresolved_branch_vas, current_pc);
        }
        break;
      }

      if (instruction.IsFunctionReturn()) {
        block.successors.push_back(
            {LiftDbEdgeKind::kReturn, block_entry_va, 0, false});
        if (instruction.IsConditionalBranch() && fallthrough_pc) {
          add_fallthrough(fallthrough_pc);
        }
        break;
      }

      switch (instruction.category) {
        case remill::Instruction::kCategoryDirectJump:
          add_direct_target(LiftDbEdgeKind::kBranchTaken,
                            instruction.branch_taken_pc, true);
          break;

        case remill::Instruction::kCategoryConditionalBranch:
          add_direct_target(LiftDbEdgeKind::kBranchTaken,
                            instruction.branch_taken_pc, true);
          if (!add_fallthrough(fallthrough_pc)) {
            PushUnique(function.unresolved_branch_vas, current_pc);
          }
          break;

        case remill::Instruction::kCategoryIndirectJump:
        case remill::Instruction::kCategoryConditionalIndirectJump: {
          bool recovered_target = false;
          for (uint64_t target_va :
               discoverJumpTableTargetsForInstruction(*memory_map_,
                                                     instruction.pc)) {
            const auto effective_target_va =
                resolve_block_target(current_pc, target_va,
                                     LiftTargetEdgeKind::kIndirectTarget);
            if (!effective_target_va) {
              continue;
            }
            recovered_target = true;
            block.successors.push_back({LiftDbEdgeKind::kBranchTaken,
                                        block_entry_va, effective_target_va,
                                        false});
            enqueue_block(effective_target_va);
          }
          if (!recovered_target) {
            PushUnique(function.unresolved_branch_vas, current_pc);
            block.successors.push_back(
                {LiftDbEdgeKind::kUnresolved, block_entry_va, 0, false});
          }
          if (instruction.IsConditionalBranch() && fallthrough_pc) {
            add_fallthrough(fallthrough_pc);
          }
          break;
        }

        case remill::Instruction::kCategoryAsyncHyperCall:
        case remill::Instruction::kCategoryConditionalAsyncHyperCall:
          PushUnique(function.unresolved_branch_vas, current_pc);
          block.successors.push_back(
              {LiftDbEdgeKind::kUnresolved, block_entry_va, 0, false});
          if (instruction.IsConditionalBranch() && fallthrough_pc) {
            add_fallthrough(fallthrough_pc);
          }
          break;

        default:
          if (!instruction.next_pc || instruction.next_pc <= current_pc) {
            PushUnique(function.unresolved_branch_vas, current_pc);
            break;
          }
          if (discovered_blocks.count(instruction.next_pc)) {
            add_fallthrough(instruction.next_pc);
            break;
          }
          current_pc = instruction.next_pc;
          continue;
      }

      break;
    }
  }

  SortAndUnique(function.block_entries);
  db.rebuildPredecessors(entry_va);

  std::map<uint64_t, StackState> block_in_states;
  std::map<uint64_t, StackState> block_out_states;
  std::deque<uint64_t> stack_worklist(function.block_entries.begin(),
                                      function.block_entries.end());
  std::set<uint64_t> queued(function.block_entries.begin(),
                            function.block_entries.end());

  while (!stack_worklist.empty()) {
    const auto block_entry_va = stack_worklist.front();
    stack_worklist.pop_front();
    queued.erase(block_entry_va);

    auto maybe_entry_state = MergePredecessorStates(block_entry_va, entry_va, db,
                                                    block_out_states);
    if (!maybe_entry_state) {
      continue;
    }

    const auto *block = db.block(block_entry_va);
    if (!block) {
      continue;
    }

    block_in_states[block_entry_va] = *maybe_entry_state;
    StackState current_state = *maybe_entry_state;
    for (auto inst_va : block->instruction_vas) {
      const auto decoded_it = decoded_instructions.find(inst_va);
      if (decoded_it == decoded_instructions.end()) {
        continue;
      }
      ApplyStackTransfer(decoded_it->second, ExtractMnemonic(decoded_it->second),
                         current_state, nullptr);
    }

    const auto out_it = block_out_states.find(block_entry_va);
    if (out_it != block_out_states.end() &&
        SameStackState(out_it->second, current_state)) {
      continue;
    }

    block_out_states[block_entry_va] = current_state;
    for (const auto &edge : block->successors) {
      if (!edge.target_block_va || !db.block(edge.target_block_va)) {
        continue;
      }
      if (queued.insert(edge.target_block_va).second) {
        stack_worklist.push_back(edge.target_block_va);
      }
    }
  }

  for (auto block_entry_va : function.block_entries) {
    auto entry_state_it = block_in_states.find(block_entry_va);
    StackState state = entry_state_it != block_in_states.end()
                           ? entry_state_it->second
                           : StackState{};
    auto *block = db.block(block_entry_va);
    if (!block) {
      continue;
    }
    for (auto inst_va : block->instruction_vas) {
      auto decoded_it = decoded_instructions.find(inst_va);
      auto *record = db.instruction(inst_va);
      if (decoded_it == decoded_instructions.end() || !record) {
        continue;
      }
      AnnotateInstruction(decoded_it->second, state, *record);
      if (record->dynamic_stack_barrier) {
        PushUnique(function.dynamic_stack_barrier_vas, inst_va);
      }
      ApplyStackTransfer(decoded_it->second, record->mnemonic, state, nullptr);
    }
  }

  SortAndUnique(function.unresolved_branch_vas);
  SortAndUnique(function.dynamic_stack_barrier_vas);

  if (options_.compute_loops) {
    ComputeLoops(entry_va, db);
  }
  if (options_.compute_use_def) {
    ComputeUseDef(entry_va, db);
  }

  db.bumpRevision();
  return true;
}

bool StaticLiftBuilder::buildFunctions(llvm::ArrayRef<uint64_t> entry_vas,
                                       LiftDatabase &db) const {
  bool built_any = false;
  for (auto entry_va : entry_vas) {
    built_any |= buildFunction(entry_va, db);
  }
  return built_any;
}

void StaticLiftBuilder::importTraceMapAsOverlays(
    const VMTraceMap &trace_map,
    llvm::ArrayRef<StaticLiftOverlayKey> overlay_keys,
    LiftDatabase &db) const {
  bool imported_any = false;
  for (const auto &key : overlay_keys) {
    if (!key.handler_va) {
      continue;
    }

    auto flat_trace = trace_map.followFlatTrace(key.handler_va, key.incoming_hash);
    if (flat_trace.records.empty()) {
      continue;
    }

    const auto overlay_key = LiftDbOverlayKey(key.handler_va, key.incoming_hash);
    auto &function = db.upsertFunction(key.handler_va);
    function.entry_va = key.handler_va;
    function.discovered_from_overlay = true;

    auto &overlay = db.upsertTraceOverlay(overlay_key);
    overlay.overlay_key = overlay_key;
    overlay.handler_va = key.handler_va;
    overlay.incoming_hash = key.incoming_hash;
    overlay.function_entry_va = key.handler_va;
    overlay.path_block_entries.clear();
    overlay.constrained_edges.clear();
    overlay.native_exit_vas.clear();
    overlay.cloned_block_entries.clear();

    auto append_edge_unique = [&](uint64_t source_va, uint64_t target_va) {
      auto it = std::find_if(
          overlay.constrained_edges.begin(), overlay.constrained_edges.end(),
          [&](const LiftDbEdgeRecord &edge) {
            return edge.kind == LiftDbEdgeKind::kOverlay &&
                   edge.source_block_va == source_va &&
                   edge.target_block_va == target_va && edge.from_overlay;
          });
      if (it == overlay.constrained_edges.end()) {
        overlay.constrained_edges.push_back(
            {LiftDbEdgeKind::kOverlay, source_va, target_va, true});
      }
    };

    for (const auto &record : flat_trace.records) {
      buildFunction(record.handler_va, db);
      auto &overlay_function = db.upsertFunction(record.handler_va);
      overlay_function.entry_va = record.handler_va;
      overlay_function.discovered_from_overlay = true;

      PushUnique(overlay.path_block_entries, record.handler_va);

      if (record.native_target_va) {
        PushUnique(overlay.native_exit_vas, record.native_target_va);
      }
      if (record.exit_target_va) {
        PushUnique(overlay.native_exit_vas, record.exit_target_va);
      }

      for (auto successor_va : record.successors) {
        if (!successor_va) {
          continue;
        }
        buildFunction(successor_va, db);
        auto &successor_function = db.upsertFunction(successor_va);
        successor_function.entry_va = successor_va;
        successor_function.discovered_from_overlay = true;
        append_edge_unique(record.handler_va, successor_va);
        PushUnique(overlay.path_block_entries, successor_va);
      }
    }
    imported_any = true;
  }

  if (imported_any) {
    db.bumpRevision();
  }
}

}  // namespace omill

#include "omill/BC/LiftDatabaseIO.h"

#include <filesystem>
#include <system_error>
#include <utility>

#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "omill/BC/LiftDatabase.h"

namespace omill {
namespace {

using llvm::json::Array;
using llvm::json::Object;
using llvm::json::Value;

static std::string HexU64(uint64_t value) {
  return "0x" + llvm::utohexstr(value);
}

static std::string HexI64(int64_t value) {
  if (value < 0) {
    return "-" + HexU64(static_cast<uint64_t>(-value));
  }
  return HexU64(static_cast<uint64_t>(value));
}

static bool ParseU64(const Value &value, uint64_t &out) {
  if (auto integer = value.getAsInteger()) {
    out = static_cast<uint64_t>(*integer);
    return true;
  }

  auto text = value.getAsString();
  if (!text) {
    return false;
  }

  llvm::StringRef str = *text;
  bool negative = str.consume_front("-");
  str.consume_front("0x");
  uint64_t parsed = 0;
  if (str.getAsInteger(16, parsed)) {
    return false;
  }
  out = negative ? static_cast<uint64_t>(-static_cast<int64_t>(parsed))
                 : parsed;
  return true;
}

static bool ParseI64(const Value &value, int64_t &out) {
  if (auto integer = value.getAsInteger()) {
    out = static_cast<int64_t>(*integer);
    return true;
  }

  auto text = value.getAsString();
  if (!text) {
    return false;
  }

  llvm::StringRef str = *text;
  bool negative = str.consume_front("-");
  str.consume_front("0x");
  uint64_t parsed = 0;
  if (str.getAsInteger(16, parsed)) {
    return false;
  }
  out = negative ? -static_cast<int64_t>(parsed) : static_cast<int64_t>(parsed);
  return true;
}

static const char *ToString(LiftDbArch arch) {
  switch (arch) {
    case LiftDbArch::kX64:
      return "x64";
    case LiftDbArch::kUnknown:
    default:
      return "unknown";
  }
}

static LiftDbArch ParseArch(llvm::StringRef text) {
  if (text == "x64") {
    return LiftDbArch::kX64;
  }
  return LiftDbArch::kUnknown;
}

static const char *ToString(LiftDbLocationKind kind) {
  switch (kind) {
    case LiftDbLocationKind::kRegister:
      return "register";
    case LiftDbLocationKind::kFlag:
      return "flag";
    case LiftDbLocationKind::kStackCell:
      return "stack_cell";
    case LiftDbLocationKind::kMemory:
      return "memory";
    case LiftDbLocationKind::kTemporary:
      return "temporary";
    case LiftDbLocationKind::kRipRelative:
      return "rip_relative";
    case LiftDbLocationKind::kSynthetic:
      return "synthetic";
    case LiftDbLocationKind::kUnknown:
    default:
      return "unknown";
  }
}

static LiftDbLocationKind ParseLocationKind(llvm::StringRef text) {
  if (text == "register") {
    return LiftDbLocationKind::kRegister;
  } else if (text == "flag") {
    return LiftDbLocationKind::kFlag;
  } else if (text == "stack_cell") {
    return LiftDbLocationKind::kStackCell;
  } else if (text == "memory") {
    return LiftDbLocationKind::kMemory;
  } else if (text == "temporary") {
    return LiftDbLocationKind::kTemporary;
  } else if (text == "rip_relative") {
    return LiftDbLocationKind::kRipRelative;
  } else if (text == "synthetic") {
    return LiftDbLocationKind::kSynthetic;
  }
  return LiftDbLocationKind::kUnknown;
}

static const char *ToString(LiftDbCategory category) {
  switch (category) {
    case LiftDbCategory::kNormal:
      return "normal";
    case LiftDbCategory::kDirectJump:
      return "direct_jump";
    case LiftDbCategory::kIndirectJump:
      return "indirect_jump";
    case LiftDbCategory::kConditionalBranch:
      return "conditional_branch";
    case LiftDbCategory::kDirectCall:
      return "direct_call";
    case LiftDbCategory::kIndirectCall:
      return "indirect_call";
    case LiftDbCategory::kReturn:
      return "return";
    case LiftDbCategory::kUnknown:
    default:
      return "unknown";
  }
}

static LiftDbCategory ParseCategory(llvm::StringRef text) {
  if (text == "normal") {
    return LiftDbCategory::kNormal;
  } else if (text == "direct_jump") {
    return LiftDbCategory::kDirectJump;
  } else if (text == "indirect_jump") {
    return LiftDbCategory::kIndirectJump;
  } else if (text == "conditional_branch") {
    return LiftDbCategory::kConditionalBranch;
  } else if (text == "direct_call") {
    return LiftDbCategory::kDirectCall;
  } else if (text == "indirect_call") {
    return LiftDbCategory::kIndirectCall;
  } else if (text == "return") {
    return LiftDbCategory::kReturn;
  }
  return LiftDbCategory::kUnknown;
}

static const char *ToString(LiftDbStackAccessKind kind) {
  switch (kind) {
    case LiftDbStackAccessKind::kRead:
      return "read";
    case LiftDbStackAccessKind::kWrite:
      return "write";
    case LiftDbStackAccessKind::kReadWrite:
      return "read_write";
    case LiftDbStackAccessKind::kReturnAddress:
      return "return_address";
    case LiftDbStackAccessKind::kShadowSpace:
      return "shadow_space";
    case LiftDbStackAccessKind::kBarrier:
      return "barrier";
    case LiftDbStackAccessKind::kUnknown:
    default:
      return "unknown";
  }
}

static LiftDbStackAccessKind ParseStackAccessKind(llvm::StringRef text) {
  if (text == "read") {
    return LiftDbStackAccessKind::kRead;
  } else if (text == "write") {
    return LiftDbStackAccessKind::kWrite;
  } else if (text == "read_write") {
    return LiftDbStackAccessKind::kReadWrite;
  } else if (text == "return_address") {
    return LiftDbStackAccessKind::kReturnAddress;
  } else if (text == "shadow_space") {
    return LiftDbStackAccessKind::kShadowSpace;
  } else if (text == "barrier") {
    return LiftDbStackAccessKind::kBarrier;
  }
  return LiftDbStackAccessKind::kUnknown;
}

static const char *ToString(LiftDbEdgeKind kind) {
  switch (kind) {
    case LiftDbEdgeKind::kFallthrough:
      return "fallthrough";
    case LiftDbEdgeKind::kBranchTaken:
      return "branch_taken";
    case LiftDbEdgeKind::kCall:
      return "call";
    case LiftDbEdgeKind::kReturn:
      return "return";
    case LiftDbEdgeKind::kUnresolved:
      return "unresolved";
    case LiftDbEdgeKind::kOverlay:
      return "overlay";
    case LiftDbEdgeKind::kUnknown:
    default:
      return "unknown";
  }
}

static LiftDbEdgeKind ParseEdgeKind(llvm::StringRef text) {
  if (text == "fallthrough") {
    return LiftDbEdgeKind::kFallthrough;
  } else if (text == "branch_taken") {
    return LiftDbEdgeKind::kBranchTaken;
  } else if (text == "call") {
    return LiftDbEdgeKind::kCall;
  } else if (text == "return") {
    return LiftDbEdgeKind::kReturn;
  } else if (text == "unresolved") {
    return LiftDbEdgeKind::kUnresolved;
  } else if (text == "overlay") {
    return LiftDbEdgeKind::kOverlay;
  }
  return LiftDbEdgeKind::kUnknown;
}

template <typename T, typename Fn>
static Array ToJSONArray(const std::vector<T> &values, Fn &&fn) {
  Array out;
  for (const auto &value : values) {
    out.emplace_back(fn(value));
  }
  return out;
}

static Array ToHexArray(const std::vector<uint64_t> &values) {
  Array out;
  for (auto value : values) {
    out.emplace_back(HexU64(value));
  }
  return out;
}

static Value ToJSON(const LiftDbLocation &location) {
  Object obj;
  obj["kind"] = ToString(location.kind);
  obj["name"] = location.name;
  obj["base_register"] = location.base_register;
  obj["offset"] = HexI64(location.offset);
  obj["size_bits"] = static_cast<int64_t>(location.size_bits);
  obj["version"] = static_cast<int64_t>(location.version);
  obj["precise"] = location.precise;
  return obj;
}

static bool FromJSON(const Value &value, LiftDbLocation &location) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto text = obj->getString("kind")) {
    location.kind = ParseLocationKind(*text);
  }
  if (auto text = obj->getString("name")) {
    location.name = text->str();
  }
  if (auto text = obj->getString("base_register")) {
    location.base_register = text->str();
  }
  if (auto *offset = obj->get("offset")) {
    ParseI64(*offset, location.offset);
  }
  if (auto integer = obj->getInteger("size_bits")) {
    location.size_bits = static_cast<uint32_t>(*integer);
  }
  if (auto integer = obj->getInteger("version")) {
    location.version = static_cast<uint32_t>(*integer);
  }
  if (auto boolean = obj->getBoolean("precise")) {
    location.precise = *boolean;
  }
  return true;
}

static Value ToJSON(const LiftDbOperandRecord &operand) {
  Object obj;
  obj["text"] = operand.text;
  obj["size_bits"] = static_cast<int64_t>(operand.size_bits);
  obj["reads"] = ToJSONArray(operand.reads, [](const LiftDbLocation &location) {
    return ToJSON(location);
  });
  obj["writes"] =
      ToJSONArray(operand.writes, [](const LiftDbLocation &location) {
        return ToJSON(location);
      });
  return obj;
}

static bool FromJSON(const Value &value, LiftDbOperandRecord &operand) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto text = obj->getString("text")) {
    operand.text = text->str();
  }
  if (auto integer = obj->getInteger("size_bits")) {
    operand.size_bits = static_cast<uint32_t>(*integer);
  }
  if (auto *reads = obj->getArray("reads")) {
    operand.reads.clear();
    for (const auto &entry : *reads) {
      LiftDbLocation location;
      if (FromJSON(entry, location)) {
        operand.reads.push_back(std::move(location));
      }
    }
  }
  if (auto *writes = obj->getArray("writes")) {
    operand.writes.clear();
    for (const auto &entry : *writes) {
      LiftDbLocation location;
      if (FromJSON(entry, location)) {
        operand.writes.push_back(std::move(location));
      }
    }
  }
  return true;
}

static Value ToJSON(const LiftDbStackAccessRecord &access) {
  Object obj;
  obj["kind"] = ToString(access.kind);
  obj["offset"] = HexI64(access.offset);
  obj["size"] = static_cast<int64_t>(access.size);
  obj["exact"] = access.exact;
  obj["location_name"] = access.location_name;
  return obj;
}

static bool FromJSON(const Value &value, LiftDbStackAccessRecord &access) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto text = obj->getString("kind")) {
    access.kind = ParseStackAccessKind(*text);
  }
  if (auto *offset = obj->get("offset")) {
    ParseI64(*offset, access.offset);
  }
  if (auto integer = obj->getInteger("size")) {
    access.size = static_cast<uint32_t>(*integer);
  }
  if (auto boolean = obj->getBoolean("exact")) {
    access.exact = *boolean;
  }
  if (auto text = obj->getString("location_name")) {
    access.location_name = text->str();
  }
  return true;
}

static Value ToJSON(const LiftDbBridgeStackWrite &write) {
  Object obj;
  obj["rsp_offset"] = HexI64(write.rsp_offset);
  obj["size_bytes"] = static_cast<int64_t>(write.size_bytes);
  obj["value"] = HexU64(write.value);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbBridgeStackWrite &write) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }
  if (auto *off = obj->get("rsp_offset")) {
    ParseI64(*off, write.rsp_offset);
  }
  if (auto integer = obj->getInteger("size_bytes")) {
    write.size_bytes = static_cast<uint32_t>(*integer);
  }
  if (auto *val = obj->get("value")) {
    ParseU64(*val, write.value);
  }
  return true;
}

static Value ToJSON(const LiftDbCallTargetBridge &bridge) {
  Object obj;
  obj["stack_writes"] = ToJSONArray(
      bridge.stack_writes,
      [](const LiftDbBridgeStackWrite &w) { return ToJSON(w); });
  obj["net_rsp_delta"] = HexI64(bridge.net_rsp_delta);
  obj["final_jump_target_pc"] = HexU64(bridge.final_jump_target_pc);
  obj["terminator"] = static_cast<int64_t>(bridge.terminator);
  obj["instructions_modeled"] =
      static_cast<int64_t>(bridge.instructions_modeled);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbCallTargetBridge &bridge) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }
  bridge.stack_writes.clear();
  if (auto *writes = obj->getArray("stack_writes")) {
    for (const auto &entry : *writes) {
      LiftDbBridgeStackWrite w;
      if (FromJSON(entry, w)) {
        bridge.stack_writes.push_back(std::move(w));
      }
    }
  }
  if (auto *delta = obj->get("net_rsp_delta")) {
    ParseI64(*delta, bridge.net_rsp_delta);
  }
  if (auto *jp = obj->get("final_jump_target_pc")) {
    ParseU64(*jp, bridge.final_jump_target_pc);
  }
  if (auto integer = obj->getInteger("terminator")) {
    bridge.terminator = static_cast<uint8_t>(*integer);
  }
  if (auto integer = obj->getInteger("instructions_modeled")) {
    bridge.instructions_modeled = static_cast<uint32_t>(*integer);
  }
  return true;
}

static Value ToJSON(const LiftDbInstructionRecord &instruction) {
  Object obj;
  obj["va"] = HexU64(instruction.va);
  obj["function_entry_va"] = HexU64(instruction.function_entry_va);
  obj["block_entry_va"] = HexU64(instruction.block_entry_va);
  obj["bytes_hex"] = instruction.bytes_hex;
  obj["mnemonic"] = instruction.mnemonic;
  obj["category"] = ToString(instruction.category);
  obj["size"] = static_cast<int64_t>(instruction.size);
  obj["stack_pointer_delta"] = HexI64(instruction.stack_pointer_delta);
  obj["has_fallthrough"] = instruction.has_fallthrough;
  obj["fallthrough_va"] = HexU64(instruction.fallthrough_va);
  obj["has_branch_target"] = instruction.has_branch_target;
  obj["branch_target_va"] = HexU64(instruction.branch_target_va);
  obj["dynamic_stack_barrier"] = instruction.dynamic_stack_barrier;
  obj["operands"] =
      ToJSONArray(instruction.operands, [](const LiftDbOperandRecord &operand) {
        return ToJSON(operand);
      });
  obj["uses"] = ToJSONArray(instruction.uses, [](const LiftDbLocation &location) {
    return ToJSON(location);
  });
  obj["defs"] = ToJSONArray(instruction.defs, [](const LiftDbLocation &location) {
    return ToJSON(location);
  });
  obj["stack_accesses"] =
      ToJSONArray(instruction.stack_accesses,
                  [](const LiftDbStackAccessRecord &access) {
                    return ToJSON(access);
                  });
  if (instruction.call_target_bridge.has_value()) {
    obj["call_target_bridge"] = ToJSON(*instruction.call_target_bridge);
  }
  return obj;
}

static bool FromJSON(const Value &value, LiftDbInstructionRecord &instruction) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto *va = obj->get("va")) {
    ParseU64(*va, instruction.va);
  }
  if (auto *entry = obj->get("function_entry_va")) {
    ParseU64(*entry, instruction.function_entry_va);
  }
  if (auto *entry = obj->get("block_entry_va")) {
    ParseU64(*entry, instruction.block_entry_va);
  }
  if (auto text = obj->getString("bytes_hex")) {
    instruction.bytes_hex = text->str();
  }
  if (auto text = obj->getString("mnemonic")) {
    instruction.mnemonic = text->str();
  }
  if (auto text = obj->getString("category")) {
    instruction.category = ParseCategory(*text);
  }
  if (auto integer = obj->getInteger("size")) {
    instruction.size = static_cast<uint32_t>(*integer);
  }
  if (auto *delta = obj->get("stack_pointer_delta")) {
    ParseI64(*delta, instruction.stack_pointer_delta);
  }
  if (auto boolean = obj->getBoolean("has_fallthrough")) {
    instruction.has_fallthrough = *boolean;
  }
  if (auto *fallthrough = obj->get("fallthrough_va")) {
    ParseU64(*fallthrough, instruction.fallthrough_va);
  }
  if (auto boolean = obj->getBoolean("has_branch_target")) {
    instruction.has_branch_target = *boolean;
  }
  if (auto *branch = obj->get("branch_target_va")) {
    ParseU64(*branch, instruction.branch_target_va);
  }
  if (auto boolean = obj->getBoolean("dynamic_stack_barrier")) {
    instruction.dynamic_stack_barrier = *boolean;
  }
  if (auto *operands = obj->getArray("operands")) {
    instruction.operands.clear();
    for (const auto &entry : *operands) {
      LiftDbOperandRecord operand;
      if (FromJSON(entry, operand)) {
        instruction.operands.push_back(std::move(operand));
      }
    }
  }
  if (auto *uses = obj->getArray("uses")) {
    instruction.uses.clear();
    for (const auto &entry : *uses) {
      LiftDbLocation location;
      if (FromJSON(entry, location)) {
        instruction.uses.push_back(std::move(location));
      }
    }
  }
  if (auto *defs = obj->getArray("defs")) {
    instruction.defs.clear();
    for (const auto &entry : *defs) {
      LiftDbLocation location;
      if (FromJSON(entry, location)) {
        instruction.defs.push_back(std::move(location));
      }
    }
  }
  if (auto *accesses = obj->getArray("stack_accesses")) {
    instruction.stack_accesses.clear();
    for (const auto &entry : *accesses) {
      LiftDbStackAccessRecord access;
      if (FromJSON(entry, access)) {
        instruction.stack_accesses.push_back(std::move(access));
      }
    }
  }
  if (auto *bridge_val = obj->get("call_target_bridge")) {
    LiftDbCallTargetBridge bridge;
    if (FromJSON(*bridge_val, bridge)) {
      instruction.call_target_bridge = std::move(bridge);
    }
  }
  return true;
}

static Value ToJSON(const LiftDbEdgeRecord &edge) {
  Object obj;
  obj["kind"] = ToString(edge.kind);
  obj["source_block_va"] = HexU64(edge.source_block_va);
  obj["target_block_va"] = HexU64(edge.target_block_va);
  obj["from_overlay"] = edge.from_overlay;
  return obj;
}

static bool FromJSON(const Value &value, LiftDbEdgeRecord &edge) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto text = obj->getString("kind")) {
    edge.kind = ParseEdgeKind(*text);
  }
  if (auto *source = obj->get("source_block_va")) {
    ParseU64(*source, edge.source_block_va);
  }
  if (auto *target = obj->get("target_block_va")) {
    ParseU64(*target, edge.target_block_va);
  }
  if (auto boolean = obj->getBoolean("from_overlay")) {
    edge.from_overlay = *boolean;
  }
  return true;
}

static Value ToJSON(const LiftDbBasicBlockRecord &block) {
  Object obj;
  obj["entry_va"] = HexU64(block.entry_va);
  obj["function_entry_va"] = HexU64(block.function_entry_va);
  obj["from_overlay_split"] = block.from_overlay_split;
  obj["instruction_vas"] = ToHexArray(block.instruction_vas);
  obj["successors"] =
      ToJSONArray(block.successors, [](const LiftDbEdgeRecord &edge) {
        return ToJSON(edge);
      });
  obj["predecessors"] = ToHexArray(block.predecessors);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbBasicBlockRecord &block) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto *entry = obj->get("entry_va")) {
    ParseU64(*entry, block.entry_va);
  }
  if (auto *entry = obj->get("function_entry_va")) {
    ParseU64(*entry, block.function_entry_va);
  }
  if (auto boolean = obj->getBoolean("from_overlay_split")) {
    block.from_overlay_split = *boolean;
  }
  if (auto *instruction_vas = obj->getArray("instruction_vas")) {
    block.instruction_vas.clear();
    for (const auto &entry : *instruction_vas) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        block.instruction_vas.push_back(va);
      }
    }
  }
  if (auto *successors = obj->getArray("successors")) {
    block.successors.clear();
    for (const auto &entry : *successors) {
      LiftDbEdgeRecord edge;
      if (FromJSON(entry, edge)) {
        block.successors.push_back(std::move(edge));
      }
    }
  }
  if (auto *predecessors = obj->getArray("predecessors")) {
    block.predecessors.clear();
    for (const auto &entry : *predecessors) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        block.predecessors.push_back(va);
      }
    }
  }
  return true;
}

static Value ToJSON(const LiftDbLoopRecord &loop) {
  Object obj;
  obj["header_va"] = HexU64(loop.header_va);
  obj["irreducible"] = loop.irreducible;
  obj["latch_vas"] = ToHexArray(loop.latch_vas);
  obj["body_block_vas"] = ToHexArray(loop.body_block_vas);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbLoopRecord &loop) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto *entry = obj->get("header_va")) {
    ParseU64(*entry, loop.header_va);
  }
  if (auto boolean = obj->getBoolean("irreducible")) {
    loop.irreducible = *boolean;
  }
  if (auto *latches = obj->getArray("latch_vas")) {
    loop.latch_vas.clear();
    for (const auto &entry : *latches) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        loop.latch_vas.push_back(va);
      }
    }
  }
  if (auto *body = obj->getArray("body_block_vas")) {
    loop.body_block_vas.clear();
    for (const auto &entry : *body) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        loop.body_block_vas.push_back(va);
      }
    }
  }
  return true;
}

static Value ToJSON(const LiftDbUseDefChainRecord &chain) {
  Object obj;
  obj["location"] = ToJSON(chain.location);
  obj["defining_instruction_va"] = HexU64(chain.defining_instruction_va);
  obj["using_instruction_vas"] = ToHexArray(chain.using_instruction_vas);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbUseDefChainRecord &chain) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto *location = obj->get("location")) {
    FromJSON(*location, chain.location);
  }
  if (auto *defining = obj->get("defining_instruction_va")) {
    ParseU64(*defining, chain.defining_instruction_va);
  }
  if (auto *uses = obj->getArray("using_instruction_vas")) {
    chain.using_instruction_vas.clear();
    for (const auto &entry : *uses) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        chain.using_instruction_vas.push_back(va);
      }
    }
  }
  return true;
}

static Value ToJSON(const LiftDbFunctionRecord &function) {
  Object obj;
  obj["entry_va"] = HexU64(function.entry_va);
  obj["discovered_from_overlay"] = function.discovered_from_overlay;
  obj["block_entries"] = ToHexArray(function.block_entries);
  obj["loops"] = ToJSONArray(function.loops, [](const LiftDbLoopRecord &loop) {
    return ToJSON(loop);
  });
  obj["use_def_chains"] =
      ToJSONArray(function.use_def_chains,
                  [](const LiftDbUseDefChainRecord &chain) {
                    return ToJSON(chain);
                  });
  obj["unresolved_branch_vas"] = ToHexArray(function.unresolved_branch_vas);
  obj["dynamic_stack_barrier_vas"] =
      ToHexArray(function.dynamic_stack_barrier_vas);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbFunctionRecord &function) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto *entry = obj->get("entry_va")) {
    ParseU64(*entry, function.entry_va);
  }
  if (auto boolean = obj->getBoolean("discovered_from_overlay")) {
    function.discovered_from_overlay = *boolean;
  }
  if (auto *entries = obj->getArray("block_entries")) {
    function.block_entries.clear();
    for (const auto &entry : *entries) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        function.block_entries.push_back(va);
      }
    }
  }
  if (auto *loops = obj->getArray("loops")) {
    function.loops.clear();
    for (const auto &entry : *loops) {
      LiftDbLoopRecord loop;
      if (FromJSON(entry, loop)) {
        function.loops.push_back(std::move(loop));
      }
    }
  }
  if (auto *chains = obj->getArray("use_def_chains")) {
    function.use_def_chains.clear();
    for (const auto &entry : *chains) {
      LiftDbUseDefChainRecord chain;
      if (FromJSON(entry, chain)) {
        function.use_def_chains.push_back(std::move(chain));
      }
    }
  }
  if (auto *entries = obj->getArray("unresolved_branch_vas")) {
    function.unresolved_branch_vas.clear();
    for (const auto &entry : *entries) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        function.unresolved_branch_vas.push_back(va);
      }
    }
  }
  if (auto *entries = obj->getArray("dynamic_stack_barrier_vas")) {
    function.dynamic_stack_barrier_vas.clear();
    for (const auto &entry : *entries) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        function.dynamic_stack_barrier_vas.push_back(va);
      }
    }
  }
  return true;
}

static Value ToJSON(const LiftDbTraceOverlayRecord &overlay) {
  Object obj;
  obj["overlay_key"] = overlay.overlay_key;
  obj["handler_va"] = HexU64(overlay.handler_va);
  obj["incoming_hash"] = HexU64(overlay.incoming_hash);
  obj["function_entry_va"] = HexU64(overlay.function_entry_va);
  obj["path_block_entries"] = ToHexArray(overlay.path_block_entries);
  obj["constrained_edges"] =
      ToJSONArray(overlay.constrained_edges, [](const LiftDbEdgeRecord &edge) {
        return ToJSON(edge);
      });
  obj["native_exit_vas"] = ToHexArray(overlay.native_exit_vas);
  obj["cloned_block_entries"] = ToHexArray(overlay.cloned_block_entries);
  return obj;
}

static bool FromJSON(const Value &value, LiftDbTraceOverlayRecord &overlay) {
  auto *obj = value.getAsObject();
  if (!obj) {
    return false;
  }

  if (auto text = obj->getString("overlay_key")) {
    overlay.overlay_key = text->str();
  }
  if (auto *entry = obj->get("handler_va")) {
    ParseU64(*entry, overlay.handler_va);
  }
  if (auto *entry = obj->get("incoming_hash")) {
    ParseU64(*entry, overlay.incoming_hash);
  }
  if (auto *entry = obj->get("function_entry_va")) {
    ParseU64(*entry, overlay.function_entry_va);
  }
  if (auto *entries = obj->getArray("path_block_entries")) {
    overlay.path_block_entries.clear();
    for (const auto &entry : *entries) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        overlay.path_block_entries.push_back(va);
      }
    }
  }
  if (auto *edges = obj->getArray("constrained_edges")) {
    overlay.constrained_edges.clear();
    for (const auto &entry : *edges) {
      LiftDbEdgeRecord edge;
      if (FromJSON(entry, edge)) {
        overlay.constrained_edges.push_back(std::move(edge));
      }
    }
  }
  if (auto *entries = obj->getArray("native_exit_vas")) {
    overlay.native_exit_vas.clear();
    for (const auto &entry : *entries) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        overlay.native_exit_vas.push_back(va);
      }
    }
  }
  if (auto *entries = obj->getArray("cloned_block_entries")) {
    overlay.cloned_block_entries.clear();
    for (const auto &entry : *entries) {
      uint64_t va = 0;
      if (ParseU64(entry, va)) {
        overlay.cloned_block_entries.push_back(va);
      }
    }
  }
  return true;
}

static bool WriteJSONFile(llvm::StringRef path, const Value &value,
                          std::string *error) {
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec, llvm::sys::fs::OF_Text);
  if (ec) {
    if (error) {
      *error = ec.message();
    }
    return false;
  }
  os << value;
  os << "\n";
  return true;
}

static std::optional<Value> ReadJSONFile(llvm::StringRef path,
                                         std::string *error) {
  auto buffer = llvm::MemoryBuffer::getFile(path);
  if (!buffer) {
    if (error) {
      *error = buffer.getError().message();
    }
    return std::nullopt;
  }

  auto parsed = llvm::json::parse(buffer.get()->getBuffer());
  if (!parsed) {
    if (error) {
      *error = llvm::toString(parsed.takeError());
    }
    return std::nullopt;
  }
  return std::move(*parsed);
}

static std::string FunctionChunkName(uint64_t entry_va) {
  return "functions/fn_" + llvm::utohexstr(entry_va) + ".json";
}

}  // namespace

bool SaveLiftDatabaseToDirectory(const LiftDatabase &db,
                                 llvm::StringRef directory,
                                 std::string *error) {
  std::filesystem::path root(directory.str());
  std::filesystem::create_directories(root);
  std::filesystem::create_directories(root / "functions");

  Array function_chunks;
  for (const auto &[entry_va, function] : db.functions()) {
    Object chunk;
    chunk["function"] = ToJSON(function);

    Array blocks;
    Array instructions;
    for (auto block_entry_va : function.block_entries) {
      auto block_it = db.blocks().find(block_entry_va);
      if (block_it == db.blocks().end()) {
        continue;
      }
      blocks.emplace_back(ToJSON(block_it->second));
      for (auto instruction_va : block_it->second.instruction_vas) {
        auto inst_it = db.instructions().find(instruction_va);
        if (inst_it == db.instructions().end()) {
          continue;
        }
        instructions.emplace_back(ToJSON(inst_it->second));
      }
    }
    chunk["blocks"] = std::move(blocks);
    chunk["instructions"] = std::move(instructions);

    const auto relative_name = FunctionChunkName(entry_va);
    const auto absolute_name = (root / relative_name).string();
    if (!WriteJSONFile(absolute_name, Value(std::move(chunk)), error)) {
      return false;
    }
    function_chunks.emplace_back(relative_name);
  }

  Array overlays;
  for (const auto &[_, overlay] : db.traceOverlays()) {
    overlays.emplace_back(ToJSON(overlay));
  }
  if (!WriteJSONFile((root / "overlays.json").string(),
                     Value(std::move(overlays)), error)) {
    return false;
  }

  Object manifest;
  manifest["format_version"] = db.manifest().format_version;
  manifest["image_path"] = db.manifest().image_path;
  manifest["image_id"] = db.manifest().image_id;
  manifest["os_name"] = db.manifest().os_name;
  manifest["abi_name"] = db.manifest().abi_name;
  manifest["arch"] = ToString(db.manifest().arch);
  manifest["image_base"] = HexU64(db.manifest().image_base);
  manifest["image_size"] = HexU64(db.manifest().image_size);
  manifest["db_revision"] = HexU64(db.manifest().db_revision);
  manifest["function_chunks"] = std::move(function_chunks);
  manifest["overlays_path"] = "overlays.json";
  return WriteJSONFile((root / "manifest.json").string(),
                       Value(std::move(manifest)), error);
}

std::optional<LiftDatabase> LoadLiftDatabaseFromDirectory(
    llvm::StringRef directory, std::string *error) {
  LiftDatabase db;
  const std::filesystem::path root(directory.str());

  auto manifest_value = ReadJSONFile((root / "manifest.json").string(), error);
  if (!manifest_value) {
    return std::nullopt;
  }

  auto *manifest = manifest_value->getAsObject();
  if (!manifest) {
    if (error) {
      *error = "lift database manifest is not a JSON object";
    }
    return std::nullopt;
  }

  if (auto text = manifest->getString("format_version")) {
    db.manifest().format_version = text->str();
  }
  if (auto text = manifest->getString("image_path")) {
    db.manifest().image_path = text->str();
  }
  if (auto text = manifest->getString("image_id")) {
    db.manifest().image_id = text->str();
  }
  if (auto text = manifest->getString("os_name")) {
    db.manifest().os_name = text->str();
  }
  if (auto text = manifest->getString("abi_name")) {
    db.manifest().abi_name = text->str();
  }
  if (auto text = manifest->getString("arch")) {
    db.manifest().arch = ParseArch(*text);
  }
  if (auto *value = manifest->get("image_base")) {
    ParseU64(*value, db.manifest().image_base);
  }
  if (auto *value = manifest->get("image_size")) {
    ParseU64(*value, db.manifest().image_size);
  }
  if (auto *value = manifest->get("db_revision")) {
    ParseU64(*value, db.manifest().db_revision);
  }

  if (auto *chunks = manifest->getArray("function_chunks")) {
    for (const auto &entry : *chunks) {
      auto path = entry.getAsString();
      if (!path) {
        continue;
      }

      auto function_value = ReadJSONFile((root / path->str()).string(), error);
      if (!function_value) {
        return std::nullopt;
      }

      auto *function_object = function_value->getAsObject();
      if (!function_object) {
        if (error) {
          *error = "function chunk is not a JSON object";
        }
        return std::nullopt;
      }

      LiftDbFunctionRecord function;
      if (auto *value = function_object->get("function")) {
        FromJSON(*value, function);
      }
      auto &stored_function = db.upsertFunction(function.entry_va);
      stored_function = std::move(function);

      if (auto *blocks = function_object->getArray("blocks")) {
        for (const auto &block_value : *blocks) {
          LiftDbBasicBlockRecord block;
          if (!FromJSON(block_value, block)) {
            continue;
          }
          auto &stored_block =
              db.upsertBlock(block.function_entry_va, block.entry_va);
          stored_block = std::move(block);
        }
      }

      if (auto *instructions = function_object->getArray("instructions")) {
        for (const auto &instruction_value : *instructions) {
          LiftDbInstructionRecord instruction;
          if (!FromJSON(instruction_value, instruction)) {
            continue;
          }
          auto &stored_instruction = db.upsertInstruction(instruction.va);
          stored_instruction = std::move(instruction);
        }
      }
    }
  }

  std::string overlays_path = "overlays.json";
  if (auto text = manifest->getString("overlays_path")) {
    overlays_path = text->str();
  }

  if (std::filesystem::exists(root / overlays_path)) {
    auto overlays_value = ReadJSONFile((root / overlays_path).string(), error);
    if (!overlays_value) {
      return std::nullopt;
    }
    if (auto *overlays = overlays_value->getAsArray()) {
      for (const auto &overlay_value : *overlays) {
        LiftDbTraceOverlayRecord overlay;
        if (!FromJSON(overlay_value, overlay)) {
          continue;
        }
        auto &stored_overlay = db.upsertTraceOverlay(overlay.overlay_key);
        stored_overlay = std::move(overlay);
      }
    }
  }

  for (const auto &[entry_va, _] : db.functions()) {
    db.rebuildPredecessors(entry_va);
  }

  return db;
}

}  // namespace omill

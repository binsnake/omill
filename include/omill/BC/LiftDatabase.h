#pragma once

#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace omill {

enum class LiftDbArch : uint8_t {
  kUnknown = 0,
  kX64 = 1,
};

enum class LiftDbLocationKind : uint8_t {
  kUnknown = 0,
  kRegister,
  kFlag,
  kStackCell,
  kMemory,
  kTemporary,
  kRipRelative,
  kSynthetic,
};

enum class LiftDbCategory : uint8_t {
  kUnknown = 0,
  kNormal,
  kDirectJump,
  kIndirectJump,
  kConditionalBranch,
  kDirectCall,
  kIndirectCall,
  kReturn,
};

enum class LiftDbStackAccessKind : uint8_t {
  kUnknown = 0,
  kRead,
  kWrite,
  kReadWrite,
  kReturnAddress,
  kShadowSpace,
  kBarrier,
};

enum class LiftDbEdgeKind : uint8_t {
  kUnknown = 0,
  kFallthrough,
  kBranchTaken,
  kCall,
  kReturn,
  kUnresolved,
  kOverlay,
};

struct LiftDbManifest {
  std::string format_version = "1";
  std::string image_path;
  std::string image_id;
  std::string os_name;
  std::string abi_name;
  LiftDbArch arch = LiftDbArch::kUnknown;
  uint64_t image_base = 0;
  uint64_t image_size = 0;
  uint64_t db_revision = 0;
};

struct LiftDbLocation {
  LiftDbLocationKind kind = LiftDbLocationKind::kUnknown;
  std::string name;
  std::string base_register;
  int64_t offset = 0;
  uint32_t size_bits = 0;
  uint32_t version = 0;
  bool precise = false;
};

struct LiftDbOperandRecord {
  std::string text;
  uint32_t size_bits = 0;
  std::vector<LiftDbLocation> reads;
  std::vector<LiftDbLocation> writes;
};

struct LiftDbStackAccessRecord {
  LiftDbStackAccessKind kind = LiftDbStackAccessKind::kUnknown;
  int64_t offset = 0;
  uint32_t size = 0;
  bool exact = false;
  std::string location_name;
};

/// Per-instruction descriptor for a deterministic call-target bridge that
/// StaticLiftBuilder resolved via symbolic probing of the direct-call
/// target's prologue.  BlockLifter uses this to emit the stack effect
/// inline at the call site, avoiding an `omill_native_boundary_<pc>`
/// placeholder for the thunk target.
struct LiftDbBridgeStackWrite {
  int64_t rsp_offset = 0;
  uint32_t size_bytes = 0;
  uint64_t value = 0;
};

struct LiftDbCallTargetBridge {
  std::vector<LiftDbBridgeStackWrite> stack_writes;
  int64_t net_rsp_delta = 0;
  uint64_t final_jump_target_pc = 0;
  /// 0 = kJmpConst, 1 = kRet.
  uint8_t terminator = 0;
  uint32_t instructions_modeled = 0;
};

struct LiftDbInstructionRecord {
  uint64_t va = 0;
  uint64_t function_entry_va = 0;
  uint64_t block_entry_va = 0;
  std::string bytes_hex;
  std::string mnemonic;
  LiftDbCategory category = LiftDbCategory::kUnknown;
  uint32_t size = 0;
  int64_t stack_pointer_delta = 0;
  bool has_fallthrough = false;
  uint64_t fallthrough_va = 0;
  bool has_branch_target = false;
  uint64_t branch_target_va = 0;
  bool dynamic_stack_barrier = false;
  std::vector<LiftDbOperandRecord> operands;
  std::vector<LiftDbLocation> uses;
  std::vector<LiftDbLocation> defs;
  std::vector<LiftDbStackAccessRecord> stack_accesses;
  std::optional<LiftDbCallTargetBridge> call_target_bridge;
};

struct LiftDbEdgeRecord {
  LiftDbEdgeKind kind = LiftDbEdgeKind::kUnknown;
  uint64_t source_block_va = 0;
  uint64_t target_block_va = 0;
  bool from_overlay = false;
};

struct LiftDbBasicBlockRecord {
  uint64_t entry_va = 0;
  uint64_t function_entry_va = 0;
  bool from_overlay_split = false;
  std::vector<uint64_t> instruction_vas;
  std::vector<LiftDbEdgeRecord> successors;
  std::vector<uint64_t> predecessors;
};

struct LiftDbLoopRecord {
  uint64_t header_va = 0;
  bool irreducible = false;
  std::vector<uint64_t> latch_vas;
  std::vector<uint64_t> body_block_vas;
};

struct LiftDbUseDefChainRecord {
  LiftDbLocation location;
  uint64_t defining_instruction_va = 0;
  std::vector<uint64_t> using_instruction_vas;
};

struct LiftDbFunctionRecord {
  uint64_t entry_va = 0;
  bool discovered_from_overlay = false;
  std::vector<uint64_t> block_entries;
  std::vector<LiftDbLoopRecord> loops;
  std::vector<LiftDbUseDefChainRecord> use_def_chains;
  std::vector<uint64_t> unresolved_branch_vas;
  std::vector<uint64_t> dynamic_stack_barrier_vas;
};

struct LiftDbTraceOverlayRecord {
  std::string overlay_key;
  uint64_t handler_va = 0;
  uint64_t incoming_hash = 0;
  uint64_t function_entry_va = 0;
  std::vector<uint64_t> path_block_entries;
  std::vector<LiftDbEdgeRecord> constrained_edges;
  std::vector<uint64_t> native_exit_vas;
  std::vector<uint64_t> cloned_block_entries;
};

class LiftDatabase {
 public:
  LiftDbManifest &manifest(void);
  const LiftDbManifest &manifest(void) const;

  LiftDbFunctionRecord &upsertFunction(uint64_t entry_va);
  LiftDbBasicBlockRecord &upsertBlock(uint64_t function_entry_va,
                                      uint64_t block_entry_va);
  LiftDbInstructionRecord &upsertInstruction(uint64_t va);
  LiftDbTraceOverlayRecord &upsertTraceOverlay(const std::string &overlay_key);

  LiftDbFunctionRecord *function(uint64_t entry_va);
  const LiftDbFunctionRecord *function(uint64_t entry_va) const;

  LiftDbBasicBlockRecord *block(uint64_t entry_va);
  const LiftDbBasicBlockRecord *block(uint64_t entry_va) const;

  LiftDbInstructionRecord *instruction(uint64_t va);
  const LiftDbInstructionRecord *instruction(uint64_t va) const;

  LiftDbTraceOverlayRecord *traceOverlay(const std::string &overlay_key);
  const LiftDbTraceOverlayRecord *traceOverlay(
      const std::string &overlay_key) const;

  const std::map<uint64_t, LiftDbFunctionRecord> &functions(void) const;
  const std::map<uint64_t, LiftDbBasicBlockRecord> &blocks(void) const;
  const std::map<uint64_t, LiftDbInstructionRecord> &instructions(void) const;
  const std::map<std::string, LiftDbTraceOverlayRecord> &traceOverlays(
      void) const;

  void clearFunction(uint64_t entry_va);
  void rebuildPredecessors(uint64_t function_entry_va);
  void bumpRevision(void);

 private:
  LiftDbManifest manifest_;
  std::map<uint64_t, LiftDbFunctionRecord> functions_;
  std::map<uint64_t, LiftDbBasicBlockRecord> blocks_;
  std::map<uint64_t, LiftDbInstructionRecord> instructions_;
  std::map<std::string, LiftDbTraceOverlayRecord> trace_overlays_;
};

std::string LiftDbOverlayKey(uint64_t handler_va, uint64_t incoming_hash);

}  // namespace omill

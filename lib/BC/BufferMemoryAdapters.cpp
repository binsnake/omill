#include "omill/BC/BufferMemoryAdapters.h"

#include "omill/Support/JumpTableDiscovery.h"

#include <remill/Arch/Arch.h>
#include <remill/Arch/Instruction.h>
#include <remill/BC/Util.h>

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>

namespace omill {

namespace {

std::vector<uint64_t> discoverJumpTableTargets(
    const BinaryMemoryMap *memory_map, TargetArch target_arch,
    const remill::Instruction &inst) {
  if (!memory_map || target_arch != TargetArch::kX86_64)
    return {};
  return discoverJumpTableTargetsForInstruction(*memory_map, inst.pc);
}

}  // namespace

// ---------------------------------------------------------------------------
// BufferTraceManager
// ---------------------------------------------------------------------------

void BufferTraceManager::setCode(const uint8_t *data, size_t size,
                                  uint64_t base) {
  code_[base] = {data, data + size};
  base_addr_ = base;
}

void BufferTraceManager::setBaseAddr(uint64_t addr) { base_addr_ = addr; }
uint64_t BufferTraceManager::baseAddr() const { return base_addr_; }

void BufferTraceManager::setBinaryMemoryMap(const BinaryMemoryMap *m) {
  memory_map_ = m;
}

void BufferTraceManager::setTargetArch(TargetArch arch) {
  target_arch_ = arch;
}

void BufferTraceManager::setModuleAndArch(llvm::Module *m,
                                           const remill::Arch *a) {
  module_ = m;
  arch_ = a;
}

void BufferTraceManager::setMaxLiftCount(unsigned n) { max_lift_count_ = n; }
void BufferTraceManager::resetLiftCount() { lift_count_ = 0; }

void BufferTraceManager::SetLiftedTraceDefinition(uint64_t addr,
                                                   llvm::Function *func) {
  lifted_[addr] = func;
  ++lift_count_;
}

llvm::Function *BufferTraceManager::GetLiftedTraceDeclaration(uint64_t addr) {
  auto it = lifted_.find(addr);
  if (it == lifted_.end())
    return nullptr;
  auto *func = llvm::dyn_cast_or_null<llvm::Function>(it->second);
  if (!func)
    lifted_.erase(it);
  return func;
}

llvm::Function *BufferTraceManager::GetLiftedTraceDefinition(uint64_t addr) {
  if (max_lift_count_ > 0 && lift_count_ >= max_lift_count_) {
    auto it = lifted_.find(addr);
    if (it != lifted_.end()) {
      auto *func = llvm::dyn_cast_or_null<llvm::Function>(it->second);
      if (!func)
        lifted_.erase(it);
      else
        return func;
    }
    auto *decl = arch_->DeclareLiftedFunction(TraceName(addr), module_);
    lifted_[addr] = decl;
    return decl;
  }
  return GetLiftedTraceDeclaration(addr);
}

bool BufferTraceManager::TryReadExecutableByte(uint64_t addr, uint8_t *out) {
  for (auto &[base, data] : code_) {
    if (addr >= base && addr < base + data.size()) {
      *out = data[addr - base];
      return true;
    }
  }
  return false;
}

void BufferTraceManager::ForEachDevirtualizedTarget(
    const remill::Instruction &inst,
    std::function<void(uint64_t, DevirtualizedTargetKind)> func) {
  for (uint64_t target :
       discoverJumpTableTargets(memory_map_, target_arch_, inst)) {
    auto decision = getLiftTargetPolicy()->ResolveLiftTarget(
        inst.pc, target, LiftTargetEdgeKind::kIndirectTarget);
    if (decision.shouldLift() && decision.effective_target_pc)
      func(*decision.effective_target_pc, DevirtualizedTargetKind::kTraceLocal);
  }
}

LiftTargetDecision BufferTraceManager::ResolveLiftTarget(
    uint64_t source_pc, uint64_t raw_target_pc, LiftTargetEdgeKind edge_kind) {
  return getLiftTargetPolicy()->ResolveLiftTarget(source_pc, raw_target_pc,
                                                  edge_kind);
}

DecodeFailureDecision BufferTraceManager::ResolveDecodeFailure(
    uint64_t source_addr, uint64_t failed_pc,
    const DecodeFailureContext &ctx) {
  llvm::SmallVector<uint64_t, 16> known_entries;
  known_entries.reserve(lifted_.size());
  for (const auto &[pc, vh] : lifted_) {
    (void)vh;
    known_entries.push_back(pc);
  }
  return getLiftTargetPolicy()->ResolveDecodeFailure(source_addr, failed_pc,
                                                     known_entries, ctx);
}

LiftTargetPolicy *BufferTraceManager::getLiftTargetPolicy() {
  if (!lift_target_policy_ ||
      lift_target_policy_memory_map_ != memory_map_ ||
      lift_target_policy_arch_ != target_arch_) {
    lift_target_policy_ =
        createBinaryLiftTargetPolicy(memory_map_, target_arch_);
    lift_target_policy_memory_map_ = memory_map_;
    lift_target_policy_arch_ = target_arch_;
  }
  return lift_target_policy_.get();
}

// ---------------------------------------------------------------------------
// BufferBlockManager
// ---------------------------------------------------------------------------

void BufferBlockManager::setModule(llvm::Module *module) { module_ = module; }

void BufferBlockManager::setBinaryMemoryMap(const BinaryMemoryMap *m) {
  memory_map_ = m;
}

void BufferBlockManager::setTargetArch(TargetArch arch) { target_arch_ = arch; }

void BufferBlockManager::setCode(const uint8_t *data, size_t size,
                                  uint64_t base) {
  code_[base] = {data, data + size};
}

void BufferBlockManager::addCode(uint64_t base, const uint8_t *data,
                                  size_t size) {
  code_[base].assign(data, data + size);
}

void BufferBlockManager::SetLiftedBlockDefinition(uint64_t addr,
                                                   llvm::Function *fn) {
  blocks_[addr] = fn;
}

llvm::Function *BufferBlockManager::GetLiftedBlockDeclaration(uint64_t addr) {
  auto it = blocks_.find(addr);
  return (it != blocks_.end()) ? it->second : nullptr;
}

llvm::Function *BufferBlockManager::GetLiftedBlockDefinition(uint64_t addr) {
  return GetLiftedBlockDeclaration(addr);
}

bool BufferBlockManager::TryReadExecutableByte(uint64_t addr, uint8_t *out) {
  for (auto &[base, data] : code_) {
    if (addr >= base && addr < base + data.size()) {
      *out = data[addr - base];
      return true;
    }
  }
  return false;
}

void BufferBlockManager::ForEachDevirtualizedTarget(
    const remill::Instruction &inst,
    std::function<void(uint64_t, DevirtualizedTargetKind)> func) {
  for (uint64_t target :
       discoverJumpTableTargets(memory_map_, target_arch_, inst)) {
    auto decision = getLiftTargetPolicy()->ResolveLiftTarget(
        inst.pc, target, LiftTargetEdgeKind::kIndirectTarget);
    if (decision.shouldLift() && decision.effective_target_pc)
      func(*decision.effective_target_pc, DevirtualizedTargetKind::kTraceLocal);
  }
}

LiftTargetDecision BufferBlockManager::ResolveLiftTarget(
    uint64_t source_pc, uint64_t raw_target_pc, LiftTargetEdgeKind edge_kind) {
  return getLiftTargetPolicy()->ResolveLiftTarget(source_pc, raw_target_pc,
                                                  edge_kind);
}

DecodeFailureDecision BufferBlockManager::ResolveDecodeFailure(
    uint64_t source_addr, uint64_t failed_pc,
    const DecodeFailureContext &ctx) {
  llvm::SmallVector<uint64_t, 16> known_entries;
  known_entries.reserve(blocks_.size());
  for (const auto &[pc, fn] : blocks_) {
    (void)fn;
    known_entries.push_back(pc);
  }
  return getLiftTargetPolicy()->ResolveDecodeFailure(source_addr, failed_pc,
                                                     known_entries, ctx);
}

llvm::Module *BufferBlockManager::GetLiftedBlockModule() { return module_; }

const BinaryMemoryMap *BufferBlockManager::GetBinaryMemoryMap() const {
  return memory_map_;
}

LiftTargetPolicy *BufferBlockManager::getLiftTargetPolicy() {
  if (!lift_target_policy_ ||
      lift_target_policy_memory_map_ != memory_map_ ||
      lift_target_policy_arch_ != target_arch_) {
    lift_target_policy_ =
        createBinaryLiftTargetPolicy(memory_map_, target_arch_);
    lift_target_policy_memory_map_ = memory_map_;
    lift_target_policy_arch_ = target_arch_;
  }
  return lift_target_policy_.get();
}

}  // namespace omill

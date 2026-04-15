#pragma once

#include "omill/BC/BlockLifter.h"
#include "omill/BC/LiftTargetPolicy.h"
#include "omill/BC/TraceLifter.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/TargetArchAnalysis.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/ValueHandle.h>

#include <map>
#include <memory>
#include <vector>

namespace remill {
class Arch;
class Instruction;
}  // namespace remill

namespace omill {

/// In-memory TraceManager for remill lifting backed by a raw PE memory map.
///
/// Supports shallow-lift mode: once max_lift_count traces have been lifted,
/// further GetLiftedTraceDefinition() calls return a declaration instead of
/// triggering a new lift, preventing unbounded recursive lifting of the call
/// graph during late target discovery.
class BufferTraceManager : public TraceManager {
 public:
  void setCode(const uint8_t *data, size_t size, uint64_t base);
  void setBaseAddr(uint64_t addr);
  uint64_t baseAddr() const;
  void setBinaryMemoryMap(const BinaryMemoryMap *memory_map);
  void setTargetArch(TargetArch arch);

  /// Must be called after the module and arch are created so that
  /// shallow-lift mode can create proper function declarations.
  void setModuleAndArch(llvm::Module *m, const remill::Arch *a);

  /// Set maximum number of traces to lift per Lift() call.  0 = unlimited.
  void setMaxLiftCount(unsigned n);
  void resetLiftCount();

  void SetLiftedTraceDefinition(uint64_t addr, llvm::Function *func) override;
  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr) override;
  llvm::Function *GetLiftedTraceDefinition(uint64_t addr) override;
  bool TryReadExecutableByte(uint64_t addr, uint8_t *out) override;

  void ForEachDevirtualizedTarget(
      const remill::Instruction &inst,
      std::function<void(uint64_t, DevirtualizedTargetKind)> func) override;

  LiftTargetDecision ResolveLiftTarget(uint64_t source_pc,
                                       uint64_t raw_target_pc,
                                       LiftTargetEdgeKind edge_kind) override;

  DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_addr, uint64_t failed_pc,
      const DecodeFailureContext &ctx) override;

 private:
  LiftTargetPolicy *getLiftTargetPolicy();

  std::map<uint64_t, std::vector<uint8_t>> code_;
  std::map<uint64_t, llvm::WeakTrackingVH> lifted_;
  uint64_t base_addr_ = 0;
  unsigned max_lift_count_ = 0;
  unsigned lift_count_ = 0;
  llvm::Module *module_ = nullptr;
  const remill::Arch *arch_ = nullptr;
  const BinaryMemoryMap *memory_map_ = nullptr;
  TargetArch target_arch_ = TargetArch::kX86_64;
  std::unique_ptr<LiftTargetPolicy> lift_target_policy_;
  const BinaryMemoryMap *lift_target_policy_memory_map_ = nullptr;
  TargetArch lift_target_policy_arch_ = TargetArch::kX86_64;
};

/// In-memory BlockManager for block-lifting mode backed by a raw PE memory
/// map.
class BufferBlockManager : public BlockManager {
 public:
  void setModule(llvm::Module *module);
  void setBinaryMemoryMap(const BinaryMemoryMap *memory_map);
  void setTargetArch(TargetArch arch);
  void setCode(const uint8_t *data, size_t size, uint64_t base);

  void addCode(uint64_t base, const uint8_t *data, size_t size) override;

  void SetLiftedBlockDefinition(uint64_t addr, llvm::Function *fn) override;
  llvm::Function *GetLiftedBlockDeclaration(uint64_t addr) override;
  llvm::Function *GetLiftedBlockDefinition(uint64_t addr) override;
  bool TryReadExecutableByte(uint64_t addr, uint8_t *out) override;

  void ForEachDevirtualizedTarget(
      const remill::Instruction &inst,
      std::function<void(uint64_t, DevirtualizedTargetKind)> func) override;

  LiftTargetDecision ResolveLiftTarget(uint64_t source_pc,
                                       uint64_t raw_target_pc,
                                       LiftTargetEdgeKind edge_kind) override;

  DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_addr, uint64_t failed_pc,
      const DecodeFailureContext &ctx) override;

  llvm::Module *GetLiftedBlockModule() override;
  const BinaryMemoryMap *GetBinaryMemoryMap() const override;

 private:
  LiftTargetPolicy *getLiftTargetPolicy();

  std::map<uint64_t, std::vector<uint8_t>> code_;
  std::map<uint64_t, llvm::Function *> blocks_;
  llvm::Module *module_ = nullptr;
  const BinaryMemoryMap *memory_map_ = nullptr;
  TargetArch target_arch_ = TargetArch::kX86_64;
  std::unique_ptr<LiftTargetPolicy> lift_target_policy_;
  const BinaryMemoryMap *lift_target_policy_memory_map_ = nullptr;
  TargetArch lift_target_policy_arch_ = TargetArch::kX86_64;
};

}  // namespace omill

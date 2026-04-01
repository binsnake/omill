#pragma once

#include <llvm/ADT/ArrayRef.h>

#include <cstdint>
#include <memory>
#include <optional>

namespace omill {

class BinaryMemoryMap;
enum class TargetArch;

enum class LiftTargetEdgeKind {
  kDirectJump,
  kConditionalTaken,
  kConditionalNotTaken,
  kCallFallthrough,
  kDirectCallTarget,
  kIndirectTarget,
  kTraceHead,
  kTraceNext,
  kDecodeFailureContinuation,
};

enum class LiftTargetClassification {
  kLiftableEntry,
  kExactFallthroughEntry,
  kInvalidatedExecutableEntry,
  kExecutablePlaceholder,
  kCanonicalOwner,
  kSuppress,
  kTerminal,
};

enum class LiftTargetTrust {
  kTrustedEntry,
  kExactFallthrough,
  kNearbyOwner,
  kInvalidatedEntry,
  kUntrustedExecutable,
  kSuppressed,
  kTerminal,
};

struct LiftTargetDecision {
  uint64_t raw_target_pc = 0;
  std::optional<uint64_t> effective_target_pc;
  LiftTargetClassification classification =
      LiftTargetClassification::kTerminal;
  LiftTargetTrust trust = LiftTargetTrust::kTerminal;
  std::optional<uint64_t> owner_pc;
  std::optional<uint64_t> fallback_pc;
  bool is_exact_fallthrough = false;
  std::optional<uint64_t> invalidated_entry_source_pc;
  std::optional<uint64_t> invalidated_entry_failed_pc;

  bool shouldLift() const;
  bool shouldMaterializePlaceholder() const;
};

struct DecodeFailureContext {
  LiftTargetEdgeKind edge_kind =
      LiftTargetEdgeKind::kDecodeFailureContinuation;
};

enum class DecodeFailureAction {
  kKeepPartialAndTerminate,
  kInvalidateEntry,
  kRedirectToTarget,
  kMaterializeExecutablePlaceholder,
  kTerminal,
};

struct DecodeFailureDecision {
  uint64_t source_pc = 0;
  uint64_t failed_pc = 0;
  DecodeFailureAction action = DecodeFailureAction::kTerminal;
  LiftTargetDecision target;
};

class LiftTargetPolicy {
 public:
  virtual ~LiftTargetPolicy();

  virtual LiftTargetDecision ResolveLiftTarget(uint64_t source_pc,
                                               uint64_t raw_target_pc,
                                               LiftTargetEdgeKind edge_kind) const = 0;

  virtual DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_pc, uint64_t failed_pc,
      llvm::ArrayRef<uint64_t> known_entry_pcs,
      const DecodeFailureContext &ctx) const = 0;
};

class BinaryLiftTargetPolicy final : public LiftTargetPolicy {
 public:
  BinaryLiftTargetPolicy(const BinaryMemoryMap *memory_map, TargetArch arch);

  LiftTargetDecision ResolveLiftTarget(uint64_t source_pc,
                                       uint64_t raw_target_pc,
                                       LiftTargetEdgeKind edge_kind) const override;

  DecodeFailureDecision ResolveDecodeFailure(
      uint64_t source_pc, uint64_t failed_pc,
      llvm::ArrayRef<uint64_t> known_entry_pcs,
      const DecodeFailureContext &ctx) const override;

 private:
  const BinaryMemoryMap *memory_map_ = nullptr;
  TargetArch arch_;
};

bool isExecutableLiftTarget(const BinaryMemoryMap *memory_map,
                            uint64_t target_pc);
std::optional<bool> isDecodableLiftTargetEntry(
    const BinaryMemoryMap *memory_map, uint64_t target_pc, TargetArch arch);
bool looksLikeSuspiciousX86EntryBytes(const BinaryMemoryMap *memory_map,
                                      uint64_t target_pc);
bool isLikelyX86CallMetadataWindow(const BinaryMemoryMap *memory_map,
                                   uint64_t target_pc);
bool isExactX86DirectControlFlowFallthrough(const BinaryMemoryMap *memory_map,
                                            uint64_t target_pc);
std::optional<uint64_t> recoverX86DirectControlFlowFallthrough(
    const BinaryMemoryMap *memory_map, uint64_t target_pc);
std::optional<uint64_t> findNearbyExecutableLiftEntry(
    const BinaryMemoryMap *memory_map, uint64_t target_pc, TargetArch arch);
uint64_t decodeFailureContinuationSearchWindow(TargetArch arch);
std::optional<uint64_t> canonicalizeLiftTargetForOverlap(
    const BinaryMemoryMap *memory_map, uint64_t target_pc, TargetArch arch);

std::unique_ptr<LiftTargetPolicy> createBinaryLiftTargetPolicy(
    const BinaryMemoryMap *memory_map, TargetArch arch);

}  // namespace omill

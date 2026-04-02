#pragma once

#include <cstdint>
#include <optional>

#include "omill/Analysis/VirtualModel/Types.h"

namespace llvm {
class CallBase;
class Function;
}  // namespace llvm

namespace omill {

enum class BoundaryKind {
  kUnknown,
  kContinuation,
  kNativeBoundary,
  kVmEnterBoundary,
  kNestedVmEnterBoundary,
  kTerminalBoundary,
};

enum class BoundaryDisposition {
  kUnknown,
  kStayInVm,
  kVmExitTerminal,
  kVmExitNativeCallReenter,
  kVmExitNativeExecUnknownReturn,
  kVmEnter,
  kNestedVmEnter,
};

enum class ContinuationEntryTransformKind {
  kNone,
  kPushImmediateJump,
  kSyntheticReturnToken,
};

struct ContinuationEntryTransform {
  ContinuationEntryTransformKind kind = ContinuationEntryTransformKind::kNone;
  std::optional<uint64_t> entry_pc;
  std::optional<uint64_t> jump_target_pc;
  std::optional<uint64_t> pushed_immediate;
  bool suppresses_normal_fallthrough = false;

  bool operator==(const ContinuationEntryTransform &other) const {
    return kind == other.kind && entry_pc == other.entry_pc &&
           jump_target_pc == other.jump_target_pc &&
           pushed_immediate == other.pushed_immediate &&
           suppresses_normal_fallthrough == other.suppresses_normal_fallthrough;
  }
  bool operator!=(const ContinuationEntryTransform &other) const {
    return !(*this == other);
  }
};

struct BoundaryFact {
  std::optional<uint64_t> boundary_pc;
  std::optional<uint64_t> native_target_pc;
  std::optional<uint64_t> continuation_pc;
  std::optional<uint64_t> continuation_vip_pc;
  std::optional<uint64_t> controlled_return_pc;
  std::optional<unsigned> continuation_slot_id;
  std::optional<unsigned> continuation_stack_cell_id;
  std::optional<unsigned> continuation_owner_id;
  VirtualStackOwnerKind continuation_owner_kind =
      VirtualStackOwnerKind::kUnknown;
  std::optional<uint64_t> covered_entry_pc;
  std::optional<ContinuationEntryTransform> continuation_entry_transform;
  VirtualReturnAddressControlKind return_address_control_kind =
      VirtualReturnAddressControlKind::kUnknown;
  BoundaryKind kind = BoundaryKind::kUnknown;
  BoundaryDisposition exit_disposition = BoundaryDisposition::kUnknown;
  bool is_partial_exit = false;
  bool is_full_exit = false;
  bool reenters_vm = false;
  bool is_vm_enter = false;
  bool is_nested_vm_enter = false;
  bool suppresses_normal_fallthrough = false;

  bool operator==(const BoundaryFact &other) const;
  bool operator!=(const BoundaryFact &other) const {
    return !(*this == other);
  }
};

std::optional<BoundaryFact> readBoundaryFact(const llvm::CallBase &call);
std::optional<BoundaryFact> readBoundaryFact(const llvm::Function &function);

void writeBoundaryFact(llvm::CallBase &call, const BoundaryFact &fact);
void writeBoundaryFact(llvm::Function &function, const BoundaryFact &fact);

BoundaryDisposition boundaryDispositionFromVirtualExitDisposition(
    VirtualExitDisposition disposition);
VirtualExitDisposition virtualExitDispositionFromBoundaryDisposition(
    BoundaryDisposition disposition);

BoundaryFact boundaryFactFromVirtualExitSummary(
    const VirtualExitSummary &summary,
    std::optional<uint64_t> boundary_pc = std::nullopt);
VirtualExitSummary virtualExitSummaryFromBoundaryFact(const BoundaryFact &fact);
BoundaryFact mergeBoundaryFacts(const BoundaryFact &base,
                                const BoundaryFact &overlay);

const char *toString(BoundaryKind kind);
const char *toString(BoundaryDisposition disposition);
const char *toString(ContinuationEntryTransformKind kind);

}  // namespace omill

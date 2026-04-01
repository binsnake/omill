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

struct BoundaryFact {
  std::optional<uint64_t> boundary_pc;
  std::optional<uint64_t> native_target_pc;
  std::optional<uint64_t> continuation_pc;
  std::optional<uint64_t> continuation_vip_pc;
  std::optional<unsigned> continuation_slot_id;
  std::optional<unsigned> continuation_stack_cell_id;
  BoundaryKind kind = BoundaryKind::kUnknown;
  BoundaryDisposition exit_disposition = BoundaryDisposition::kUnknown;
  bool is_partial_exit = false;
  bool is_full_exit = false;
  bool reenters_vm = false;
  bool is_vm_enter = false;
  bool is_nested_vm_enter = false;

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

const char *toString(BoundaryKind kind);
const char *toString(BoundaryDisposition disposition);

}  // namespace omill

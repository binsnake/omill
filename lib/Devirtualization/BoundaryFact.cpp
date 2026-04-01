#include "omill/Devirtualization/BoundaryFact.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>

namespace omill {

bool BoundaryFact::operator==(const BoundaryFact &other) const {
  return boundary_pc == other.boundary_pc &&
         native_target_pc == other.native_target_pc &&
         continuation_pc == other.continuation_pc &&
         continuation_vip_pc == other.continuation_vip_pc &&
         continuation_slot_id == other.continuation_slot_id &&
         continuation_stack_cell_id == other.continuation_stack_cell_id &&
         kind == other.kind && exit_disposition == other.exit_disposition &&
         is_partial_exit == other.is_partial_exit &&
         is_full_exit == other.is_full_exit &&
         reenters_vm == other.reenters_vm &&
         is_vm_enter == other.is_vm_enter &&
         is_nested_vm_enter == other.is_nested_vm_enter;
}

namespace {

constexpr const char *kVirtualExitDisposition = "omill.virtual_exit_disposition";
constexpr const char *kVirtualExitNativeTargetPc =
    "omill.virtual_exit_native_target_pc";
constexpr const char *kVirtualExitContinuationPc =
    "omill.virtual_exit_continuation_pc";
constexpr const char *kVirtualExitContinuationVip =
    "omill.virtual_exit_continuation_vip";
constexpr const char *kVirtualExitContinuationSlotId =
    "omill.virtual_exit_continuation_slot_id";
constexpr const char *kVirtualExitContinuationStackCellId =
    "omill.virtual_exit_continuation_stack_cell_id";
constexpr const char *kVirtualExitPartial = "omill.virtual_exit_partial";
constexpr const char *kVirtualExitFull = "omill.virtual_exit_full";
constexpr const char *kVirtualExitReentersVm = "omill.virtual_exit_reenters_vm";
constexpr const char *kNativeBoundaryPc = "omill.native_boundary_pc";
constexpr const char *kNativeDirectTargetPc = "omill.native_direct_target_pc";
constexpr const char *kVmEnterTargetPc = "omill.vm_enter_target_pc";

std::optional<uint64_t> parseHexString(llvm::StringRef text) {
  if (text.empty())
    return std::nullopt;
  if (text.consume_front("0x") || text.consume_front("0X")) {
  }
  uint64_t value = 0;
  if (text.getAsInteger(16, value))
    return std::nullopt;
  return value;
}

std::optional<uint64_t> getFunctionHexAttr(const llvm::Function &function,
                                           llvm::StringRef name) {
  auto attr = function.getFnAttribute(name);
  if (!attr.isValid())
    return std::nullopt;
  return parseHexString(attr.getValueAsString());
}

bool getFunctionBoolAttr(const llvm::Function &function, llvm::StringRef name) {
  auto attr = function.getFnAttribute(name);
  if (!attr.isValid())
    return false;
  auto text = attr.getValueAsString();
  return text.empty() || !text.equals_insensitive("0");
}

std::optional<llvm::StringRef> getFunctionStringAttr(const llvm::Function &function,
                                                     llvm::StringRef name) {
  auto attr = function.getFnAttribute(name);
  if (!attr.isValid())
    return std::nullopt;
  return attr.getValueAsString();
}

std::optional<llvm::StringRef> getCallStringAttr(const llvm::CallBase &call,
                                                 llvm::StringRef name) {
  auto attr = call.getFnAttr(name);
  if (!attr.isValid())
    return std::nullopt;
  return attr.getValueAsString();
}

std::optional<uint64_t> getCallHexAttr(const llvm::CallBase &call,
                                       llvm::StringRef name) {
  auto attr = call.getFnAttr(name);
  if (!attr.isValid())
    return std::nullopt;
  return parseHexString(attr.getValueAsString());
}

bool getCallBoolAttr(const llvm::CallBase &call, llvm::StringRef name) {
  auto attr = call.getFnAttr(name);
  if (!attr.isValid())
    return false;
  auto text = attr.getValueAsString();
  return text.empty() || !text.equals_insensitive("0");
}

BoundaryDisposition parseDisposition(llvm::StringRef text) {
  if (text == "stay_in_vm")
    return BoundaryDisposition::kStayInVm;
  if (text == "vm_exit_terminal")
    return BoundaryDisposition::kVmExitTerminal;
  if (text == "vm_exit_native_call_reenter")
    return BoundaryDisposition::kVmExitNativeCallReenter;
  if (text == "vm_exit_native_exec_unknown_return")
    return BoundaryDisposition::kVmExitNativeExecUnknownReturn;
  if (text == "vm_enter")
    return BoundaryDisposition::kVmEnter;
  if (text == "nested_vm_enter")
    return BoundaryDisposition::kNestedVmEnter;
  return BoundaryDisposition::kUnknown;
}

BoundaryKind inferKind(const BoundaryFact &fact) {
  if (fact.is_nested_vm_enter ||
      fact.exit_disposition == BoundaryDisposition::kNestedVmEnter) {
    return BoundaryKind::kNestedVmEnterBoundary;
  }
  if (fact.is_vm_enter || fact.exit_disposition == BoundaryDisposition::kVmEnter)
    return BoundaryKind::kVmEnterBoundary;
  if (fact.exit_disposition == BoundaryDisposition::kVmExitTerminal)
    return BoundaryKind::kTerminalBoundary;
  if (fact.native_target_pc.has_value() || fact.boundary_pc.has_value())
    return BoundaryKind::kNativeBoundary;
  if (fact.continuation_pc.has_value() || fact.continuation_vip_pc.has_value())
    return BoundaryKind::kContinuation;
  return BoundaryKind::kUnknown;
}

template <typename T>
void maybeSetFunctionHexAttr(llvm::Function &function, llvm::StringRef name,
                             const std::optional<T> &value) {
  if (!value)
    return;
  function.addFnAttr(name, llvm::utohexstr(static_cast<uint64_t>(*value)));
}

void maybeAddCallHexAttr(llvm::CallBase &call, llvm::StringRef name,
                         const std::optional<uint64_t> &value) {
  if (!value)
    return;
  call.addFnAttr(llvm::Attribute::get(call.getContext(), name,
                                      llvm::utohexstr(*value)));
}

void maybeAddCallBoolAttr(llvm::CallBase &call, llvm::StringRef name, bool value) {
  if (!value)
    return;
  call.addFnAttr(llvm::Attribute::get(call.getContext(), name, "1"));
}

}  // namespace

const char *toString(BoundaryKind kind) {
  switch (kind) {
    case BoundaryKind::kUnknown:
      return "unknown";
    case BoundaryKind::kContinuation:
      return "continuation";
    case BoundaryKind::kNativeBoundary:
      return "native_boundary";
    case BoundaryKind::kVmEnterBoundary:
      return "vm_enter_boundary";
    case BoundaryKind::kNestedVmEnterBoundary:
      return "nested_vm_enter_boundary";
    case BoundaryKind::kTerminalBoundary:
      return "terminal_boundary";
  }
  return "unknown";
}

const char *toString(BoundaryDisposition disposition) {
  switch (disposition) {
    case BoundaryDisposition::kUnknown:
      return "unknown";
    case BoundaryDisposition::kStayInVm:
      return "stay_in_vm";
    case BoundaryDisposition::kVmExitTerminal:
      return "vm_exit_terminal";
    case BoundaryDisposition::kVmExitNativeCallReenter:
      return "vm_exit_native_call_reenter";
    case BoundaryDisposition::kVmExitNativeExecUnknownReturn:
      return "vm_exit_native_exec_unknown_return";
    case BoundaryDisposition::kVmEnter:
      return "vm_enter";
    case BoundaryDisposition::kNestedVmEnter:
      return "nested_vm_enter";
  }
  return "unknown";
}

BoundaryDisposition boundaryDispositionFromVirtualExitDisposition(
    VirtualExitDisposition disposition) {
  switch (disposition) {
    case VirtualExitDisposition::kUnknown:
      return BoundaryDisposition::kUnknown;
    case VirtualExitDisposition::kStayInVm:
      return BoundaryDisposition::kStayInVm;
    case VirtualExitDisposition::kVmExitTerminal:
      return BoundaryDisposition::kVmExitTerminal;
    case VirtualExitDisposition::kVmExitNativeCallReenter:
      return BoundaryDisposition::kVmExitNativeCallReenter;
    case VirtualExitDisposition::kVmExitNativeExecUnknownReturn:
      return BoundaryDisposition::kVmExitNativeExecUnknownReturn;
    case VirtualExitDisposition::kVmEnter:
      return BoundaryDisposition::kVmEnter;
    case VirtualExitDisposition::kNestedVmEnter:
      return BoundaryDisposition::kNestedVmEnter;
  }
  return BoundaryDisposition::kUnknown;
}

VirtualExitDisposition virtualExitDispositionFromBoundaryDisposition(
    BoundaryDisposition disposition) {
  switch (disposition) {
    case BoundaryDisposition::kUnknown:
      return VirtualExitDisposition::kUnknown;
    case BoundaryDisposition::kStayInVm:
      return VirtualExitDisposition::kStayInVm;
    case BoundaryDisposition::kVmExitTerminal:
      return VirtualExitDisposition::kVmExitTerminal;
    case BoundaryDisposition::kVmExitNativeCallReenter:
      return VirtualExitDisposition::kVmExitNativeCallReenter;
    case BoundaryDisposition::kVmExitNativeExecUnknownReturn:
      return VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
    case BoundaryDisposition::kVmEnter:
      return VirtualExitDisposition::kVmEnter;
    case BoundaryDisposition::kNestedVmEnter:
      return VirtualExitDisposition::kNestedVmEnter;
  }
  return VirtualExitDisposition::kUnknown;
}

std::optional<BoundaryFact> readBoundaryFact(const llvm::CallBase &call) {
  BoundaryFact fact;
  fact.boundary_pc = getCallHexAttr(call, kNativeBoundaryPc);
  auto vm_enter_target_pc = getCallHexAttr(call, kVmEnterTargetPc);
  if (!fact.boundary_pc)
    fact.boundary_pc = vm_enter_target_pc;
  fact.native_target_pc = getCallHexAttr(call, kNativeDirectTargetPc);
  if (!fact.native_target_pc)
    fact.native_target_pc = getCallHexAttr(call, kVirtualExitNativeTargetPc);
  fact.continuation_pc = getCallHexAttr(call, kVirtualExitContinuationPc);
  fact.continuation_vip_pc = getCallHexAttr(call, kVirtualExitContinuationVip);
  if (auto slot_id = getCallHexAttr(call, kVirtualExitContinuationSlotId))
    fact.continuation_slot_id = static_cast<unsigned>(*slot_id);
  if (auto stack_cell_id =
          getCallHexAttr(call, kVirtualExitContinuationStackCellId)) {
    fact.continuation_stack_cell_id = static_cast<unsigned>(*stack_cell_id);
  }
  if (!fact.continuation_vip_pc)
    fact.continuation_vip_pc = fact.continuation_pc;
  if (auto disposition = getCallStringAttr(call, kVirtualExitDisposition))
    fact.exit_disposition = parseDisposition(*disposition);
  fact.is_partial_exit = getCallBoolAttr(call, kVirtualExitPartial);
  fact.is_full_exit = getCallBoolAttr(call, kVirtualExitFull);
  fact.reenters_vm = getCallBoolAttr(call, kVirtualExitReentersVm);
  fact.is_nested_vm_enter =
      fact.exit_disposition == BoundaryDisposition::kNestedVmEnter;
  fact.is_vm_enter =
      (vm_enter_target_pc.has_value() && !fact.is_nested_vm_enter) ||
      fact.exit_disposition == BoundaryDisposition::kVmEnter;
  fact.kind = inferKind(fact);

  if (!fact.boundary_pc && !fact.native_target_pc && !fact.continuation_pc &&
      !fact.continuation_vip_pc && !fact.continuation_slot_id &&
      !fact.continuation_stack_cell_id &&
      fact.exit_disposition == BoundaryDisposition::kUnknown &&
      !fact.is_partial_exit && !fact.is_full_exit && !fact.reenters_vm &&
      !fact.is_vm_enter && !fact.is_nested_vm_enter) {
    return std::nullopt;
  }
  return fact;
}

std::optional<BoundaryFact> readBoundaryFact(const llvm::Function &function) {
  BoundaryFact fact;
  fact.boundary_pc = getFunctionHexAttr(function, kNativeBoundaryPc);
  auto vm_enter_target_pc = getFunctionHexAttr(function, kVmEnterTargetPc);
  if (!fact.boundary_pc)
    fact.boundary_pc = vm_enter_target_pc;
  fact.native_target_pc = getFunctionHexAttr(function, kNativeDirectTargetPc);
  if (!fact.native_target_pc)
    fact.native_target_pc =
        getFunctionHexAttr(function, kVirtualExitNativeTargetPc);
  fact.continuation_pc =
      getFunctionHexAttr(function, kVirtualExitContinuationPc);
  fact.continuation_vip_pc =
      getFunctionHexAttr(function, kVirtualExitContinuationVip);
  if (auto slot_id =
          getFunctionHexAttr(function, kVirtualExitContinuationSlotId)) {
    fact.continuation_slot_id = static_cast<unsigned>(*slot_id);
  }
  if (auto stack_cell_id =
          getFunctionHexAttr(function, kVirtualExitContinuationStackCellId)) {
    fact.continuation_stack_cell_id = static_cast<unsigned>(*stack_cell_id);
  }
  if (!fact.continuation_vip_pc)
    fact.continuation_vip_pc = fact.continuation_pc;
  if (auto disposition = getFunctionStringAttr(function, kVirtualExitDisposition))
    fact.exit_disposition = parseDisposition(*disposition);
  fact.is_partial_exit = getFunctionBoolAttr(function, kVirtualExitPartial);
  fact.is_full_exit = getFunctionBoolAttr(function, kVirtualExitFull);
  fact.reenters_vm = getFunctionBoolAttr(function, kVirtualExitReentersVm);
  fact.is_nested_vm_enter =
      fact.exit_disposition == BoundaryDisposition::kNestedVmEnter;
  fact.is_vm_enter =
      (vm_enter_target_pc.has_value() && !fact.is_nested_vm_enter) ||
      fact.exit_disposition == BoundaryDisposition::kVmEnter;
  fact.kind = inferKind(fact);

  if (!fact.boundary_pc && !fact.native_target_pc && !fact.continuation_pc &&
      !fact.continuation_vip_pc && !fact.continuation_slot_id &&
      !fact.continuation_stack_cell_id &&
      fact.exit_disposition == BoundaryDisposition::kUnknown &&
      !fact.is_partial_exit && !fact.is_full_exit && !fact.reenters_vm &&
      !fact.is_vm_enter && !fact.is_nested_vm_enter) {
    return std::nullopt;
  }
  return fact;
}

void writeBoundaryFact(llvm::CallBase &call, const BoundaryFact &fact) {
  maybeAddCallHexAttr(call, kNativeBoundaryPc, fact.boundary_pc);
  if (fact.is_vm_enter || fact.is_nested_vm_enter)
    maybeAddCallHexAttr(call, kVmEnterTargetPc, fact.boundary_pc);
  maybeAddCallHexAttr(call, kVirtualExitNativeTargetPc, fact.native_target_pc);
  maybeAddCallHexAttr(call, kVirtualExitContinuationPc, fact.continuation_pc);
  maybeAddCallHexAttr(call, kVirtualExitContinuationVip, fact.continuation_vip_pc);
  if (fact.continuation_slot_id) {
    maybeAddCallHexAttr(call, kVirtualExitContinuationSlotId,
                        std::optional<uint64_t>(*fact.continuation_slot_id));
  }
  if (fact.continuation_stack_cell_id) {
    maybeAddCallHexAttr(
        call, kVirtualExitContinuationStackCellId,
        std::optional<uint64_t>(*fact.continuation_stack_cell_id));
  }
  if (fact.exit_disposition != BoundaryDisposition::kUnknown) {
    call.addFnAttr(llvm::Attribute::get(call.getContext(), kVirtualExitDisposition,
                                        toString(fact.exit_disposition)));
  }
  maybeAddCallBoolAttr(call, kVirtualExitPartial, fact.is_partial_exit);
  maybeAddCallBoolAttr(call, kVirtualExitFull, fact.is_full_exit);
  maybeAddCallBoolAttr(call, kVirtualExitReentersVm, fact.reenters_vm);
}

void writeBoundaryFact(llvm::Function &function, const BoundaryFact &fact) {
  maybeSetFunctionHexAttr(function, kNativeBoundaryPc, fact.boundary_pc);
  if (fact.is_vm_enter || fact.is_nested_vm_enter)
    maybeSetFunctionHexAttr(function, kVmEnterTargetPc, fact.boundary_pc);
  maybeSetFunctionHexAttr(function, kVirtualExitNativeTargetPc,
                          fact.native_target_pc);
  if (fact.native_target_pc &&
      fact.kind == BoundaryKind::kNativeBoundary) {
    maybeSetFunctionHexAttr(function, kNativeDirectTargetPc, fact.native_target_pc);
  }
  maybeSetFunctionHexAttr(function, kVirtualExitContinuationPc,
                          fact.continuation_pc);
  maybeSetFunctionHexAttr(function, kVirtualExitContinuationVip,
                          fact.continuation_vip_pc);
  if (fact.continuation_slot_id) {
    maybeSetFunctionHexAttr(function, kVirtualExitContinuationSlotId,
                            std::optional<uint64_t>(*fact.continuation_slot_id));
  }
  if (fact.continuation_stack_cell_id) {
    maybeSetFunctionHexAttr(
        function, kVirtualExitContinuationStackCellId,
        std::optional<uint64_t>(*fact.continuation_stack_cell_id));
  }
  if (fact.exit_disposition != BoundaryDisposition::kUnknown) {
    function.addFnAttr(kVirtualExitDisposition, toString(fact.exit_disposition));
  }
  if (fact.is_partial_exit)
    function.addFnAttr(kVirtualExitPartial, "1");
  if (fact.is_full_exit)
    function.addFnAttr(kVirtualExitFull, "1");
  if (fact.reenters_vm)
    function.addFnAttr(kVirtualExitReentersVm, "1");
}

BoundaryFact boundaryFactFromVirtualExitSummary(
    const VirtualExitSummary &summary, std::optional<uint64_t> boundary_pc) {
  BoundaryFact fact;
  fact.boundary_pc = boundary_pc;
  fact.native_target_pc = summary.native_target_pc;
  fact.continuation_pc = summary.continuation_pc;
  fact.continuation_vip_pc = summary.continuation_vip.resolved_pc;
  fact.continuation_slot_id = summary.continuation_vip.slot_id;
  fact.continuation_stack_cell_id = summary.continuation_vip.stack_cell_id;
  if (!fact.continuation_vip_pc)
    fact.continuation_vip_pc = fact.continuation_pc;
  fact.exit_disposition =
      boundaryDispositionFromVirtualExitDisposition(summary.disposition);
  fact.is_partial_exit = summary.is_partial_exit;
  fact.is_full_exit = summary.is_full_exit;
  fact.reenters_vm = summary.reenters_vm;
  fact.is_vm_enter = summary.disposition == VirtualExitDisposition::kVmEnter;
  fact.is_nested_vm_enter =
      summary.disposition == VirtualExitDisposition::kNestedVmEnter;
  fact.kind = inferKind(fact);
  return fact;
}

VirtualExitSummary virtualExitSummaryFromBoundaryFact(const BoundaryFact &fact) {
  VirtualExitSummary summary;
  summary.disposition =
      virtualExitDispositionFromBoundaryDisposition(fact.exit_disposition);
  summary.native_target_pc = fact.native_target_pc;
  summary.continuation_pc = fact.continuation_pc;
  if (fact.continuation_vip_pc) {
    summary.continuation_vip.resolved_pc = *fact.continuation_vip_pc;
    summary.continuation_vip.expr_before_dispatch.kind = VirtualExprKind::kConstant;
    summary.continuation_vip.expr_before_dispatch.bit_width = 64;
    summary.continuation_vip.expr_before_dispatch.complete = true;
    summary.continuation_vip.expr_before_dispatch.constant =
        *fact.continuation_vip_pc;
    summary.continuation_vip.expr_after_dispatch =
        summary.continuation_vip.expr_before_dispatch;
    summary.continuation_vip.symbolic = false;
  }
  summary.continuation_vip.slot_id = fact.continuation_slot_id;
  summary.continuation_vip.stack_cell_id = fact.continuation_stack_cell_id;
  if (summary.continuation_vip.stack_cell_id) {
    summary.continuation_vip.source_kind =
        VirtualInstructionPointerSourceKind::kStackCell;
  } else if (summary.continuation_vip.slot_id) {
    summary.continuation_vip.source_kind =
        VirtualInstructionPointerSourceKind::kNamedSlot;
  }
  summary.is_partial_exit = fact.is_partial_exit;
  summary.is_full_exit = fact.is_full_exit;
  summary.reenters_vm = fact.reenters_vm;
  return summary;
}

}  // namespace omill

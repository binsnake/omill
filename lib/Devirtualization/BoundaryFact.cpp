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
         controlled_return_pc == other.controlled_return_pc &&
         continuation_slot_id == other.continuation_slot_id &&
         continuation_stack_cell_id == other.continuation_stack_cell_id &&
         continuation_owner_id == other.continuation_owner_id &&
         continuation_owner_kind == other.continuation_owner_kind &&
         covered_entry_pc == other.covered_entry_pc &&
         continuation_entry_transform == other.continuation_entry_transform &&
         return_address_control_kind == other.return_address_control_kind &&
         kind == other.kind && exit_disposition == other.exit_disposition &&
         is_partial_exit == other.is_partial_exit &&
         is_full_exit == other.is_full_exit &&
         reenters_vm == other.reenters_vm &&
         is_vm_enter == other.is_vm_enter &&
         is_nested_vm_enter == other.is_nested_vm_enter &&
         suppresses_normal_fallthrough == other.suppresses_normal_fallthrough;
}

namespace {

constexpr const char *kVirtualExitDisposition = "omill.virtual_exit_disposition";
constexpr const char *kVirtualExitNativeTargetPc =
    "omill.virtual_exit_native_target_pc";
constexpr const char *kVirtualExitContinuationPc =
    "omill.virtual_exit_continuation_pc";
constexpr const char *kVirtualExitContinuationVip =
    "omill.virtual_exit_continuation_vip";
constexpr const char *kVirtualExitControlledReturnPc =
    "omill.virtual_exit_controlled_return_pc";
constexpr const char *kVirtualExitReturnControlKind =
    "omill.virtual_exit_return_control_kind";
constexpr const char *kVirtualExitContinuationSlotId =
    "omill.virtual_exit_continuation_slot_id";
constexpr const char *kVirtualExitContinuationStackCellId =
    "omill.virtual_exit_continuation_stack_cell_id";
constexpr const char *kVirtualExitContinuationOwnerId =
    "omill.virtual_exit_continuation_owner_id";
constexpr const char *kVirtualExitContinuationOwnerKind =
    "omill.virtual_exit_continuation_owner_kind";
constexpr const char *kVirtualExitCoveredEntryPc =
    "omill.virtual_exit_covered_entry_pc";
constexpr const char *kVirtualExitEntryTransformKind =
    "omill.virtual_exit_entry_transform_kind";
constexpr const char *kVirtualExitEntryTransformTargetPc =
    "omill.virtual_exit_entry_transform_target_pc";
constexpr const char *kVirtualExitEntryTransformImmediate =
    "omill.virtual_exit_entry_transform_imm";
constexpr const char *kVirtualExitEntryTransformSuppressesFallthrough =
    "omill.virtual_exit_entry_transform_suppresses_normal_fallthrough";
constexpr const char *kVirtualExitPartial = "omill.virtual_exit_partial";
constexpr const char *kVirtualExitFull = "omill.virtual_exit_full";
constexpr const char *kVirtualExitReentersVm = "omill.virtual_exit_reenters_vm";
constexpr const char *kVirtualExitSuppressesNormalFallthrough =
    "omill.virtual_exit_suppresses_normal_fallthrough";
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

VirtualReturnAddressControlKind parseReturnAddressControlKind(
    llvm::StringRef text) {
  if (text == "preserved")
    return VirtualReturnAddressControlKind::kPreserved;
  if (text == "state_slot_controlled")
    return VirtualReturnAddressControlKind::kStateSlotControlled;
  if (text == "stack_cell_controlled")
    return VirtualReturnAddressControlKind::kStackCellControlled;
  if (text == "redirected_constant")
    return VirtualReturnAddressControlKind::kRedirectedConstant;
  if (text == "redirected_symbolic")
    return VirtualReturnAddressControlKind::kRedirectedSymbolic;
  if (text == "clobbered")
    return VirtualReturnAddressControlKind::kClobbered;
  return VirtualReturnAddressControlKind::kUnknown;
}

VirtualStackOwnerKind parseStackOwnerKind(llvm::StringRef text) {
  if (text == "native_stack_pointer")
    return VirtualStackOwnerKind::kNativeStackPointer;
  if (text == "frame_pointer_like")
    return VirtualStackOwnerKind::kFramePointerLike;
  if (text == "vm_stack_root_slot")
    return VirtualStackOwnerKind::kVmStackRootSlot;
  if (text == "argument_root")
    return VirtualStackOwnerKind::kArgumentRoot;
  if (text == "alloca_root")
    return VirtualStackOwnerKind::kAllocaRoot;
  if (text == "derived_owner")
    return VirtualStackOwnerKind::kDerivedOwner;
  return VirtualStackOwnerKind::kUnknown;
}

ContinuationEntryTransformKind parseContinuationEntryTransformKind(
    llvm::StringRef text) {
  if (text == "push_immediate_jump")
    return ContinuationEntryTransformKind::kPushImmediateJump;
  if (text == "synthetic_return_token")
    return ContinuationEntryTransformKind::kSyntheticReturnToken;
  return ContinuationEntryTransformKind::kNone;
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

const char *toString(ContinuationEntryTransformKind kind) {
  switch (kind) {
    case ContinuationEntryTransformKind::kNone:
      return "none";
    case ContinuationEntryTransformKind::kPushImmediateJump:
      return "push_immediate_jump";
    case ContinuationEntryTransformKind::kSyntheticReturnToken:
      return "synthetic_return_token";
  }
  return "none";
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
  fact.controlled_return_pc =
      getCallHexAttr(call, kVirtualExitControlledReturnPc);
  if (auto kind = getCallStringAttr(call, kVirtualExitReturnControlKind))
    fact.return_address_control_kind = parseReturnAddressControlKind(*kind);
  if (auto slot_id = getCallHexAttr(call, kVirtualExitContinuationSlotId))
    fact.continuation_slot_id = static_cast<unsigned>(*slot_id);
  if (auto stack_cell_id =
          getCallHexAttr(call, kVirtualExitContinuationStackCellId)) {
    fact.continuation_stack_cell_id = static_cast<unsigned>(*stack_cell_id);
  }
  if (auto owner_id = getCallHexAttr(call, kVirtualExitContinuationOwnerId))
    fact.continuation_owner_id = static_cast<unsigned>(*owner_id);
  if (auto owner_kind = getCallStringAttr(call, kVirtualExitContinuationOwnerKind))
    fact.continuation_owner_kind = parseStackOwnerKind(*owner_kind);
  fact.covered_entry_pc = getCallHexAttr(call, kVirtualExitCoveredEntryPc);
  if (auto transform_kind =
          getCallStringAttr(call, kVirtualExitEntryTransformKind)) {
    ContinuationEntryTransform transform;
    transform.kind = parseContinuationEntryTransformKind(*transform_kind);
    transform.entry_pc =
        fact.covered_entry_pc ? fact.covered_entry_pc : fact.continuation_pc;
    transform.jump_target_pc =
        getCallHexAttr(call, kVirtualExitEntryTransformTargetPc);
    transform.pushed_immediate =
        getCallHexAttr(call, kVirtualExitEntryTransformImmediate);
    transform.suppresses_normal_fallthrough = getCallBoolAttr(
        call, kVirtualExitEntryTransformSuppressesFallthrough);
    if (transform.kind != ContinuationEntryTransformKind::kNone)
      fact.continuation_entry_transform = transform;
  }
  if (!fact.continuation_vip_pc)
    fact.continuation_vip_pc = fact.continuation_pc;
  if (auto disposition = getCallStringAttr(call, kVirtualExitDisposition))
    fact.exit_disposition = parseDisposition(*disposition);
  fact.is_partial_exit = getCallBoolAttr(call, kVirtualExitPartial);
  fact.is_full_exit = getCallBoolAttr(call, kVirtualExitFull);
  fact.reenters_vm = getCallBoolAttr(call, kVirtualExitReentersVm);
  fact.suppresses_normal_fallthrough =
      getCallBoolAttr(call, kVirtualExitSuppressesNormalFallthrough);
  fact.is_nested_vm_enter =
      fact.exit_disposition == BoundaryDisposition::kNestedVmEnter;
  fact.is_vm_enter =
      (vm_enter_target_pc.has_value() && !fact.is_nested_vm_enter) ||
      fact.exit_disposition == BoundaryDisposition::kVmEnter;
  fact.kind = inferKind(fact);

  if (!fact.boundary_pc && !fact.native_target_pc && !fact.continuation_pc &&
      !fact.continuation_vip_pc && !fact.controlled_return_pc &&
      !fact.continuation_slot_id &&
      !fact.continuation_stack_cell_id &&
      !fact.continuation_owner_id &&
      fact.continuation_owner_kind == VirtualStackOwnerKind::kUnknown &&
      !fact.covered_entry_pc && !fact.continuation_entry_transform &&
      fact.return_address_control_kind == VirtualReturnAddressControlKind::kUnknown &&
      fact.exit_disposition == BoundaryDisposition::kUnknown &&
      !fact.is_partial_exit && !fact.is_full_exit && !fact.reenters_vm &&
      !fact.is_vm_enter && !fact.is_nested_vm_enter &&
      !fact.suppresses_normal_fallthrough) {
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
  fact.controlled_return_pc =
      getFunctionHexAttr(function, kVirtualExitControlledReturnPc);
  if (auto kind = getFunctionStringAttr(function, kVirtualExitReturnControlKind))
    fact.return_address_control_kind = parseReturnAddressControlKind(*kind);
  if (auto slot_id =
          getFunctionHexAttr(function, kVirtualExitContinuationSlotId)) {
    fact.continuation_slot_id = static_cast<unsigned>(*slot_id);
  }
  if (auto stack_cell_id =
          getFunctionHexAttr(function, kVirtualExitContinuationStackCellId)) {
    fact.continuation_stack_cell_id = static_cast<unsigned>(*stack_cell_id);
  }
  if (auto owner_id =
          getFunctionHexAttr(function, kVirtualExitContinuationOwnerId)) {
    fact.continuation_owner_id = static_cast<unsigned>(*owner_id);
  }
  if (auto owner_kind =
          getFunctionStringAttr(function, kVirtualExitContinuationOwnerKind)) {
    fact.continuation_owner_kind = parseStackOwnerKind(*owner_kind);
  }
  fact.covered_entry_pc =
      getFunctionHexAttr(function, kVirtualExitCoveredEntryPc);
  if (auto transform_kind =
          getFunctionStringAttr(function, kVirtualExitEntryTransformKind)) {
    ContinuationEntryTransform transform;
    transform.kind = parseContinuationEntryTransformKind(*transform_kind);
    transform.entry_pc =
        fact.covered_entry_pc ? fact.covered_entry_pc : fact.continuation_pc;
    transform.jump_target_pc =
        getFunctionHexAttr(function, kVirtualExitEntryTransformTargetPc);
    transform.pushed_immediate =
        getFunctionHexAttr(function, kVirtualExitEntryTransformImmediate);
    transform.suppresses_normal_fallthrough = getFunctionBoolAttr(
        function, kVirtualExitEntryTransformSuppressesFallthrough);
    if (transform.kind != ContinuationEntryTransformKind::kNone)
      fact.continuation_entry_transform = transform;
  }
  if (!fact.continuation_vip_pc)
    fact.continuation_vip_pc = fact.continuation_pc;
  if (auto disposition = getFunctionStringAttr(function, kVirtualExitDisposition))
    fact.exit_disposition = parseDisposition(*disposition);
  fact.is_partial_exit = getFunctionBoolAttr(function, kVirtualExitPartial);
  fact.is_full_exit = getFunctionBoolAttr(function, kVirtualExitFull);
  fact.reenters_vm = getFunctionBoolAttr(function, kVirtualExitReentersVm);
  fact.suppresses_normal_fallthrough =
      getFunctionBoolAttr(function, kVirtualExitSuppressesNormalFallthrough);
  fact.is_nested_vm_enter =
      fact.exit_disposition == BoundaryDisposition::kNestedVmEnter;
  fact.is_vm_enter =
      (vm_enter_target_pc.has_value() && !fact.is_nested_vm_enter) ||
      fact.exit_disposition == BoundaryDisposition::kVmEnter;
  fact.kind = inferKind(fact);

  if (!fact.boundary_pc && !fact.native_target_pc && !fact.continuation_pc &&
      !fact.continuation_vip_pc && !fact.controlled_return_pc &&
      !fact.continuation_slot_id &&
      !fact.continuation_stack_cell_id &&
      !fact.continuation_owner_id &&
      fact.continuation_owner_kind == VirtualStackOwnerKind::kUnknown &&
      !fact.covered_entry_pc && !fact.continuation_entry_transform &&
      fact.return_address_control_kind == VirtualReturnAddressControlKind::kUnknown &&
      fact.exit_disposition == BoundaryDisposition::kUnknown &&
      !fact.is_partial_exit && !fact.is_full_exit && !fact.reenters_vm &&
      !fact.is_vm_enter && !fact.is_nested_vm_enter &&
      !fact.suppresses_normal_fallthrough) {
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
  maybeAddCallHexAttr(call, kVirtualExitControlledReturnPc,
                      fact.controlled_return_pc);
  if (fact.return_address_control_kind !=
      VirtualReturnAddressControlKind::kUnknown) {
    call.addFnAttr(llvm::Attribute::get(call.getContext(),
                                        kVirtualExitReturnControlKind,
                                        renderVirtualReturnAddressControlKind(
                                            fact.return_address_control_kind)));
  }
  if (fact.continuation_slot_id) {
    maybeAddCallHexAttr(call, kVirtualExitContinuationSlotId,
                        std::optional<uint64_t>(*fact.continuation_slot_id));
  }
  if (fact.continuation_stack_cell_id) {
    maybeAddCallHexAttr(
        call, kVirtualExitContinuationStackCellId,
        std::optional<uint64_t>(*fact.continuation_stack_cell_id));
  }
  if (fact.continuation_owner_id) {
    maybeAddCallHexAttr(call, kVirtualExitContinuationOwnerId,
                        std::optional<uint64_t>(*fact.continuation_owner_id));
  }
  if (fact.continuation_owner_kind != VirtualStackOwnerKind::kUnknown) {
    call.addFnAttr(llvm::Attribute::get(call.getContext(),
                                        kVirtualExitContinuationOwnerKind,
                                        renderVirtualStackOwnerKind(
                                            fact.continuation_owner_kind)));
  }
  maybeAddCallHexAttr(call, kVirtualExitCoveredEntryPc, fact.covered_entry_pc);
  if (fact.continuation_entry_transform) {
    call.addFnAttr(llvm::Attribute::get(
        call.getContext(), kVirtualExitEntryTransformKind,
        toString(fact.continuation_entry_transform->kind)));
    maybeAddCallHexAttr(call, kVirtualExitEntryTransformTargetPc,
                        fact.continuation_entry_transform->jump_target_pc);
    maybeAddCallHexAttr(call, kVirtualExitEntryTransformImmediate,
                        fact.continuation_entry_transform->pushed_immediate);
    maybeAddCallBoolAttr(
        call, kVirtualExitEntryTransformSuppressesFallthrough,
        fact.continuation_entry_transform->suppresses_normal_fallthrough);
  }
  if (fact.exit_disposition != BoundaryDisposition::kUnknown) {
    call.addFnAttr(llvm::Attribute::get(call.getContext(), kVirtualExitDisposition,
                                        toString(fact.exit_disposition)));
  }
  maybeAddCallBoolAttr(call, kVirtualExitPartial, fact.is_partial_exit);
  maybeAddCallBoolAttr(call, kVirtualExitFull, fact.is_full_exit);
  maybeAddCallBoolAttr(call, kVirtualExitReentersVm, fact.reenters_vm);
  maybeAddCallBoolAttr(call, kVirtualExitSuppressesNormalFallthrough,
                       fact.suppresses_normal_fallthrough);
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
  maybeSetFunctionHexAttr(function, kVirtualExitControlledReturnPc,
                          fact.controlled_return_pc);
  if (fact.return_address_control_kind !=
      VirtualReturnAddressControlKind::kUnknown) {
    function.addFnAttr(kVirtualExitReturnControlKind,
                       renderVirtualReturnAddressControlKind(
                           fact.return_address_control_kind));
  }
  if (fact.continuation_slot_id) {
    maybeSetFunctionHexAttr(function, kVirtualExitContinuationSlotId,
                            std::optional<uint64_t>(*fact.continuation_slot_id));
  }
  if (fact.continuation_stack_cell_id) {
    maybeSetFunctionHexAttr(
        function, kVirtualExitContinuationStackCellId,
        std::optional<uint64_t>(*fact.continuation_stack_cell_id));
  }
  if (fact.continuation_owner_id) {
    maybeSetFunctionHexAttr(
        function, kVirtualExitContinuationOwnerId,
        std::optional<uint64_t>(*fact.continuation_owner_id));
  }
  if (fact.continuation_owner_kind != VirtualStackOwnerKind::kUnknown) {
    function.addFnAttr(kVirtualExitContinuationOwnerKind,
                       renderVirtualStackOwnerKind(
                           fact.continuation_owner_kind));
  }
  maybeSetFunctionHexAttr(function, kVirtualExitCoveredEntryPc,
                          fact.covered_entry_pc);
  if (fact.continuation_entry_transform) {
    function.addFnAttr(kVirtualExitEntryTransformKind,
                       toString(fact.continuation_entry_transform->kind));
    maybeSetFunctionHexAttr(function, kVirtualExitEntryTransformTargetPc,
                            fact.continuation_entry_transform->jump_target_pc);
    maybeSetFunctionHexAttr(function, kVirtualExitEntryTransformImmediate,
                            fact.continuation_entry_transform->pushed_immediate);
    if (fact.continuation_entry_transform->suppresses_normal_fallthrough)
      function.addFnAttr(kVirtualExitEntryTransformSuppressesFallthrough, "1");
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
  if (fact.suppresses_normal_fallthrough)
    function.addFnAttr(kVirtualExitSuppressesNormalFallthrough, "1");
}

BoundaryFact boundaryFactFromVirtualExitSummary(
    const VirtualExitSummary &summary, std::optional<uint64_t> boundary_pc) {
  BoundaryFact fact;
  fact.boundary_pc = boundary_pc;
  fact.native_target_pc = summary.native_target_pc;
  fact.continuation_pc = summary.continuation_pc;
  fact.continuation_vip_pc = summary.continuation_vip.resolved_pc;
  fact.controlled_return_pc =
      summary.return_address_control.resolved_effective_return_pc;
  fact.continuation_slot_id = summary.continuation_vip.slot_id;
  fact.continuation_stack_cell_id = summary.continuation_vip.stack_cell_id;
  fact.continuation_owner_id = summary.return_address_control.return_owner_id;
  fact.continuation_owner_kind = summary.return_address_control.return_owner_kind;
  fact.return_address_control_kind = summary.return_address_control.kind;
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
  fact.suppresses_normal_fallthrough =
      summary.return_address_control.suppresses_normal_fallthrough;
  fact.kind = inferKind(fact);
  return fact;
}

VirtualExitSummary virtualExitSummaryFromBoundaryFact(const BoundaryFact &fact) {
  VirtualExitSummary summary;
  summary.disposition =
      virtualExitDispositionFromBoundaryDisposition(fact.exit_disposition);
  summary.native_target_pc = fact.native_target_pc;
  summary.continuation_pc = fact.continuation_pc;
  summary.return_address_control.kind = fact.return_address_control_kind;
  summary.return_address_control.original_return_pc = fact.continuation_pc;
  summary.return_address_control.return_slot_id = fact.continuation_slot_id;
  summary.return_address_control.return_stack_cell_id =
      fact.continuation_stack_cell_id;
  summary.return_address_control.return_owner_id = fact.continuation_owner_id;
  summary.return_address_control.return_owner_kind =
      fact.continuation_owner_kind;
  summary.return_address_control.resolved_effective_return_pc =
      fact.controlled_return_pc;
  summary.return_address_control.suppresses_normal_fallthrough =
      fact.suppresses_normal_fallthrough;
  if (fact.controlled_return_pc) {
    summary.return_address_control.effective_return_expr.kind =
        VirtualExprKind::kConstant;
    summary.return_address_control.effective_return_expr.bit_width = 64;
    summary.return_address_control.effective_return_expr.complete = true;
    summary.return_address_control.effective_return_expr.constant =
        *fact.controlled_return_pc;
  }
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

BoundaryFact mergeBoundaryFacts(const BoundaryFact &base,
                                const BoundaryFact &overlay) {
  BoundaryFact merged = base;
  if (!merged.boundary_pc)
    merged.boundary_pc = overlay.boundary_pc;
  if (!merged.native_target_pc)
    merged.native_target_pc = overlay.native_target_pc;
  if (!merged.continuation_pc)
    merged.continuation_pc = overlay.continuation_pc;
  if (!merged.continuation_vip_pc)
    merged.continuation_vip_pc = overlay.continuation_vip_pc;
  if (!merged.controlled_return_pc)
    merged.controlled_return_pc = overlay.controlled_return_pc;
  if (!merged.continuation_slot_id)
    merged.continuation_slot_id = overlay.continuation_slot_id;
  if (!merged.continuation_stack_cell_id)
    merged.continuation_stack_cell_id = overlay.continuation_stack_cell_id;
  if (!merged.continuation_owner_id)
    merged.continuation_owner_id = overlay.continuation_owner_id;
  if (merged.continuation_owner_kind == VirtualStackOwnerKind::kUnknown)
    merged.continuation_owner_kind = overlay.continuation_owner_kind;
  if (!merged.covered_entry_pc)
    merged.covered_entry_pc = overlay.covered_entry_pc;
  if (!merged.continuation_entry_transform)
    merged.continuation_entry_transform = overlay.continuation_entry_transform;
  if (merged.return_address_control_kind ==
      VirtualReturnAddressControlKind::kUnknown) {
    merged.return_address_control_kind = overlay.return_address_control_kind;
  }
  if (merged.kind == BoundaryKind::kUnknown)
    merged.kind = overlay.kind;
  if (merged.exit_disposition == BoundaryDisposition::kUnknown)
    merged.exit_disposition = overlay.exit_disposition;
  merged.is_partial_exit = merged.is_partial_exit || overlay.is_partial_exit;
  merged.is_full_exit = merged.is_full_exit || overlay.is_full_exit;
  merged.reenters_vm = merged.reenters_vm || overlay.reenters_vm;
  merged.is_vm_enter = merged.is_vm_enter || overlay.is_vm_enter;
  merged.is_nested_vm_enter =
      merged.is_nested_vm_enter || overlay.is_nested_vm_enter;
  merged.suppresses_normal_fallthrough =
      merged.suppresses_normal_fallthrough ||
      overlay.suppresses_normal_fallthrough;
  return merged;
}

}  // namespace omill

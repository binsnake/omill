#include "omill/Devirtualization/ExecutableTargetFact.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

bool ExecutableTargetFact::operator==(const ExecutableTargetFact &other) const {
  return raw_target_pc == other.raw_target_pc &&
         effective_target_pc == other.effective_target_pc &&
         canonical_owner_pc == other.canonical_owner_pc &&
         kind == other.kind && trust == other.trust &&
         exact_fallthrough_target == other.exact_fallthrough_target &&
         invalidated_executable_entry == other.invalidated_executable_entry &&
         invalidated_entry_source_pc == other.invalidated_entry_source_pc &&
         invalidated_entry_failed_pc == other.invalidated_entry_failed_pc;
}

namespace {

constexpr const char *kExecutableTargetPc = "omill.executable_target_pc";
constexpr const char *kEffectiveTargetPc = "omill.effective_target_pc";
constexpr const char *kCanonicalOwnerPc = "omill.canonical_owner_pc";
constexpr const char *kExactFallthroughTarget =
    "omill.exact_fallthrough_target";
constexpr const char *kInvalidatedExecutableEntry =
    "omill.invalidated_executable_entry";
constexpr const char *kInvalidatedEntrySourcePc =
    "omill.invalidated_entry_source_pc";
constexpr const char *kInvalidatedEntryFailedPc =
    "omill.invalidated_entry_failed_pc";
constexpr const char *kExecutableTargetKind = "omill.executable_target_kind";
constexpr const char *kExecutableTargetTrust = "omill.executable_target_trust";

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

std::optional<uint64_t> getInstructionU64Metadata(const llvm::Instruction &inst,
                                                  llvm::StringRef name) {
  auto *md = inst.getMetadata(name);
  auto *tuple = llvm::dyn_cast_or_null<llvm::MDTuple>(md);
  if (!tuple || tuple->getNumOperands() == 0)
    return std::nullopt;
  auto *value = llvm::mdconst::dyn_extract<llvm::ConstantInt>(
      tuple->getOperand(0));
  if (!value)
    return std::nullopt;
  return value->getZExtValue();
}

bool getInstructionBoolMetadata(const llvm::Instruction &inst,
                                llvm::StringRef name) {
  auto value = getInstructionU64Metadata(inst, name);
  return value.has_value() && *value != 0;
}

std::optional<llvm::StringRef> getInstructionStringMetadata(
    const llvm::Instruction &inst, llvm::StringRef name) {
  auto *md = inst.getMetadata(name);
  auto *tuple = llvm::dyn_cast_or_null<llvm::MDTuple>(md);
  if (!tuple || tuple->getNumOperands() == 0)
    return std::nullopt;
  auto *value = llvm::dyn_cast<llvm::MDString>(tuple->getOperand(0));
  if (!value)
    return std::nullopt;
  return value->getString();
}

void setInstructionU64Metadata(llvm::Instruction &inst, llvm::StringRef name,
                               uint64_t value) {
  auto &ctx = inst.getContext();
  inst.setMetadata(
      name,
      llvm::MDTuple::get(
          ctx, {llvm::ConstantAsMetadata::get(
                    llvm::ConstantInt::get(llvm::Type::getInt64Ty(ctx), value))}));
}

void setInstructionBoolMetadata(llvm::Instruction &inst, llvm::StringRef name,
                                bool value) {
  auto &ctx = inst.getContext();
  inst.setMetadata(
      name,
      llvm::MDTuple::get(
          ctx, {llvm::ConstantAsMetadata::get(
                    llvm::ConstantInt::get(llvm::Type::getInt1Ty(ctx), value))}));
}

void setInstructionStringMetadata(llvm::Instruction &inst, llvm::StringRef name,
                                  llvm::StringRef value) {
  auto &ctx = inst.getContext();
  llvm::Metadata *ops[] = {llvm::MDString::get(ctx, value)};
  inst.setMetadata(name, llvm::MDTuple::get(ctx, ops));
}

ExecutableTargetKind kindFromString(llvm::StringRef value) {
  if (value == "liftable_entry")
    return ExecutableTargetKind::kLiftableEntry;
  if (value == "exact_fallthrough_entry")
    return ExecutableTargetKind::kExactFallthroughEntry;
  if (value == "invalidated_executable_entry")
    return ExecutableTargetKind::kInvalidatedExecutableEntry;
  if (value == "executable_placeholder")
    return ExecutableTargetKind::kExecutablePlaceholder;
  if (value == "canonical_owner")
    return ExecutableTargetKind::kCanonicalOwner;
  if (value == "suppress")
    return ExecutableTargetKind::kSuppress;
  return ExecutableTargetKind::kTerminal;
}

ExecutableTargetTrust trustFromString(llvm::StringRef value) {
  if (value == "trusted_entry")
    return ExecutableTargetTrust::kTrustedEntry;
  if (value == "exact_fallthrough")
    return ExecutableTargetTrust::kExactFallthrough;
  if (value == "nearby_owner")
    return ExecutableTargetTrust::kNearbyOwner;
  if (value == "invalidated_entry")
    return ExecutableTargetTrust::kInvalidatedEntry;
  if (value == "untrusted_executable")
    return ExecutableTargetTrust::kUntrustedExecutable;
  if (value == "suppressed")
    return ExecutableTargetTrust::kSuppressed;
  return ExecutableTargetTrust::kTerminal;
}

ExecutableTargetKind inferKind(const ExecutableTargetFact &fact) {
  if (fact.invalidated_executable_entry)
    return ExecutableTargetKind::kInvalidatedExecutableEntry;
  if (fact.canonical_owner_pc.has_value() &&
      *fact.canonical_owner_pc != fact.raw_target_pc)
    return ExecutableTargetKind::kCanonicalOwner;
  if (fact.exact_fallthrough_target)
    return ExecutableTargetKind::kExactFallthroughEntry;
  return ExecutableTargetKind::kExecutablePlaceholder;
}

ExecutableTargetTrust inferTrust(const ExecutableTargetFact &fact) {
  if (fact.invalidated_executable_entry)
    return ExecutableTargetTrust::kInvalidatedEntry;
  if (fact.canonical_owner_pc.has_value() &&
      *fact.canonical_owner_pc != fact.raw_target_pc)
    return ExecutableTargetTrust::kNearbyOwner;
  if (fact.exact_fallthrough_target)
    return ExecutableTargetTrust::kExactFallthrough;
  return ExecutableTargetTrust::kUntrustedExecutable;
}

template <typename T>
void maybeSetFunctionHexAttr(llvm::Function &function, llvm::StringRef name,
                             const std::optional<T> &value) {
  if (!value)
    return;
  function.addFnAttr(name, llvm::utohexstr(static_cast<uint64_t>(*value)));
}

}  // namespace

const char *toString(ExecutableTargetKind kind) {
  switch (kind) {
    case ExecutableTargetKind::kLiftableEntry:
      return "liftable_entry";
    case ExecutableTargetKind::kExactFallthroughEntry:
      return "exact_fallthrough_entry";
    case ExecutableTargetKind::kInvalidatedExecutableEntry:
      return "invalidated_executable_entry";
    case ExecutableTargetKind::kExecutablePlaceholder:
      return "executable_placeholder";
    case ExecutableTargetKind::kCanonicalOwner:
      return "canonical_owner";
    case ExecutableTargetKind::kSuppress:
      return "suppress";
    case ExecutableTargetKind::kTerminal:
      return "terminal";
  }
  return "terminal";
}

const char *toString(ExecutableTargetTrust trust) {
  switch (trust) {
    case ExecutableTargetTrust::kTrustedEntry:
      return "trusted_entry";
    case ExecutableTargetTrust::kExactFallthrough:
      return "exact_fallthrough";
    case ExecutableTargetTrust::kNearbyOwner:
      return "nearby_owner";
    case ExecutableTargetTrust::kInvalidatedEntry:
      return "invalidated_entry";
    case ExecutableTargetTrust::kUntrustedExecutable:
      return "untrusted_executable";
    case ExecutableTargetTrust::kSuppressed:
      return "suppressed";
    case ExecutableTargetTrust::kTerminal:
      return "terminal";
  }
  return "terminal";
}

std::optional<ExecutableTargetFact> readExecutableTargetFact(
    const llvm::CallBase &call) {
  auto raw_target_pc = getInstructionU64Metadata(call, kExecutableTargetPc);
  if (!raw_target_pc) {
    if (auto *callee = call.getCalledFunction()) {
      if (callee->getName() == "__omill_missing_block_handler" &&
          call.arg_size() >= 1) {
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call.getArgOperand(0)))
          raw_target_pc = ci->getZExtValue();
      } else if (callee->getName() == "__remill_missing_block" &&
                 call.arg_size() >= 2) {
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call.getArgOperand(1)))
          raw_target_pc = ci->getZExtValue();
      }
      if (!raw_target_pc) {
        if (auto callee_fact = readExecutableTargetFact(*callee))
          raw_target_pc = callee_fact->raw_target_pc;
      }
    }
  }
  if (!raw_target_pc)
    return std::nullopt;

  ExecutableTargetFact fact;
  fact.raw_target_pc = *raw_target_pc;
  fact.effective_target_pc =
      getInstructionU64Metadata(call, kEffectiveTargetPc);
  fact.canonical_owner_pc =
      getInstructionU64Metadata(call, kCanonicalOwnerPc);
  fact.exact_fallthrough_target =
      getInstructionBoolMetadata(call, kExactFallthroughTarget);
  fact.invalidated_executable_entry =
      getInstructionBoolMetadata(call, kInvalidatedExecutableEntry);
  fact.invalidated_entry_source_pc =
      getInstructionU64Metadata(call, kInvalidatedEntrySourcePc);
  fact.invalidated_entry_failed_pc =
      getInstructionU64Metadata(call, kInvalidatedEntryFailedPc);

  if (auto kind = getInstructionStringMetadata(call, kExecutableTargetKind)) {
    fact.kind = kindFromString(*kind);
  } else {
    fact.kind = inferKind(fact);
  }
  if (auto trust = getInstructionStringMetadata(call, kExecutableTargetTrust)) {
    fact.trust = trustFromString(*trust);
  } else {
    fact.trust = inferTrust(fact);
  }

  return fact;
}

std::optional<ExecutableTargetFact> readExecutableTargetFact(
    const llvm::Function &function) {
  std::optional<uint64_t> raw_target_pc =
      getFunctionHexAttr(function, kExecutableTargetPc);
  if (!raw_target_pc) {
    uint64_t parsed = extractStructuralCodeTargetPC(function.getName());
    if (function.getName().starts_with("omill_executable_target_") && parsed != 0)
      raw_target_pc = parsed;
  }
  if (!raw_target_pc)
    return std::nullopt;

  ExecutableTargetFact fact;
  fact.raw_target_pc = *raw_target_pc;
  fact.effective_target_pc = getFunctionHexAttr(function, kEffectiveTargetPc);
  fact.canonical_owner_pc = getFunctionHexAttr(function, kCanonicalOwnerPc);
  fact.exact_fallthrough_target =
      getFunctionBoolAttr(function, kExactFallthroughTarget);
  fact.invalidated_executable_entry =
      getFunctionBoolAttr(function, kInvalidatedExecutableEntry);
  fact.invalidated_entry_source_pc =
      getFunctionHexAttr(function, kInvalidatedEntrySourcePc);
  fact.invalidated_entry_failed_pc =
      getFunctionHexAttr(function, kInvalidatedEntryFailedPc);

  if (auto kind = getFunctionStringAttr(function, kExecutableTargetKind)) {
    fact.kind = kindFromString(*kind);
  } else {
    fact.kind = inferKind(fact);
  }
  if (auto trust = getFunctionStringAttr(function, kExecutableTargetTrust)) {
    fact.trust = trustFromString(*trust);
  } else {
    fact.trust = inferTrust(fact);
  }

  return fact;
}

void writeExecutableTargetFact(llvm::CallBase &call,
                               const ExecutableTargetFact &fact) {
  auto &inst = static_cast<llvm::Instruction &>(call);
  setInstructionU64Metadata(inst, kExecutableTargetPc, fact.raw_target_pc);
  if (fact.effective_target_pc)
    setInstructionU64Metadata(inst, kEffectiveTargetPc, *fact.effective_target_pc);
  if (fact.canonical_owner_pc)
    setInstructionU64Metadata(inst, kCanonicalOwnerPc, *fact.canonical_owner_pc);
  if (fact.exact_fallthrough_target)
    setInstructionBoolMetadata(inst, kExactFallthroughTarget, true);
  if (fact.invalidated_executable_entry)
    setInstructionBoolMetadata(inst, kInvalidatedExecutableEntry, true);
  if (fact.invalidated_entry_source_pc) {
    setInstructionU64Metadata(inst, kInvalidatedEntrySourcePc,
                              *fact.invalidated_entry_source_pc);
  }
  if (fact.invalidated_entry_failed_pc) {
    setInstructionU64Metadata(inst, kInvalidatedEntryFailedPc,
                              *fact.invalidated_entry_failed_pc);
  }
  setInstructionStringMetadata(inst, kExecutableTargetKind, toString(fact.kind));
  setInstructionStringMetadata(inst, kExecutableTargetTrust,
                               toString(fact.trust));
}

void writeExecutableTargetFact(llvm::Function &function,
                               const ExecutableTargetFact &fact) {
  function.addFnAttr(kExecutableTargetPc, llvm::utohexstr(fact.raw_target_pc));
  maybeSetFunctionHexAttr(function, kEffectiveTargetPc, fact.effective_target_pc);
  maybeSetFunctionHexAttr(function, kCanonicalOwnerPc, fact.canonical_owner_pc);
  if (fact.exact_fallthrough_target)
    function.addFnAttr(kExactFallthroughTarget, "1");
  if (fact.invalidated_executable_entry)
    function.addFnAttr(kInvalidatedExecutableEntry, "1");
  maybeSetFunctionHexAttr(function, kInvalidatedEntrySourcePc,
                          fact.invalidated_entry_source_pc);
  maybeSetFunctionHexAttr(function, kInvalidatedEntryFailedPc,
                          fact.invalidated_entry_failed_pc);
  function.addFnAttr(kExecutableTargetKind, toString(fact.kind));
  function.addFnAttr(kExecutableTargetTrust, toString(fact.trust));
}

std::optional<ExecutableTargetFact> executableTargetFactFromDecision(
    const LiftTargetDecision &decision) {
  if (!decision.raw_target_pc)
    return std::nullopt;

  ExecutableTargetFact fact;
  fact.raw_target_pc = decision.raw_target_pc;
  fact.effective_target_pc = decision.effective_target_pc;
  fact.canonical_owner_pc = decision.owner_pc;
  fact.exact_fallthrough_target = decision.is_exact_fallthrough;
  fact.invalidated_executable_entry =
      decision.classification == LiftTargetClassification::kInvalidatedExecutableEntry;
  fact.invalidated_entry_source_pc = decision.invalidated_entry_source_pc;
  fact.invalidated_entry_failed_pc = decision.invalidated_entry_failed_pc;

  switch (decision.classification) {
    case LiftTargetClassification::kLiftableEntry:
      fact.kind = ExecutableTargetKind::kLiftableEntry;
      break;
    case LiftTargetClassification::kExactFallthroughEntry:
      fact.kind = ExecutableTargetKind::kExactFallthroughEntry;
      break;
    case LiftTargetClassification::kInvalidatedExecutableEntry:
      fact.kind = ExecutableTargetKind::kInvalidatedExecutableEntry;
      break;
    case LiftTargetClassification::kExecutablePlaceholder:
      fact.kind = ExecutableTargetKind::kExecutablePlaceholder;
      break;
    case LiftTargetClassification::kCanonicalOwner:
      fact.kind = ExecutableTargetKind::kCanonicalOwner;
      break;
    case LiftTargetClassification::kSuppress:
      fact.kind = ExecutableTargetKind::kSuppress;
      break;
    case LiftTargetClassification::kTerminal:
      fact.kind = ExecutableTargetKind::kTerminal;
      break;
  }

  switch (decision.trust) {
    case LiftTargetTrust::kTrustedEntry:
      fact.trust = ExecutableTargetTrust::kTrustedEntry;
      break;
    case LiftTargetTrust::kExactFallthrough:
      fact.trust = ExecutableTargetTrust::kExactFallthrough;
      break;
    case LiftTargetTrust::kNearbyOwner:
      fact.trust = ExecutableTargetTrust::kNearbyOwner;
      break;
    case LiftTargetTrust::kInvalidatedEntry:
      fact.trust = ExecutableTargetTrust::kInvalidatedEntry;
      break;
    case LiftTargetTrust::kUntrustedExecutable:
      fact.trust = ExecutableTargetTrust::kUntrustedExecutable;
      break;
    case LiftTargetTrust::kSuppressed:
      fact.trust = ExecutableTargetTrust::kSuppressed;
      break;
    case LiftTargetTrust::kTerminal:
      fact.trust = ExecutableTargetTrust::kTerminal;
      break;
  }

  return fact;
}

}  // namespace omill

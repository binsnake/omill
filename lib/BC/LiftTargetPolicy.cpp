#include "omill/BC/LiftTargetPolicy.h"

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Arch/ArchABI.h"

#include <algorithm>
#include <limits>

namespace omill {

namespace {

bool looksLikePlausibleX86FunctionEntry(const BinaryMemoryMap *memory_map,
                                        uint64_t pc) {
  if (!memory_map)
    return false;
  uint8_t buf[6] = {};
  if (!memory_map->read(pc, buf, sizeof(buf)))
    return false;
  if (buf[0] == 0x55 || buf[0] == 0x53 || buf[0] == 0x56 || buf[0] == 0x57)
    return true;
  if (buf[0] == 0x41 && buf[1] >= 0x50 && buf[1] <= 0x57)
    return true;
  if (buf[0] == 0x48 && buf[1] == 0x83 && buf[2] == 0xEC)
    return true;
  if (buf[0] == 0x48 && buf[1] == 0x81 && buf[2] == 0xEC)
    return true;
  if (buf[0] == 0x48 && buf[1] == 0x89 && buf[3] == 0x24 &&
      (buf[2] == 0x5C || buf[2] == 0x74 || buf[2] == 0x7C))
    return true;
  if (buf[0] == 0x4C && buf[1] == 0x89 && buf[3] == 0x24 &&
      (buf[2] == 0x44 || buf[2] == 0x4C || buf[2] == 0x54 ||
       buf[2] == 0x5C || buf[2] == 0x64 || buf[2] == 0x6C ||
       buf[2] == 0x74 || buf[2] == 0x7C))
    return true;
  return false;
}

bool isLikelyDesynchronizedLiftTarget(const BinaryMemoryMap *memory_map,
                                      uint64_t target_pc,
                                      std::optional<uint64_t> nearby_entry_pc,
                                      TargetArch arch) {
  if (!nearby_entry_pc.has_value() || *nearby_entry_pc >= target_pc)
    return false;

  const uint64_t delta = target_pc - *nearby_entry_pc;
  const uint64_t window = arch == TargetArch::kAArch64 ? 4 : 8;
  if (delta == 0 || delta > window)
    return false;

  auto raw_decodable = isDecodableLiftTargetEntry(memory_map, target_pc, arch);
  if (!raw_decodable.has_value() || *raw_decodable)
    return false;

  auto nearby_decodable =
      isDecodableLiftTargetEntry(memory_map, *nearby_entry_pc, arch);
  return nearby_decodable.has_value() && *nearby_decodable;
}

}  // namespace

bool LiftTargetDecision::shouldLift() const {
  return classification == LiftTargetClassification::kLiftableEntry ||
         classification == LiftTargetClassification::kExactFallthroughEntry ||
         classification == LiftTargetClassification::kCanonicalOwner;
}

bool LiftTargetDecision::shouldMaterializePlaceholder() const {
  return classification == LiftTargetClassification::kExecutablePlaceholder ||
         classification == LiftTargetClassification::kInvalidatedExecutableEntry;
}

LiftTargetPolicy::~LiftTargetPolicy() = default;

BinaryLiftTargetPolicy::BinaryLiftTargetPolicy(const BinaryMemoryMap *memory_map,
                                               TargetArch arch)
    : memory_map_(memory_map), arch_(arch) {}

LiftTargetDecision BinaryLiftTargetPolicy::ResolveLiftTarget(
    uint64_t, uint64_t raw_target_pc, LiftTargetEdgeKind) const {
  LiftTargetDecision decision;
  decision.raw_target_pc = raw_target_pc;

  if (!isExecutableLiftTarget(memory_map_, raw_target_pc)) {
    decision.classification = LiftTargetClassification::kTerminal;
    decision.trust = LiftTargetTrust::kTerminal;
    return decision;
  }

  const bool exact_fallthrough =
      arch_ == TargetArch::kX86_64 &&
      isExactX86DirectControlFlowFallthrough(memory_map_, raw_target_pc);
  auto canonical =
      canonicalizeLiftTargetForOverlap(memory_map_, raw_target_pc, arch_);

  if (!canonical.has_value()) {
    decision.classification = LiftTargetClassification::kSuppress;
    decision.trust = LiftTargetTrust::kSuppressed;
    return decision;
  }

  decision.effective_target_pc = *canonical;
  decision.is_exact_fallthrough = exact_fallthrough;

  if (*canonical != raw_target_pc) {
    decision.classification = LiftTargetClassification::kCanonicalOwner;
    decision.trust = LiftTargetTrust::kNearbyOwner;
    decision.owner_pc = *canonical;
    decision.fallback_pc = raw_target_pc;
    return decision;
  }

  if (exact_fallthrough) {
    decision.classification = LiftTargetClassification::kExactFallthroughEntry;
    decision.trust = LiftTargetTrust::kExactFallthrough;
    return decision;
  }

  auto decodable =
      isDecodableLiftTargetEntry(memory_map_, raw_target_pc, arch_);
  if (decodable.has_value() && *decodable) {
    decision.classification = LiftTargetClassification::kLiftableEntry;
    decision.trust = LiftTargetTrust::kTrustedEntry;
    return decision;
  }

  decision.classification = LiftTargetClassification::kExecutablePlaceholder;
  decision.trust = LiftTargetTrust::kUntrustedExecutable;
  return decision;
}

DecodeFailureDecision BinaryLiftTargetPolicy::ResolveDecodeFailure(
    uint64_t source_pc, uint64_t failed_pc, llvm::ArrayRef<uint64_t> known_entry_pcs,
    const DecodeFailureContext &) const {
  DecodeFailureDecision decision;
  decision.source_pc = source_pc;
  decision.failed_pc = failed_pc;

  if (!isExecutableLiftTarget(memory_map_, failed_pc)) {
    decision.action = DecodeFailureAction::kTerminal;
    decision.target.raw_target_pc = failed_pc;
    decision.target.classification = LiftTargetClassification::kTerminal;
    decision.target.trust = LiftTargetTrust::kTerminal;
    return decision;
  }

  if (arch_ == TargetArch::kX86_64) {
    const uint64_t distance =
        failed_pc >= source_pc ? failed_pc - source_pc : uint64_t(0);
    if (distance <= decodeFailureContinuationSearchWindow(arch_) &&
        (isLikelyX86CallMetadataWindow(memory_map_, source_pc) ||
         looksLikeSuspiciousX86EntryBytes(memory_map_, source_pc) ||
         isLikelyX86CallMetadataWindow(memory_map_, failed_pc) ||
         looksLikeSuspiciousX86EntryBytes(memory_map_, failed_pc))) {
      decision.action = DecodeFailureAction::kInvalidateEntry;
      decision.target.raw_target_pc = source_pc;
      decision.target.effective_target_pc = source_pc;
      decision.target.classification =
          LiftTargetClassification::kInvalidatedExecutableEntry;
      decision.target.trust = LiftTargetTrust::kInvalidatedEntry;
      decision.target.invalidated_entry_source_pc = source_pc;
      decision.target.invalidated_entry_failed_pc = failed_pc;
      return decision;
    }

    if (isLikelyX86CallMetadataWindow(memory_map_, failed_pc) ||
        looksLikeSuspiciousX86EntryBytes(memory_map_, failed_pc)) {
      const uint64_t window = decodeFailureContinuationSearchWindow(arch_);
      std::optional<uint64_t> best;
      uint64_t best_distance = std::numeric_limits<uint64_t>::max();
      for (uint64_t candidate_pc : known_entry_pcs) {
        if (!candidate_pc || candidate_pc == source_pc || candidate_pc >= failed_pc)
          continue;
        if (looksLikeSuspiciousX86EntryBytes(memory_map_, candidate_pc) ||
            isLikelyX86CallMetadataWindow(memory_map_, candidate_pc)) {
          continue;
        }
        const uint64_t distance = failed_pc - candidate_pc;
        if (distance == 0 || distance > window)
          continue;
        if (!best || distance < best_distance ||
            (distance == best_distance && candidate_pc > *best)) {
          best = candidate_pc;
          best_distance = distance;
        }
      }
      if (best.has_value()) {
        decision.action = DecodeFailureAction::kRedirectToTarget;
        decision.target.raw_target_pc = failed_pc;
        decision.target.effective_target_pc = *best;
        decision.target.classification = LiftTargetClassification::kCanonicalOwner;
        decision.target.trust = LiftTargetTrust::kNearbyOwner;
        decision.target.owner_pc = *best;
        decision.target.fallback_pc = failed_pc;
        return decision;
      }
    }
  }

  auto lift_decision =
      ResolveLiftTarget(source_pc, failed_pc,
                        LiftTargetEdgeKind::kDecodeFailureContinuation);
  if (lift_decision.classification == LiftTargetClassification::kCanonicalOwner &&
      lift_decision.effective_target_pc.has_value() &&
      *lift_decision.effective_target_pc != failed_pc) {
    decision.action = DecodeFailureAction::kRedirectToTarget;
    decision.target = std::move(lift_decision);
    return decision;
  }

  decision.action = DecodeFailureAction::kMaterializeExecutablePlaceholder;
  decision.target.raw_target_pc = failed_pc;
  decision.target.effective_target_pc = failed_pc;
  decision.target.classification =
      LiftTargetClassification::kExecutablePlaceholder;
  decision.target.trust = lift_decision.is_exact_fallthrough
                              ? LiftTargetTrust::kExactFallthrough
                              : LiftTargetTrust::kUntrustedExecutable;
  decision.target.is_exact_fallthrough = lift_decision.is_exact_fallthrough;
  decision.target.owner_pc = lift_decision.owner_pc;
  decision.target.fallback_pc = lift_decision.fallback_pc;
  return decision;
}

bool isExecutableLiftTarget(const BinaryMemoryMap *memory_map,
                            uint64_t target_pc) {
  return memory_map && target_pc != 0 && memory_map->isExecutable(target_pc, 1);
}

std::optional<bool> isDecodableLiftTargetEntry(
    const BinaryMemoryMap *memory_map, uint64_t target_pc, TargetArch arch) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      if (target_pc & 0x3)
        return false;
      uint8_t buf[4] = {};
      return memory_map->read(target_pc, buf, sizeof(buf));
    }
    case TargetArch::kX86_64:
    default:
      return canDecodeX86InstructionAt(*memory_map, target_pc);
  }
}

bool looksLikeSuspiciousX86EntryBytes(const BinaryMemoryMap *memory_map,
                                      uint64_t target_pc) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return false;
  uint8_t bytes[16] = {};
  if (!memory_map->read(target_pc, bytes, sizeof(bytes)))
    return false;

  auto is_suspicious = [](uint8_t byte) {
    switch (byte) {
      case 0x60:
      case 0x61:
      case 0x62:
      case 0x8E:
      case 0xC8:
      case 0xCA:
      case 0xCB:
      case 0xCE:
      case 0xCF:
      case 0xE0:
      case 0xE1:
      case 0xE2:
      case 0xE3:
      case 0xE4:
      case 0xE5:
      case 0xE6:
      case 0xE7:
      case 0xEC:
      case 0xED:
      case 0xEE:
      case 0xEF:
      case 0xF4:
      case 0xFA:
      case 0xFB:
        return true;
      default:
        return false;
    }
  };

  unsigned suspicious = 0;
  for (unsigned i = 0; i < sizeof(bytes); ++i) {
    if (bytes[i] == 0xC3 || bytes[i] == 0xC2 || bytes[i] == 0xE8 ||
        bytes[i] == 0xE9 || bytes[i] == 0xEB) {
      break;
    }
    if (is_suspicious(bytes[i]))
      ++suspicious;
  }
  return suspicious >= 2;
}

bool isLikelyX86CallMetadataWindow(const BinaryMemoryMap *memory_map,
                                   uint64_t target_pc) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return false;

  constexpr uint64_t kLookback = 16;
  constexpr uint64_t kWindow = 16;
  uint64_t start = target_pc > kLookback ? target_pc - kLookback : 1;
  for (uint64_t call_pc = start; call_pc < target_pc; ++call_pc) {
    uint8_t opcode = 0;
    if (!memory_map->read(call_pc, &opcode, sizeof(opcode)) || opcode != 0xE8)
      continue;
    uint64_t call_fallthrough = call_pc + 5;
    if (target_pc > call_pc && target_pc < call_fallthrough)
      return true;
    if (target_pc < call_fallthrough || target_pc > call_fallthrough + kWindow)
      continue;
    return true;
  }
  return false;
}

bool isExactX86DirectControlFlowFallthrough(const BinaryMemoryMap *memory_map,
                                            uint64_t target_pc) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return false;

  constexpr uint64_t kLookback = 16;
  uint64_t start = target_pc > kLookback ? target_pc - kLookback : 1;
  for (uint64_t pc = start; pc < target_pc; ++pc) {
    uint8_t bytes[2] = {};
    if (!memory_map->read(pc, bytes, sizeof(bytes)))
      continue;

    uint64_t fallthrough = 0;
    if (bytes[0] == 0xE8 || bytes[0] == 0xE9) {
      fallthrough = pc + 5;
    } else if (bytes[0] == 0xEB || (bytes[0] >= 0x70 && bytes[0] <= 0x7F) ||
               bytes[0] == 0xE3) {
      fallthrough = pc + 2;
    } else if (bytes[0] == 0x0F && bytes[1] >= 0x80 && bytes[1] <= 0x8F) {
      fallthrough = pc + 6;
    } else {
      continue;
    }

    if (fallthrough == target_pc)
      return true;
  }
  return false;
}

std::optional<uint64_t> recoverX86DirectControlFlowFallthrough(
    const BinaryMemoryMap *memory_map, uint64_t target_pc) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return std::nullopt;

  constexpr uint64_t kLookback = 16;
  uint64_t start = target_pc > kLookback ? target_pc - kLookback : 1;
  for (uint64_t pc = start; pc < target_pc; ++pc) {
    uint8_t bytes[2] = {};
    if (!memory_map->read(pc, bytes, sizeof(bytes)))
      continue;

    uint64_t fallthrough = 0;
    bool inside_immediate = false;
    if (bytes[0] == 0xE8 || bytes[0] == 0xE9) {
      fallthrough = pc + 5;
      inside_immediate = target_pc > pc && target_pc < fallthrough;
    } else if (bytes[0] == 0xEB || (bytes[0] >= 0x70 && bytes[0] <= 0x7F) ||
               bytes[0] == 0xE3) {
      fallthrough = pc + 2;
      inside_immediate = target_pc > pc && target_pc < fallthrough;
    } else if (bytes[0] == 0x0F && bytes[1] >= 0x80 && bytes[1] <= 0x8F) {
      fallthrough = pc + 6;
      inside_immediate = target_pc > pc && target_pc < fallthrough;
    }

    if (!inside_immediate)
      continue;
    if (!isExecutableLiftTarget(memory_map, fallthrough))
      continue;
    return fallthrough;
  }
  return std::nullopt;
}

std::optional<uint64_t> findNearbyExecutableLiftEntry(
    const BinaryMemoryMap *memory_map, uint64_t target_pc, TargetArch arch) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      auto aligned = target_pc & ~uint64_t(0x3);
      if (aligned == target_pc)
        return std::nullopt;
      auto decodable = isDecodableLiftTargetEntry(memory_map, aligned, arch);
      if (decodable.has_value() && *decodable)
        return aligned;
      return std::nullopt;
    }
    case TargetArch::kX86_64:
    default: {
      constexpr uint64_t kWindow = 64;
      uint64_t start = (target_pc > kWindow) ? (target_pc - kWindow) : 1;
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isExecutableLiftTarget(memory_map, pc))
          continue;
        auto decodable = isDecodableLiftTargetEntry(memory_map, pc, arch);
        if (decodable.has_value() && *decodable)
          return pc;
      }
      return std::nullopt;
    }
  }
}

std::optional<uint64_t> canonicalizeLiftTargetForOverlap(
    const BinaryMemoryMap *memory_map, uint64_t target_pc, TargetArch arch) {
  if (!isExecutableLiftTarget(memory_map, target_pc))
    return target_pc;

  if (arch == TargetArch::kX86_64) {
    if (auto fallthrough =
            recoverX86DirectControlFlowFallthrough(memory_map, target_pc)) {
      return *fallthrough;
    }
    const uint64_t window = 8;
    uint64_t start = (target_pc > window) ? (target_pc - window) : 1;
    std::optional<uint64_t> plausible_owner;
    for (uint64_t candidate = target_pc; candidate > start; --candidate) {
      uint64_t pc = candidate - 1;
      if (!isExecutableLiftTarget(memory_map, pc))
        continue;
      if (!looksLikePlausibleX86FunctionEntry(memory_map, pc))
        continue;
      plausible_owner = pc;
      auto next_pc = nextDecodableX86InstructionPC(*memory_map, pc);
      if (next_pc.has_value() && pc < target_pc && *next_pc > target_pc) {
        plausible_owner = pc;
      }
    }
    if (plausible_owner.has_value())
      return plausible_owner;
  }

  auto decodable = isDecodableLiftTargetEntry(memory_map, target_pc, arch);
  if (decodable.has_value() && *decodable)
    return target_pc;

  auto nearby_entry = findNearbyExecutableLiftEntry(memory_map, target_pc, arch);
  if (!nearby_entry)
    return target_pc;
  if (isLikelyDesynchronizedLiftTarget(memory_map, target_pc, nearby_entry,
                                       arch)) {
    return std::nullopt;
  }
  return nearby_entry;
}

uint64_t decodeFailureContinuationSearchWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 8;
    case TargetArch::kX86_64:
    default:
      return 32;
  }
}

std::unique_ptr<LiftTargetPolicy> createBinaryLiftTargetPolicy(
    const BinaryMemoryMap *memory_map, TargetArch arch) {
  return std::make_unique<BinaryLiftTargetPolicy>(memory_map, arch);
}

}  // namespace omill

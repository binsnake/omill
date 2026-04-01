#pragma once

#include <cstdint>
#include <optional>

#include "omill/BC/LiftTargetPolicy.h"

namespace llvm {
class CallBase;
class Function;
}  // namespace llvm

namespace omill {

enum class ExecutableTargetKind {
  kLiftableEntry,
  kExactFallthroughEntry,
  kInvalidatedExecutableEntry,
  kExecutablePlaceholder,
  kCanonicalOwner,
  kSuppress,
  kTerminal,
};

enum class ExecutableTargetTrust {
  kTrustedEntry,
  kExactFallthrough,
  kNearbyOwner,
  kInvalidatedEntry,
  kUntrustedExecutable,
  kSuppressed,
  kTerminal,
};

struct ExecutableTargetFact {
  uint64_t raw_target_pc = 0;
  std::optional<uint64_t> effective_target_pc;
  std::optional<uint64_t> canonical_owner_pc;
  ExecutableTargetKind kind = ExecutableTargetKind::kExecutablePlaceholder;
  ExecutableTargetTrust trust = ExecutableTargetTrust::kUntrustedExecutable;
  bool exact_fallthrough_target = false;
  bool invalidated_executable_entry = false;
  std::optional<uint64_t> invalidated_entry_source_pc;
  std::optional<uint64_t> invalidated_entry_failed_pc;

  bool operator==(const ExecutableTargetFact &other) const;
  bool operator!=(const ExecutableTargetFact &other) const {
    return !(*this == other);
  }
};

std::optional<ExecutableTargetFact> readExecutableTargetFact(
    const llvm::CallBase &call);
std::optional<ExecutableTargetFact> readExecutableTargetFact(
    const llvm::Function &function);

void writeExecutableTargetFact(llvm::CallBase &call,
                               const ExecutableTargetFact &fact);
void writeExecutableTargetFact(llvm::Function &function,
                               const ExecutableTargetFact &fact);

std::optional<ExecutableTargetFact> executableTargetFactFromDecision(
    const LiftTargetDecision &decision);

const char *toString(ExecutableTargetKind kind);
const char *toString(ExecutableTargetTrust trust);

}  // namespace omill

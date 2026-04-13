#pragma once

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/STLFunctionalExtras.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "omill/Analysis/VirtualModel/Types.h"
#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"

namespace llvm {
class Module;
}

namespace omill {

class IterativeLiftingSession;
class RemillProjectionLifter;

enum class OutputRootClosureSourceKind {
  kConstantCodeTarget,
  kConstantCalliTarget,
  kConstantDispatchTarget,
  kMissingBlockHandlerTarget,
  kInvalidatedExecutableTarget,
  kAnnotatedVmContinuationTarget,
  kVmUnresolvedContinuationTarget,
};

struct OutputRootClosureWorkItem {
  std::string owner_function;
  unsigned site_index = 0;
  std::optional<uint64_t> site_pc;
  uint64_t target_pc = 0;
  bool vip_symbolic = false;
  OutputRootClosureSourceKind source_kind =
      OutputRootClosureSourceKind::kConstantCodeTarget;
  std::optional<BoundaryFact> boundary;
  std::optional<ExecutableTargetFact> executable_target;
  std::string identity;
};

struct OutputRootClosureTargetSummary {
  std::vector<uint64_t> constant_code_targets;
  std::vector<uint64_t> constant_calli_targets;
  std::vector<uint64_t> constant_dispatch_targets;
  std::vector<uint64_t> annotated_vm_continuation_targets;
};

OutputRootClosureTargetSummary collectOutputRootClosureTargets(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc,
    bool include_defined_targets = false);

std::vector<OutputRootClosureWorkItem> collectOutputRootClosureWorkItems(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc,
    bool include_defined_targets = false);

std::vector<uint64_t> collectVmUnresolvedContinuationTargets(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc);

std::vector<OutputRootClosureWorkItem> collectVmUnresolvedContinuationWorkItems(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc);

std::vector<uint64_t> collectLateLiftableOutputRootClosureTargets(
    const OutputRootClosureTargetSummary &summary,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<bool(uint64_t)> is_executable_target,
    llvm::function_ref<bool(uint64_t)> should_skip_target);

unsigned lateLiftTargets(llvm::ArrayRef<uint64_t> targets,
                         RemillProjectionLifter &projection_lifter,
                         IterativeLiftingSession &session,
                         llvm::function_ref<bool(uint64_t)> has_defined_target,
                         llvm::function_ref<bool(uint64_t)> is_executable_target,
                         llvm::function_ref<bool(uint64_t)> should_skip_target);

}  // namespace omill

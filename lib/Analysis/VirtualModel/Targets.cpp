#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>

#include <limits>
#include <optional>

#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/ProtectedBoundaryUtils.h"

namespace omill::virtual_model::detail {

namespace {

static uint64_t nearbyEntrySearchWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 4;
    case TargetArch::kX86_64:
    default:
      return 64;
  }
}

static uint64_t overlapDesyncWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 4;
    case TargetArch::kX86_64:
    default:
      return 8;
  }
}

static bool looksLikePlausibleX86FunctionEntry(
    const BinaryMemoryMap &binary_memory, uint64_t pc) {
  uint8_t buf[6] = {};
  if (!binary_memory.read(pc, buf, sizeof(buf)))
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

static std::string normalizeBoundaryName(llvm::StringRef name) {
  return name.lower();
}

static std::string syntheticBoundaryName(uint64_t entry_va) {
  return normalizeBoundaryName(std::string("vm_entry_") +
                               llvm::utohexstr(entry_va));
}

static const VirtualBoundaryInfo *lookupBoundaryByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va) {
  for (const auto &boundary : model.boundaries()) {
    if (boundary.entry_va.has_value() && *boundary.entry_va == entry_va)
      return &boundary;
  }
  return nullptr;
}

}  // namespace

std::optional<uint64_t> inferLiftedCallContinuationPc(llvm::CallBase &call) {
  llvm::Value *continuation_input = &call;
  llvm::CallBase *intermediate_lifted_call = nullptr;

  for (auto *I = call.getNextNode(); I; I = I->getNextNode()) {
    if (auto *next_call = llvm::dyn_cast<llvm::CallBase>(I)) {
      auto *next_callee = next_call->getCalledFunction();
      if (!next_callee || !hasLiftedSignature(*next_callee))
        continue;
      auto *next_call_inst = llvm::dyn_cast<llvm::CallInst>(next_call);
      if (next_call_inst &&
          next_call_inst->getTailCallKind() == llvm::CallInst::TCK_MustTail &&
          next_call->arg_size() >= 3 &&
          next_call->getArgOperand(2) == continuation_input) {
        auto *pc = llvm::dyn_cast<llvm::ConstantInt>(next_call->getArgOperand(1));
        if (!pc)
          return std::nullopt;
        return pc->getZExtValue();
      }

      if (!intermediate_lifted_call) {
        intermediate_lifted_call = next_call;
        continuation_input = intermediate_lifted_call;
      }
    }

    if (I->isTerminator())
      break;
  }

  return std::nullopt;
}

const VirtualHandlerSummary *lookupHandlerByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va) {
  for (const auto &handler : model.handlers()) {
    if (handler.entry_va.has_value() && *handler.entry_va == entry_va)
      return &handler;
  }
  return nullptr;
}

bool isTargetMapped(const BinaryMemoryMap &binary_memory, uint64_t target_pc) {
  if (target_pc == 0)
    return false;
  uint8_t byte = 0;
  return binary_memory.read(target_pc, &byte, 1);
}

bool isTargetExecutable(const BinaryMemoryMap &binary_memory,
                        uint64_t target_pc) {
  if (target_pc == 0)
    return false;
  return binary_memory.isExecutable(target_pc, 1);
}

const BinaryMemoryMap::ImportEntry *lookupImportTarget(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc) {
  if (!target_pc)
    return nullptr;
  return binary_memory.lookupImport(target_pc);
}

TargetArch targetArchForModule(llvm::Module &M) {
  TargetArch arch = TargetArch::kX86_64;

  if (auto *md = M.getModuleFlag("omill.target_arch")) {
    if (auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(md))
      arch = static_cast<TargetArch>(ci->getZExtValue());
  }
  return arch;
}

std::optional<bool> isTargetDecodableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch arch) {
  if (!isTargetExecutable(binary_memory, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      if (target_pc & 0x3)
        return false;
      uint8_t buf[4] = {};
      return binary_memory.read(target_pc, buf, sizeof(buf));
    }
    case TargetArch::kX86_64:
    default:
      return canDecodeX86InstructionAt(binary_memory, target_pc);
  }
}

const VirtualHandlerSummary *findNearbyLiftedHandlerEntry(
    const VirtualMachineModel &model, uint64_t target_pc, TargetArch arch) {
  const auto window = nearbyEntrySearchWindow(arch);
  const VirtualHandlerSummary *best = nullptr;
  uint64_t best_distance = std::numeric_limits<uint64_t>::max();
  for (const auto &handler : model.handlers()) {
    if (!handler.entry_va.has_value())
      continue;
    const auto entry_va = *handler.entry_va;
    uint64_t distance = 0;
    if (entry_va > target_pc) {
      distance = entry_va - target_pc;
    } else {
      distance = target_pc - entry_va;
    }
    if (distance == 0 || distance > window)
      continue;
    if (!best || distance < best_distance ||
        (distance == best_distance && *best->entry_va > entry_va)) {
      best = &handler;
      best_distance = distance;
    }
  }
  return best;
}

std::optional<uint64_t> findNearbyExecutableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch arch) {
  if (!isTargetExecutable(binary_memory, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      auto aligned = target_pc & ~uint64_t(0x3);
      if (aligned == target_pc)
        return std::nullopt;
      auto decodable = isTargetDecodableEntry(binary_memory, aligned, arch);
      if (decodable.has_value() && *decodable)
        return aligned;
      return std::nullopt;
    }
    case TargetArch::kX86_64:
    default: {
      const uint64_t kWindow = nearbyEntrySearchWindow(arch);
      uint64_t start = (target_pc > kWindow) ? (target_pc - kWindow) : 1;
      std::optional<uint64_t> overlapping_owner_pc;
      std::optional<uint64_t> plausible_overlapping_owner_pc;
      std::optional<uint64_t> nearest_decodable_pc;
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isTargetExecutable(binary_memory, pc))
          continue;
        if (pc < target_pc &&
            (target_pc - pc) <= overlapDesyncWindow(TargetArch::kX86_64) &&
            looksLikePlausibleX86FunctionEntry(binary_memory, pc) &&
            !plausible_overlapping_owner_pc.has_value()) {
          plausible_overlapping_owner_pc = pc;
        }
        auto next_pc = nextDecodableX86InstructionPC(binary_memory, pc);
        if (next_pc.has_value() && pc < target_pc && *next_pc > target_pc &&
            !overlapping_owner_pc.has_value()) {
          overlapping_owner_pc = pc;
          if (looksLikePlausibleX86FunctionEntry(binary_memory, pc) &&
              !plausible_overlapping_owner_pc.has_value()) {
            plausible_overlapping_owner_pc = pc;
          }
        }
      }
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isTargetExecutable(binary_memory, pc))
          continue;
        auto decodable = isTargetDecodableEntry(binary_memory, pc, arch);
        if (decodable.has_value() && *decodable) {
          nearest_decodable_pc = pc;
          break;
        }
      }
      if (nearest_decodable_pc.has_value())
        return nearest_decodable_pc;
      if (plausible_overlapping_owner_pc.has_value())
        return plausible_overlapping_owner_pc;
      if (overlapping_owner_pc.has_value())
        return overlapping_owner_pc;
      return std::nullopt;
    }
  }
}

bool isLikelyDisassemblyDesyncTarget(const BinaryMemoryMap &binary_memory,
                                     uint64_t target_pc,
                                     std::optional<uint64_t> nearby_entry_pc,
                                     TargetArch arch) {
  if (!nearby_entry_pc.has_value())
    return false;
  if (target_pc == 0 || *nearby_entry_pc == 0 || *nearby_entry_pc >= target_pc)
    return false;

  const uint64_t delta = target_pc - *nearby_entry_pc;
  if (delta == 0 || delta > overlapDesyncWindow(arch))
    return false;

  auto raw_target_decodable =
      isTargetDecodableEntry(binary_memory, target_pc, arch);
  if (!raw_target_decodable.has_value() || *raw_target_decodable)
    return false;

  auto nearby_entry_decodable =
      isTargetDecodableEntry(binary_memory, *nearby_entry_pc, arch);
  return nearby_entry_decodable.has_value() && *nearby_entry_decodable;
}

std::optional<std::string> resolveBoundaryNameForTarget(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    uint64_t pc) {
  if (const auto *boundary = lookupBoundaryByEntryVA(model, pc))
    return normalizeBoundaryName(boundary->name);

  auto fallback_name = syntheticBoundaryName(pc);
  if (const auto *boundary = model.lookupBoundary(fallback_name))
    return normalizeBoundaryName(boundary->name);

  if (auto boundary = classifyProtectedBoundary(binary_memory, pc)) {
    if (const auto *existing =
            lookupBoundaryByEntryVA(model, boundary->entry_va)) {
      return normalizeBoundaryName(existing->name);
    }
    return syntheticBoundaryName(boundary->entry_va);
  }

  return std::nullopt;
}

}  // namespace omill::virtual_model::detail

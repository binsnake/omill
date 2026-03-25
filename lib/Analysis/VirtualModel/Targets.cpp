#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>

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
  for (const auto &handler : model.handlers()) {
    if (!handler.entry_va.has_value())
      continue;
    const auto entry_va = *handler.entry_va;
    if (entry_va >= target_pc)
      continue;
    if ((target_pc - entry_va) > window)
      continue;
    if (!best || *best->entry_va < entry_va)
      best = &handler;
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
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isTargetExecutable(binary_memory, pc))
          continue;
        auto decodable = isTargetDecodableEntry(binary_memory, pc, arch);
        if (decodable.has_value() && *decodable)
          return pc;
      }
      return std::nullopt;
    }
  }
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

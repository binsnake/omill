#include "omill/Analysis/RegisterRoleMap.h"
#include "omill/Analysis/VirtualModel/Analysis.h"

#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Module.h>

namespace omill {

// ============================================================================
// RegisterRoleMap
// ============================================================================

void RegisterRoleMap::seedFromStateLayout(const llvm::DataLayout &DL,
                                          const llvm::Module &M) {
  // x86-64 State struct well-known offsets (from remill's State.h).
  // GPR section starts at offset 2208, each register is 16 bytes apart
  // (8 bytes value + 8 bytes volatile padding).
  //
  // RSP: offset 2312, 8 bytes.
  bind(2312, 8, RegisterRole::kRSP, "RSP");

  // RIP is not stored at a fixed State offset — it's the function's %pc
  // argument (arg1), which the lifter folds to a constant at lift time.
  // We record offset 0 as a sentinel to indicate "see %pc argument".
  // This lets consumers know that RIP tracking is available even though
  // it doesn't live in the State struct in the usual way.
}

void RegisterRoleMap::refineFromVirtualModel(
    const VirtualMachineModel &model) {
  // Find VIP: scan handlers for the first canonical_vip with a slot_id.
  for (auto &handler : model.handlers()) {
    auto &vip = handler.canonical_vip;
    if (!vip.slot_id)
      continue;
    auto *slot = model.lookupSlot(*vip.slot_id);
    if (!slot || slot->offset < 0)
      continue;
    // Only bind if we don't already have a VIP binding.
    if (!bindingForRole(RegisterRole::kVIP)) {
      bind(static_cast<unsigned>(slot->offset), slot->width,
           RegisterRole::kVIP, slot->base_name);
    }
    break;
  }

  // Find VSP: scan handlers for stack owners with kVmStackRootSlot kind.
  for (auto &handler : model.handlers()) {
    for (auto &owner : handler.stack_owners) {
      if (owner.kind != VirtualStackOwnerKind::kVmStackRootSlot)
        continue;
      if (!owner.owner_slot_id)
        continue;
      auto *slot = model.lookupSlot(*owner.owner_slot_id);
      if (!slot || slot->offset < 0)
        continue;
      if (!bindingForRole(RegisterRole::kVSP)) {
        bind(static_cast<unsigned>(slot->offset), slot->width,
             RegisterRole::kVSP, slot->base_name);
      }
      return;  // found VSP, done
    }
  }
}

void RegisterRoleMap::bind(unsigned state_offset, unsigned width,
                           RegisterRole role,
                           llvm::StringRef canonical_name) {
  offset_to_role_[state_offset] = RegisterRoleBinding{
      role, state_offset, width, canonical_name.str()};
}

std::optional<RegisterRole> RegisterRoleMap::roleAt(unsigned offset) const {
  auto it = offset_to_role_.find(offset);
  if (it == offset_to_role_.end())
    return std::nullopt;
  return it->second.role;
}

const RegisterRoleBinding *RegisterRoleMap::bindingForRole(
    RegisterRole role) const {
  for (auto &[off, binding] : offset_to_role_)
    if (binding.role == role)
      return &binding;
  return nullptr;
}

const RegisterRoleBinding *RegisterRoleMap::bindingAt(unsigned offset) const {
  auto it = offset_to_role_.find(offset);
  if (it == offset_to_role_.end())
    return nullptr;
  return &it->second;
}

// ============================================================================
// RegisterRoleMapAnalysis
// ============================================================================

llvm::AnalysisKey RegisterRoleMapAnalysis::Key;

RegisterRoleMapAnalysis::Result RegisterRoleMapAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  Result result;
  result.map.seedFromStateLayout(M.getDataLayout(), M);
  return result;
}

}  // namespace omill

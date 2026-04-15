#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <optional>
#include <string>

namespace llvm {
class DataLayout;
class Module;
}  // namespace llvm

namespace omill {

class VirtualMachineModel;

/// Semantic role of a State struct offset in the context of devirtualization.
enum class RegisterRole : uint8_t {
  kNone,
  kRIP,        ///< Native program counter (lifted %pc argument)
  kRSP,        ///< Native stack pointer
  kVIP,        ///< Virtual instruction pointer (VM bytecode address)
  kVSP,        ///< Virtual stack pointer
  kReturnPC,   ///< Return address slot (RETURN_PC)
};

/// Associates a State struct offset with its semantic role.
struct RegisterRoleBinding {
  RegisterRole role = RegisterRole::kNone;
  unsigned state_offset = 0;
  unsigned width = 0;  // in bytes
  std::string canonical_name;
};

/// Module-level map from State struct byte offsets to their semantic roles.
///
/// Initially seeded with static x86-64 layout knowledge (RSP, RIP).
/// Refined later when the VirtualMachineModel identifies VIP/VSP slots.
/// Never invalidated — persists across all pass invocations.
class RegisterRoleMap {
 public:
  /// Seed from static x86-64 State layout knowledge.
  void seedFromStateLayout(const llvm::DataLayout &DL, const llvm::Module &M);

  /// Refine roles from the VirtualMachineModel's slot and stack owner
  /// summaries.  Called after each VirtualMachineModelAnalysis run.
  /// Identifies VIP from the canonical handler VIP slot, and VSP from
  /// stack owners with kVmStackRootSlot kind.
  void refineFromVirtualModel(const VirtualMachineModel &model);

  /// Bind a specific offset to a role.  Overwrites any existing binding.
  void bind(unsigned state_offset, unsigned width, RegisterRole role,
            llvm::StringRef canonical_name);

  /// Query the role at a given State byte offset.
  std::optional<RegisterRole> roleAt(unsigned offset) const;

  /// Get the binding for a role, if any.
  const RegisterRoleBinding *bindingForRole(RegisterRole role) const;

  /// Get the binding at an offset, if any.
  const RegisterRoleBinding *bindingAt(unsigned offset) const;

  bool empty() const { return offset_to_role_.empty(); }

 private:
  llvm::DenseMap<unsigned, RegisterRoleBinding> offset_to_role_;
};

/// Module analysis providing the RegisterRoleMap.
///
/// The result is never invalidated — the map is seeded on first run and
/// refined in-place by subsequent passes (e.g. after VirtualMachineModel
/// identifies VIP/VSP slots).
class RegisterRoleMapAnalysis
    : public llvm::AnalysisInfoMixin<RegisterRoleMapAnalysis> {
  friend llvm::AnalysisInfoMixin<RegisterRoleMapAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  struct Result {
    RegisterRoleMap map;

    /// Never invalidated — the map accumulates knowledge monotonically.
    bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                    llvm::ModuleAnalysisManager::Invalidator &) {
      return false;
    }
  };

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);
};

}  // namespace omill

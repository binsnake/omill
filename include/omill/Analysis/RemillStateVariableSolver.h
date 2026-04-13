#pragma once

#include <cstdint>
#include <optional>
#include <string>

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"

namespace llvm {
class CallBase;
class Function;
class Instruction;
class Module;
}  // namespace llvm

namespace omill {

enum class SolvedIntegerValueKind : uint8_t {
  kUnknown = 0,
  kConstant,
  kSet,
};

struct SolvedIntegerValue {
  SolvedIntegerValueKind kind = SolvedIntegerValueKind::kUnknown;
  unsigned bit_width = 0;
  llvm::SmallVector<uint64_t, 8> values;

  bool empty() const { return values.empty(); }
  std::optional<uint64_t> constant() const;
  std::optional<bool> constantBool() const;
};

enum class RemillControlTransferKind : uint8_t {
  kUnknown = 0,
  kConditionalBranch,
  kIndirectJump,
  kIndirectCall,
  kDirectJump,
  kDirectCall,
};

struct RemillControlTransferSolution {
  uint64_t control_pc = 0;
  RemillControlTransferKind kind = RemillControlTransferKind::kUnknown;
  SolvedIntegerValue transfer_value;
  std::optional<bool> branch_taken;
  llvm::SmallVector<uint64_t, 8> possible_target_pcs;
  llvm::StringMap<SolvedIntegerValue> named_state_values;
};

class RemillStateVariableSolver {
 public:
  explicit RemillStateVariableSolver(llvm::Module &M);

  std::optional<RemillControlTransferSolution> solveControlTransfer(
      llvm::Function &F, uint64_t control_pc);
  std::optional<SolvedIntegerValue> solveStateFieldBeforeControlTransfer(
      llvm::Function &F, uint64_t control_pc, llvm::StringRef field_name);

  bool annotateSolvedControlTransfer(
      llvm::Function &F, uint64_t control_pc,
      RemillControlTransferSolution *solution_out = nullptr);

 private:
  llvm::Module &module_;
};

std::optional<llvm::SmallVector<uint64_t, 8>> readSolvedTargetSet(
    const llvm::CallBase &call);
void writeSolvedTargetSet(llvm::CallBase &call,
                          llvm::ArrayRef<uint64_t> targets);

std::optional<bool> readSolvedBranchTaken(const llvm::Instruction &inst);
void writeSolvedBranchTaken(llvm::Instruction &inst, bool taken);

}  // namespace omill

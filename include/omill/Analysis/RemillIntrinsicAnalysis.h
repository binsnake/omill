#pragma once

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

namespace llvm {
class CallInst;
class Function;
}  // namespace llvm

namespace omill {

/// Result of analyzing a function for remill intrinsic calls.
/// Passes use this to efficiently find calls they need to lower.
struct RemillIntrinsicInfo {
  llvm::SmallVector<llvm::CallInst *, 8> read_memory;
  llvm::SmallVector<llvm::CallInst *, 8> write_memory;
  llvm::SmallVector<llvm::CallInst *, 4> flag_computations;
  llvm::SmallVector<llvm::CallInst *, 4> comparisons;
  llvm::SmallVector<llvm::CallInst *, 4> undefined_values;
  llvm::SmallVector<llvm::CallInst *, 2> control_flow;  // call/ret/jump
  llvm::SmallVector<llvm::CallInst *, 2> hyper_calls;
  llvm::SmallVector<llvm::CallInst *, 2> barriers;
  llvm::SmallVector<llvm::CallInst *, 2> atomics;
  llvm::SmallVector<llvm::CallInst *, 2> fetch_and_ops;
  llvm::SmallVector<llvm::CallInst *, 2> delay_slots;
  llvm::SmallVector<llvm::CallInst *, 2> fpu_ops;
  llvm::SmallVector<llvm::CallInst *, 2> io_ports;
  llvm::SmallVector<llvm::CallInst *, 2> x86_specific;

  /// Any inline asm calls that look like remill's volatile barriers.
  llvm::SmallVector<llvm::CallInst *, 16> volatile_barriers;

  bool hasAnyIntrinsics() const {
    return !read_memory.empty() || !write_memory.empty() ||
           !flag_computations.empty() || !comparisons.empty() ||
           !undefined_values.empty() || !control_flow.empty() ||
           !hyper_calls.empty() || !barriers.empty() || !atomics.empty() ||
           !fetch_and_ops.empty() || !delay_slots.empty() || !fpu_ops.empty() ||
           !io_ports.empty() || !x86_specific.empty() ||
           !volatile_barriers.empty();
  }
};

/// New-PM analysis pass that scans a function for all remill intrinsic calls
/// and categorizes them. Other passes request this analysis to find the calls
/// they need to transform.
class RemillIntrinsicAnalysis
    : public llvm::AnalysisInfoMixin<RemillIntrinsicAnalysis> {
  friend llvm::AnalysisInfoMixin<RemillIntrinsicAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = RemillIntrinsicInfo;

  Result run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);
};

}  // namespace omill

#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>

namespace llvm {
class Function;
class Module;
}  // namespace llvm

namespace omill {

/// Module-level map from entry PC to lifted function.
/// Built once by scanning all functions that match the lifted signature
/// (ptr, i64, ptr) -> ptr, excluding __remill_*/__omill_*/_native prefixes.
class LiftedFunctionMap {
 public:
  /// Look up a lifted function by its entry PC.
  llvm::Function *lookup(uint64_t pc) const {
    auto it = pc_to_func_.find(pc);
    return it != pc_to_func_.end() ? it->second : nullptr;
  }

  /// Check if a function is a known lifted function.
  bool isLifted(const llvm::Function *F) const {
    return lifted_set_.count(F);
  }

  /// Number of lifted functions found.
  size_t size() const { return pc_to_func_.size(); }

  /// Insert a newly-lifted function into the map.
  /// Used by IterativeTargetResolution after auto-lifting.
  void insert(uint64_t pc, llvm::Function *F) {
    pc_to_func_[pc] = F;
    lifted_set_.insert(F);
  }

  /// LLVM analysis invalidation — the map is updated incrementally
  /// via insert(), so it is never invalidated by the framework.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  friend class LiftedFunctionAnalysis;
  llvm::DenseMap<uint64_t, llvm::Function *> pc_to_func_;
  llvm::DenseSet<const llvm::Function *> lifted_set_;
};

/// Module analysis that builds a LiftedFunctionMap.
class LiftedFunctionAnalysis
    : public llvm::AnalysisInfoMixin<LiftedFunctionAnalysis> {
  friend llvm::AnalysisInfoMixin<LiftedFunctionAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = LiftedFunctionMap;

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

}  // namespace omill

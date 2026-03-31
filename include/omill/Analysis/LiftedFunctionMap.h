#pragma once

#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <llvm/ADT/Twine.h>
#include <string>
#include <unordered_map>
#include <unordered_set>

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
    if (!module_)
      return nullptr;
    auto it = pc_to_name_.find(pc);
    if (it != pc_to_name_.end()) {
      if (auto *fn = module_->getFunction(it->second))
        return fn;
    }

    for (llvm::StringRef prefix : {"sub_", "blk_", "block_"}) {
      std::string name = (prefix + llvm::Twine::utohexstr(pc)).str();
      if (auto *fn = module_->getFunction(name); fn && !fn->isDeclaration())
        return fn;
    }
    return nullptr;
  }

  /// Check if a function is a known lifted function.
  bool isLifted(const llvm::Function *F) const {
    return F && lifted_names_.count(F->getName().str());
  }

  /// Number of lifted functions found.
  size_t size() const { return pc_to_name_.size(); }

  /// Insert a newly-lifted function into the map.
  /// Used by IterativeTargetResolution after auto-lifting.
  void insert(uint64_t pc, llvm::Function *F) {
    if (!F)
      return;
    module_ = F->getParent();
    auto name = F->getName().str();
    pc_to_name_[pc] = name;
    lifted_names_.insert(std::move(name));
  }

  /// LLVM analysis invalidation. Entries are keyed by function name and
  /// re-resolved through the owning module, so the cache tolerates module
  /// rewrites that erase/recreate functions with the same lifted names.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  friend class LiftedFunctionAnalysis;
  llvm::Module *module_ = nullptr;
  std::unordered_map<uint64_t, std::string> pc_to_name_;
  std::unordered_set<std::string> lifted_names_;
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

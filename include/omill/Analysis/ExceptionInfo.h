#pragma once

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

#include <algorithm>
#include <cstdint>
#include <vector>

namespace llvm {
class Module;
}  // namespace llvm

namespace omill {

/// A single .pdata RUNTIME_FUNCTION entry parsed from a PE binary.
struct RuntimeFunctionEntry {
  uint64_t begin_va;    // Function start VA (ImageBase + BeginAddress RVA)
  uint64_t end_va;      // Function end VA
  uint64_t handler_va;  // Exception handler VA (0 if none)
};

/// Provides structured exception handling metadata parsed from PE .pdata.
///
/// The consumer populates this before running the pipeline (same pattern
/// as BinaryMemoryMap). Passes query it to resolve forced exceptions
/// (ud2, int3) to their SEH handlers.
class ExceptionInfo {
 public:
  /// Add a parsed RUNTIME_FUNCTION entry.
  void addEntry(RuntimeFunctionEntry entry) {
    entries_.push_back(entry);
    sorted_ = false;
  }

  /// Look up the RUNTIME_FUNCTION covering a given VA (binary search).
  /// Returns nullptr if no entry covers this address.
  const RuntimeFunctionEntry *lookup(uint64_t va) const {
    ensureSorted();
    // Binary search for the entry where begin_va <= va < end_va.
    auto it = std::upper_bound(
        entries_.begin(), entries_.end(), va,
        [](uint64_t v, const RuntimeFunctionEntry &e) {
          return v < e.begin_va;
        });
    if (it == entries_.begin())
      return nullptr;
    --it;
    if (va >= it->begin_va && va < it->end_va)
      return &(*it);
    return nullptr;
  }

  /// Return unique handler VAs (for auto-lifting).
  std::vector<uint64_t> getHandlerVAs() const {
    std::vector<uint64_t> result;
    for (const auto &e : entries_) {
      if (e.handler_va != 0)
        result.push_back(e.handler_va);
    }
    std::sort(result.begin(), result.end());
    result.erase(std::unique(result.begin(), result.end()), result.end());
    return result;
  }

  bool empty() const { return entries_.empty(); }

  /// LLVM analysis invalidation -- exception info is always valid.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  void ensureSorted() const {
    if (!sorted_) {
      auto &self = const_cast<ExceptionInfo &>(*this);
      std::sort(self.entries_.begin(), self.entries_.end(),
                [](const RuntimeFunctionEntry &a,
                   const RuntimeFunctionEntry &b) {
                  return a.begin_va < b.begin_va;
                });
      self.sorted_ = true;
    }
  }

  llvm::SmallVector<RuntimeFunctionEntry, 64> entries_;
  bool sorted_ = false;
};

/// Module-level analysis providing ExceptionInfo.
///
/// Consumer registers this with a pre-built ExceptionInfo (same pattern
/// as BinaryMemoryAnalysis). If not registered, passes get an empty
/// ExceptionInfo and gracefully degrade.
class ExceptionInfoAnalysis
    : public llvm::AnalysisInfoMixin<ExceptionInfoAnalysis> {
  friend llvm::AnalysisInfoMixin<ExceptionInfoAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = ExceptionInfo;

  ExceptionInfoAnalysis() = default;

  /// Construct with a pre-built exception info.
  explicit ExceptionInfoAnalysis(ExceptionInfo info)
      : info_(std::move(info)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);

 private:
  ExceptionInfo info_;
};

}  // namespace omill

#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <optional>
#include <vector>

namespace llvm {
class Module;
}  // namespace llvm

namespace omill {

class BinaryMemoryMap;
class VMHandlerChainSolver;

/// Extracted VM handler dispatch graph from binary byte pattern scanning.
///
/// EAC-style hash-threaded interpreter VMs use a dispatch epilogue pattern:
///   mov eax, <RVA32>; add rax, [r12+0xE0]; jmp rax
/// to chain handler execution.  This class scans binary memory for these
/// patterns and builds a graph of handler entry VAs and their dispatch targets.
///
/// This is a plain data structure, not an LLVM analysis.  Use
/// VMHandlerGraphAnalysis to make it available through the pass manager.
class VMHandlerGraph {
 public:
  VMHandlerGraph() = default;

  /// Construct with metadata only (no byte-pattern scanning).
  /// Use with mergeChainResults() to populate from a chain solver.
  VMHandlerGraph(uint64_t image_base, uint64_t vmenter_va,
                 uint64_t vmexit_va)
      : image_base_(image_base),
        vmenter_va_(vmenter_va),
        vmexit_va_(vmexit_va) {}

  /// Construct by scanning binary memory for dispatch patterns.
  ///
  /// \param mem      Binary memory map with all loaded sections.
  /// \param image_base  PE image base address.
  /// \param vmenter_va  VA of the VM entry function (context save).
  /// \param vmexit_va   VA of the VM exit function (context restore).
  VMHandlerGraph(const BinaryMemoryMap &mem, uint64_t image_base,
                 uint64_t vmenter_va, uint64_t vmexit_va);

  /// All discovered handler entry VAs (sorted, deduplicated).
  const std::vector<uint64_t> &handlerEntries() const {
    return handler_entries_;
  }

  /// All unique dispatch target VAs (superset of handler entries).
  const std::vector<uint64_t> &allTargetVAs() const {
    return all_target_vas_;
  }

  /// For a dispatch instruction at binary addr X, get the resolved target VA.
  std::optional<uint64_t> getDispatchTarget(uint64_t dispatch_addr) const;

  /// Get all dispatch target VAs for a handler starting at the given VA.
  /// Uses binary address ranges to associate dispatch sites with handlers.
  llvm::SmallVector<uint64_t, 4> getHandlerTargets(uint64_t handler_va) const;

  /// Get the RVA (relative to image base) for a dispatch at binary addr X.
  std::optional<uint32_t> getDispatchRVA(uint64_t dispatch_addr) const;

  /// Map from RVA to resolved target VA.  Used to match IR constants to
  /// known dispatch targets without needing binary address correspondence.
  std::optional<uint64_t> resolveRVA(uint32_t rva) const;

  uint64_t imageBase() const { return image_base_; }
  uint64_t vmenterVA() const { return vmenter_va_; }
  uint64_t vmexitVA() const { return vmexit_va_; }

  bool isVMHandler(uint64_t va) const { return handler_set_.count(va); }
  bool empty() const { return handler_entries_.empty(); }

  /// Number of dispatch sites found in the binary.
  size_t numDispatchSites() const { return dispatch_targets_.size(); }

  /// Merge results from the VMHandlerChainSolver into this graph.
  ///
  /// For each chain entry that has resolved successors, adds:
  ///   - handler_va as a handler entry
  ///   - each successor as a handler entry + dispatch target
  ///   - handler_va → successor mapping in chain_targets_
  void mergeChainResults(const VMHandlerChainSolver &solver);

  /// Get chain-solved successor VAs for a handler.
  llvm::SmallVector<uint64_t, 2> getChainTargets(uint64_t handler_va) const;

  /// LLVM analysis invalidation — the graph is immutable once built.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  /// Scan binary memory for dispatch byte patterns.
  void scanDispatchPatterns(const BinaryMemoryMap &mem);

  /// Scan for call/jmp instructions targeting vmenter_va to find initial
  /// handler entries.
  void scanVMEntrySites(const BinaryMemoryMap &mem);

  /// Build handler_entries_ from all discovered targets.
  void buildHandlerGraph();

  uint64_t image_base_ = 0;
  uint64_t vmenter_va_ = 0;
  uint64_t vmexit_va_ = 0;

  /// dispatch_addr → target_VA.
  llvm::DenseMap<uint64_t, uint64_t> dispatch_targets_;

  /// dispatch_addr → RVA (before adding image_base).
  llvm::DenseMap<uint64_t, uint32_t> dispatch_rvas_;

  /// RVA → target_VA (for IR matching).
  llvm::DenseMap<uint32_t, uint64_t> rva_to_target_;

  /// All unique target VAs (sorted).
  std::vector<uint64_t> all_target_vas_;

  /// Handler entry VAs (sorted, deduplicated).
  std::vector<uint64_t> handler_entries_;

  /// Fast lookup set for handler VAs.
  llvm::DenseSet<uint64_t> handler_set_;

  /// Chain-solved dispatch targets: handler_va → successor VAs.
  llvm::DenseMap<uint64_t, llvm::SmallVector<uint64_t, 2>> chain_targets_;
};

/// Module-level analysis providing the VMHandlerGraph.
///
/// The consumer registers this with a pre-built graph (same pattern as
/// BinaryMemoryAnalysis).  If not registered, passes that depend on it
/// get an empty graph and gracefully degrade.
class VMHandlerGraphAnalysis
    : public llvm::AnalysisInfoMixin<VMHandlerGraphAnalysis> {
  friend llvm::AnalysisInfoMixin<VMHandlerGraphAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = VMHandlerGraph;

  VMHandlerGraphAnalysis() = default;

  /// Construct with a pre-built handler graph.
  explicit VMHandlerGraphAnalysis(VMHandlerGraph graph)
      : graph_(std::move(graph)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);

 private:
  VMHandlerGraph graph_;
};

}  // namespace omill

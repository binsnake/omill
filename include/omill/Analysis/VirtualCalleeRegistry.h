#pragma once

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace llvm {
class Module;
}  // namespace llvm

namespace omill {

class VMTraceMap;

/// Metadata record for a single outlined virtual callee.
///
/// Each record links a per-callsite clone (clone_name) to the underlying base
/// function (base_name) and, critically, to the exact (handler_va, trace_hash)
/// key that identifies the traced path through the hash-dispatch VM.  This
/// linkage lets downstream passes and the pipeline cross-reference the trace
/// map without re-deriving handler identity from function attributes.
struct VirtualCalleeRecord {
  std::string clone_name;
  std::string base_name;
  std::string caller_name;
  std::string kind;           // "hash_resolved" or "nested_helper"
  std::optional<uint64_t> hash;
  uint64_t first_round = 0;

  /// The handler VA that roots this callee in the VM trace chain.
  /// Zero means the record was created before trace linkage existed.
  uint64_t handler_va = 0;

  /// The incoming hash that selects the specific demerged path through
  /// the handler.  Together with handler_va this forms the unique trace key
  /// (handler_va, trace_hash) into VMTraceMap.
  std::optional<uint64_t> trace_hash;

  /// Whether this record has been validated against a VMTraceMap entry.
  bool trace_linked = false;
};

/// Module-level registry of all outlined virtual callees.
///
/// This is the single source of truth for virtual callee metadata.  The
/// omill-lift tool populates it; the pipeline and downstream passes query it.
/// Function attributes (omill.vm_outlined_virtual_call etc.) remain as
/// lightweight boundary markers, but detail data lives here.
class VirtualCalleeRegistry {
 public:
  size_t size() const { return records_.size(); }

  llvm::ArrayRef<VirtualCalleeRecord> records() const { return records_; }

  /// Lookup by clone function name.
  std::optional<VirtualCalleeRecord> lookup(llvm::StringRef clone_name) const;

  /// Lookup by the (handler_va, trace_hash) trace key.
  /// Returns the record whose handler_va and trace_hash match exactly.
  std::optional<VirtualCalleeRecord>
  lookupByTraceKey(uint64_t handler_va, uint64_t trace_hash) const;

  /// All records derived from a given base function name.
  llvm::SmallVector<const VirtualCalleeRecord *, 4>
  lookupByBase(llvm::StringRef base_name) const;

  /// All records for a given caller function name.
  llvm::SmallVector<const VirtualCalleeRecord *, 4>
  lookupByCaller(llvm::StringRef caller_name) const;

  size_t countKind(llvm::StringRef kind) const;

  /// Number of records that have been validated against a VMTraceMap entry.
  size_t countTraceLinked() const;

  /// Validate all records against a VMTraceMap.  Sets trace_linked on each
  /// record whose (handler_va, trace_hash) key exists in the trace map.
  /// Returns the number of records newly linked.
  unsigned linkToTraceMap(const VMTraceMap &trace_map);

  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  friend class VirtualCalleeRegistryAnalysis;
  std::vector<VirtualCalleeRecord> records_;
  void rebuildIndices();
  llvm::DenseMap<uint64_t, llvm::SmallVector<size_t, 2>> trace_key_index_;
};

class VirtualCalleeRegistryAnalysis
    : public llvm::AnalysisInfoMixin<VirtualCalleeRegistryAnalysis> {
  friend llvm::AnalysisInfoMixin<VirtualCalleeRegistryAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = VirtualCalleeRegistry;

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

void setVirtualCalleeRegistryMetadata(
    llvm::Module &M, llvm::ArrayRef<VirtualCalleeRecord> records);

}  // namespace omill
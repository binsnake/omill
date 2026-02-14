#pragma once

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

#include <cstdint>
#include <map>
#include <optional>
#include <string>

namespace llvm {
class Module;
}  // namespace llvm

namespace omill {

/// Provides read-only access to the original binary's memory contents
/// (.rdata, .data, etc.). The consumer populates this before running
/// the pipeline.
class BinaryMemoryMap {
 public:
  struct ImportEntry {
    std::string module;
    std::string function;
  };

  /// Add a memory region from the original binary.
  void addRegion(uint64_t base, const uint8_t *data, size_t size);

  /// Register an IAT entry mapping an IAT slot VA to an import name.
  void addImport(uint64_t iat_va, std::string module, std::string function);

  /// Look up an import by its IAT slot virtual address.
  const ImportEntry *lookupImport(uint64_t iat_va) const;

  /// Read `size` bytes from the mapped address space.
  /// Returns true if the entire read was within a mapped region.
  bool read(uint64_t addr, uint8_t *out, unsigned size) const;

  /// Read a little-endian integer of the given byte size (1/2/4/8).
  std::optional<uint64_t> readInt(uint64_t addr, unsigned byte_size) const;

  bool empty() const { return regions_.empty() && imports_.empty(); }

  bool hasImports() const { return !imports_.empty(); }

  /// LLVM analysis invalidation — binary memory is always valid.
  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  struct Region {
    uint64_t base;
    const uint8_t *data;
    size_t size;
  };
  llvm::SmallVector<Region, 4> regions_;
  std::map<uint64_t, ImportEntry> imports_;
};

/// Module-level analysis providing the BinaryMemoryMap.
///
/// The consumer registers this with a pre-built map (same pattern as
/// LLVM's TargetIRAnalysis). If not registered, passes that depend on
/// it get an empty map and gracefully degrade.
class BinaryMemoryAnalysis
    : public llvm::AnalysisInfoMixin<BinaryMemoryAnalysis> {
  friend llvm::AnalysisInfoMixin<BinaryMemoryAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = BinaryMemoryMap;

  BinaryMemoryAnalysis() = default;

  /// Construct with a pre-built memory map.
  explicit BinaryMemoryAnalysis(BinaryMemoryMap map)
      : map_(std::move(map)) {}

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &);

 private:
  BinaryMemoryMap map_;
};

}  // namespace omill

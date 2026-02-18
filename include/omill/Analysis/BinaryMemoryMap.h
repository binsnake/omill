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

/// Classification of a value loaded from a relocated address.
enum class RelocValueKind {
  /// Not relocated — the value is a plain constant.
  NotRelocated,
  /// Relocated, and the on-disk value looks like a valid absolute VA
  /// (within [image_base, image_base + image_size)). This is a normal
  /// relocated pointer.
  NormalAddress,
  /// Relocated, but the on-disk value does NOT look like a valid VA.
  /// This is suspicious — the relocation may be used for constant encoding.
  Suspicious,
};

/// Provides read-only access to the original binary's memory contents
/// (.rdata, .data, etc.). The consumer populates this before running
/// the pipeline.
class BinaryMemoryMap {
 public:
  struct ImportEntry {
    std::string module;
    std::string function;
  };

  /// A base relocation entry parsed from the PE .reloc section.
  struct RelocEntry {
    uint64_t va;       // Virtual address of the relocated value.
    uint8_t size;      // Size in bytes (8 for DIR64, 4 for HIGHLOW).
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

  /// Register a base relocation entry from the PE .reloc section.
  void addRelocation(uint64_t va, uint8_t size);

  /// Finalize relocations after all addRelocation() calls (sorts the list).
  void finalizeRelocations();

  /// Check if any relocation entry overlaps the byte range [addr, addr+size).
  bool isRelocated(uint64_t addr, unsigned size) const;

  /// Classify a value loaded from a potentially-relocated address.
  /// Checks relocation overlap, then heuristically classifies the on-disk
  /// value as a normal address or suspicious constant.
  RelocValueKind classifyRelocatedValue(uint64_t addr, unsigned size,
                                        uint64_t on_disk_value) const;

  bool hasRelocations() const { return !relocs_.empty(); }

  /// Set/get the PE image base and size (needed for classification heuristic).
  void setImageBase(uint64_t base) { image_base_ = base; }
  uint64_t imageBase() const { return image_base_; }
  void setImageSize(uint64_t size) { image_size_ = size; }
  uint64_t imageSize() const { return image_size_; }

  /// Check if the preferred image base looks suspicious (0, kernel range,
  /// or typical system DLL range), meaning ASLR will always produce a
  /// non-zero delta and on-disk relocated values may be wrong.
  bool isSuspiciousImageBase() const;

  /// Iterate over all mapped regions (for JIT memory mapping, etc.).
  template <typename Fn>
  void forEachRegion(Fn &&fn) const {
    for (const auto &r : regions_)
      fn(r.base, r.data, r.size);
  }

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
  llvm::SmallVector<RelocEntry, 0> relocs_;
  bool relocs_sorted_ = false;
  uint64_t image_base_ = 0;
  uint64_t image_size_ = 0;
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

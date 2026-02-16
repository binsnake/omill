#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/StringRef.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace omill {

/// Supported hash algorithms for import resolution.
enum class HashAlgorithm : uint8_t {
  FNV1a32,            // (val ^ byte) * 0x01000193
  FNV1a32_Lowercase,  // same, but tolower each byte first
  DJB2,               // hash * 33 + byte
};

/// Hash database for resolving import hash constants to Windows API names.
/// Supports multiple hash algorithms via precomputed lookup tables.
class ImportHashDB {
 public:
  struct ExportEntry {
    std::string module;
    std::string function;
  };

  struct ResolvedImport {
    ExportEntry entry;
    HashAlgorithm algorithm;
    uint32_t seed;
  };

  /// Add an individual export to the database.
  void addExport(llvm::StringRef module, llvm::StringRef function);

  /// Load the built-in table of common Windows API exports (~1000 entries).
  void loadBuiltins();

  /// Load exports from a text file: "module.dll\tFunctionName" per line.
  bool loadFromFile(llvm::StringRef path);

  /// Build precomputed lookup tables for all supported algorithm/seed
  /// combinations.  Must be called after loading exports and before
  /// calling tryResolve().
  void buildLookupTables();

  /// Try to resolve a hash constant against all precomputed lookup tables.
  /// Returns the matching export, algorithm, and seed if found.
  std::optional<ResolvedImport> tryResolve(uint32_t hash_value) const;

  /// Resolve a lazy_importer hash (legacy API, linear scan).
  std::optional<ExportEntry> resolve(uint32_t offset,
                                     uint32_t target_hash) const;

  /// Given a hash, check if it matches a known DLL name (case-insensitive
  /// FNV1a32 with seed 0x811c9dc5).
  std::optional<std::string> resolveModuleName(uint32_t hash) const;

  /// Given a known module and function hash, resolve the function name
  /// (case-sensitive FNV1a32 with seed 0x811c9dc5).
  std::optional<ExportEntry> resolveInModule(llvm::StringRef module,
                                             uint32_t func_hash) const;

  /// Compute hash with a specific algorithm and seed.
  static uint32_t computeHash(llvm::StringRef name, HashAlgorithm algo,
                              uint32_t seed);

  /// Compute the FNV-1a hash for a name with given offset (legacy API).
  static uint32_t computeHash(llvm::StringRef name, uint32_t offset);

  size_t size() const { return exports_.size(); }

 private:
  std::vector<ExportEntry> exports_;

  struct LookupTable {
    HashAlgorithm algo;
    uint32_t seed;
    llvm::DenseMap<uint32_t, size_t> table;  // hash → index into exports_
  };
  std::vector<LookupTable> lookup_tables_;
};

}  // namespace omill

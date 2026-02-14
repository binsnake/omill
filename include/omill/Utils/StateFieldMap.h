#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringMap.h>
#include <llvm/ADT/StringRef.h>

#include <optional>
#include <string>

namespace llvm {
class DataLayout;
class GetElementPtrInst;
class Module;
class StructType;
class Type;
class Value;
}  // namespace llvm

namespace omill {

/// Category of a field within the State struct.
enum class StateFieldCategory {
  kGPR,        // General-purpose register (RAX, RBX, etc.)
  kVector,     // Vector register (XMM, YMM, ZMM)
  kFlag,       // Individual flag (CF, ZF, SF, OF, PF, AF, DF)
  kSegment,    // Segment selector (CS, DS, ES, FS, GS, SS)
  kFPU,        // FPU state (x87, FPU status/control words)
  kMMX,        // MMX register
  kAVX512Mask, // AVX-512 mask register (k0-k7)
  kControl,    // Control registers, XCR, segment caches
  kPadding,    // Volatile separator or alignment padding
  kOther,      // Anything else
};

/// A single resolved field within the State struct.
struct StateField {
  std::string name;           // e.g., "RAX", "ZF", "XMM0"
  unsigned offset;            // Byte offset from State base
  unsigned size;              // Size in bytes
  StateFieldCategory category;
  bool is_volatile_separator; // True if this is remill's volatile padding
};

/// Maps byte offsets in the remill State struct to register field information.
/// Built by analyzing the State StructType from a remill-lifted module.
class StateFieldMap {
 public:
  /// Construct from a module containing the State type.
  /// The module must have been loaded via remill (contains %struct.State).
  explicit StateFieldMap(llvm::Module &M);

  /// Look up a field by byte offset into the State struct.
  std::optional<StateField> fieldAtOffset(unsigned offset) const;

  /// Look up a field by name (e.g., "RAX", "ZF").
  std::optional<StateField> fieldByName(llvm::StringRef name) const;

  /// Given a GEP instruction rooted at the State pointer, resolve
  /// which field it accesses and the byte offset.
  /// Returns std::nullopt if the GEP doesn't resolve to a known field.
  std::optional<StateField> resolveGEP(llvm::GetElementPtrInst *GEP) const;

  /// Given an arbitrary pointer value, attempt to trace it back to a
  /// State field. Handles chains of GEP + bitcast.
  std::optional<StateField> resolvePointer(llvm::Value *ptr) const;

  /// Get all GPR fields.
  llvm::SmallVector<StateField, 16> getGPRs() const;

  /// Get all flag fields.
  llvm::SmallVector<StateField, 8> getFlags() const;

  /// Get all vector register fields.
  llvm::SmallVector<StateField, 32> getVectorRegs() const;

  /// Get the State struct type.
  llvm::StructType *getStateType() const { return state_type_; }

  /// Check if a value is (derived from) the State pointer argument.
  bool isStatePointer(llvm::Value *V) const;

 private:
  void buildMap(llvm::Module &M);
  void addField(const std::string &name, unsigned offset, unsigned size,
                StateFieldCategory category, bool volatile_sep = false);

  /// Derive register names from the x86-64 struct type layout.
  /// Fallback when __remill_basic_block is unavailable.
  void addX86_64RegisterNames();

  llvm::StructType *state_type_ = nullptr;
  const llvm::DataLayout *data_layout_ = nullptr;

  // Offset -> field
  llvm::DenseMap<unsigned, StateField> offset_to_field_;

  // Name -> offset (for reverse lookup)
  llvm::StringMap<unsigned> name_to_offset_;

  // All fields, ordered by offset
  llvm::SmallVector<StateField, 128> all_fields_;
};

}  // namespace omill

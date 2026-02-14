#include "omill/Utils/StateFieldMap.h"

#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

namespace omill {

namespace {

// Map common State sub-struct/field names to categories.
StateFieldCategory categorizeFieldName(llvm::StringRef name) {
  // GPRs
  if (name == "RAX" || name == "RBX" || name == "RCX" || name == "RDX" ||
      name == "RSI" || name == "RDI" || name == "RSP" || name == "RBP" ||
      name == "R8" || name == "R9" || name == "R10" || name == "R11" ||
      name == "R12" || name == "R13" || name == "R14" || name == "R15" ||
      name == "RIP") {
    return StateFieldCategory::kGPR;
  }

  // Flags
  if (name == "CF" || name == "PF" || name == "AF" || name == "ZF" ||
      name == "SF" || name == "DF" || name == "OF") {
    return StateFieldCategory::kFlag;
  }

  // Vector registers
  if (name.starts_with("XMM") || name.starts_with("YMM") ||
      name.starts_with("ZMM")) {
    return StateFieldCategory::kVector;
  }

  // MMX
  if (name.starts_with("MM")) {
    return StateFieldCategory::kMMX;
  }

  // Segment selectors
  if (name == "CS" || name == "DS" || name == "ES" || name == "FS" ||
      name == "GS" || name == "SS") {
    return StateFieldCategory::kSegment;
  }

  // FPU
  if (name.starts_with("ST") || name.starts_with("FPU") ||
      name.starts_with("FXSAVE")) {
    return StateFieldCategory::kFPU;
  }

  // AVX-512 mask registers
  if (name.size() == 2 && name[0] == 'K' && name[1] >= '0' &&
      name[1] <= '7') {
    return StateFieldCategory::kAVX512Mask;
  }

  // Volatile separators
  if (name.starts_with("_")) {
    return StateFieldCategory::kPadding;
  }

  return StateFieldCategory::kOther;
}

/// Recursively flatten a struct type, mapping each leaf field to its byte offset
/// and a human-readable name. We build paths like "gpr.rax.qword" and map
/// known names.
void flattenStruct(const llvm::DataLayout &DL, llvm::StructType *ST,
                   uint64_t base_offset, const std::string &prefix,
                   llvm::SmallVectorImpl<StateField> &out) {
  if (!ST) return;

  const auto *SL = DL.getStructLayout(ST);

  for (unsigned i = 0, e = ST->getNumElements(); i < e; ++i) {
    auto *elem_ty = ST->getElementType(i);
    uint64_t field_offset = base_offset + SL->getElementOffset(i);
    uint64_t field_size = DL.getTypeAllocSize(elem_ty);

    std::string field_name;
    if (ST->hasName()) {
      // Attempt to derive the field name from the struct name and index.
      // LLVM struct types don't carry field names, so we use the struct
      // type name + field index as a fallback.
      field_name = prefix.empty()
                       ? (ST->getName().str() + "." + std::to_string(i))
                       : (prefix + "." + std::to_string(i));
    } else {
      field_name =
          prefix.empty() ? std::to_string(i) : (prefix + "." + std::to_string(i));
    }

    if (auto *inner_st = llvm::dyn_cast<llvm::StructType>(elem_ty)) {
      flattenStruct(DL, inner_st, field_offset, field_name, out);
    } else if (llvm::isa<llvm::ArrayType>(elem_ty)) {
      // For arrays, add the array as a single entity
      // (e.g., vec[32] as a block)
      StateField field;
      field.name = field_name;
      field.offset = static_cast<unsigned>(field_offset);
      field.size = static_cast<unsigned>(field_size);
      field.category = StateFieldCategory::kOther;
      field.is_volatile_separator = false;
      out.push_back(std::move(field));
    } else {
      // Leaf field
      StateField field;
      field.name = field_name;
      field.offset = static_cast<unsigned>(field_offset);
      field.size = static_cast<unsigned>(field_size);
      field.category = StateFieldCategory::kOther;

      // Check if this is a volatile separator (typically uint8_t named _N)
      field.is_volatile_separator =
          (field_size == 1 && field_name.find("._") != std::string::npos);

      out.push_back(std::move(field));
    }
  }
}

// Register names are discovered dynamically from __remill_basic_block's named
// GEP instructions, which map register names to State struct offsets.

}  // namespace

StateFieldMap::StateFieldMap(llvm::Module &M) { buildMap(M); }

void StateFieldMap::buildMap(llvm::Module &M) {
  data_layout_ = &M.getDataLayout();

  // Find the State struct type. Remill names it "struct.State".
  // First try direct lookup by name in the context.
  state_type_ = llvm::StructType::getTypeByName(M.getContext(), "struct.State");

  // Fallback: scan identified types (for older modules where the type
  // might have a different naming).
  if (!state_type_) {
    for (auto *ST : M.getIdentifiedStructTypes()) {
      if (ST->getName() == "struct.State") {
        state_type_ = ST;
        break;
      }
    }
  }

  if (!state_type_) {
    // No State type found. We can still discover register names from
    // __remill_basic_block GEPs without the struct type.
  }

  // Flatten the struct to discover all fields and their offsets.
  if (state_type_) {
    flattenStruct(*data_layout_, state_type_, 0, "", all_fields_);

    // Register all flat fields by offset.
    for (auto &field : all_fields_) {
      offset_to_field_[field.offset] = field;
    }
  }

  // Now overlay known register names. We do this by finding the
  // __remill_basic_block function, which declares local variables
  // aliased to State fields. The variable names ARE the register names.
  // This is the canonical way remill maps names to offsets.
  bool found_remill_bb = false;
  if (auto *BB = M.getFunction("__remill_basic_block")) {
    // The entry block contains allocas/GEPs that name each register.
    // Each named variable is a pointer into the State struct.
    // We can extract the offset from the GEP indices.
    if (!BB->empty()) {
      for (auto &I : BB->getEntryBlock()) {
        if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I)) {
          if (!GEP->hasName()) continue;

          llvm::APInt offset_ap(64, 0);
          if (GEP->accumulateConstantOffset(*data_layout_, offset_ap)) {
            unsigned offset = static_cast<unsigned>(offset_ap.getZExtValue());
            unsigned size = static_cast<unsigned>(
                data_layout_->getTypeAllocSize(GEP->getResultElementType()));
            std::string name = GEP->getName().str();

            StateFieldCategory cat = categorizeFieldName(name);
            addField(name, offset, size, cat);
            found_remill_bb = true;
          }
        }
      }
    }
  }

  // Fallback: if __remill_basic_block was inlined/deleted, derive register
  // names from the struct type layout.  x86-64 GPR is struct.GPR with
  // alternating {i64 separator, Reg} pairs for 17 registers.
  if (!found_remill_bb && state_type_) {
    addX86_64RegisterNames();
  }
}

void StateFieldMap::addX86_64RegisterNames() {
  // x86-64 remill State layout:
  //   State = { X86State }
  //   X86State = { ArchState, vec[32], ArithFlags, Flags, Segments,
  //                AddressSpace, GPR, X87Stack, MMX, ... }
  //   GPR = { i64, Reg, i64, Reg, ... } (17 regs with separator padding)
  //
  // Detect the GPR sub-struct by finding struct.GPR in the type hierarchy.
  auto *gpr_ty = llvm::StructType::getTypeByName(
      state_type_->getContext(), "struct.GPR");
  if (!gpr_ty)
    return;

  // Compute GPR base offset within State.
  unsigned gpr_base = 0;
  bool found_gpr = false;

  // Walk the X86State struct to find the GPR field.
  auto *x86_ty = llvm::StructType::getTypeByName(
      state_type_->getContext(), "struct.X86State");
  if (!x86_ty)
    return;

  const auto *x86_layout = data_layout_->getStructLayout(x86_ty);
  for (unsigned i = 0; i < x86_ty->getNumElements(); ++i) {
    if (x86_ty->getElementType(i) == gpr_ty) {
      gpr_base = static_cast<unsigned>(x86_layout->getElementOffset(i));
      found_gpr = true;
      break;
    }
  }
  if (!found_gpr)
    return;

  // GPR register order in remill (from State.h):
  // {sep, RAX, sep, RBX, sep, RCX, sep, RDX,
  //  sep, RSI, sep, RDI, sep, RSP, sep, RBP,
  //  sep, R8,  sep, R9,  sep, R10, sep, R11,
  //  sep, R12, sep, R13, sep, R14, sep, R15,
  //  sep, RIP}
  static constexpr const char *kGPRNames[] = {
      "RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RSP", "RBP",
      "R8",  "R9",  "R10", "R11", "R12", "R13", "R14", "R15", "RIP",
  };
  static constexpr unsigned kNumGPRs = 17;

  const auto *gpr_layout = data_layout_->getStructLayout(gpr_ty);

  // GPR struct fields: element 0 is initial separator (i64),
  // then pairs of (Reg, separator). Registers are at odd indices:
  // element 1 = RAX, element 3 = RBX, element 5 = RCX, ...
  for (unsigned i = 0; i < kNumGPRs; ++i) {
    unsigned elem_idx = 1 + i * 2; // skip initial sep, then every other
    if (elem_idx >= gpr_ty->getNumElements())
      break;
    unsigned offset = gpr_base +
        static_cast<unsigned>(gpr_layout->getElementOffset(elem_idx));
    addField(kGPRNames[i], offset, 8, StateFieldCategory::kGPR);
  }

  // Also add flags from ArithFlags struct.
  auto *aflags_ty = llvm::StructType::getTypeByName(
      state_type_->getContext(), "struct.ArithFlags");
  if (aflags_ty) {
    unsigned aflags_base = 0;
    for (unsigned i = 0; i < x86_ty->getNumElements(); ++i) {
      if (x86_ty->getElementType(i) == aflags_ty) {
        aflags_base = static_cast<unsigned>(x86_layout->getElementOffset(i));
        break;
      }
    }
    // ArithFlags: {sep, CF, sep, PF, sep, AF, sep, ZF, sep, SF, sep, DF, sep, OF}
    static constexpr const char *kFlagNames[] = {
        "CF", "PF", "AF", "ZF", "SF", "DF", "OF",
    };
    const auto *aflags_layout = data_layout_->getStructLayout(aflags_ty);
    for (unsigned i = 0; i < 7; ++i) {
      unsigned elem_idx = 1 + i * 2;
      if (elem_idx >= aflags_ty->getNumElements())
        break;
      unsigned offset = aflags_base +
          static_cast<unsigned>(aflags_layout->getElementOffset(elem_idx));
      addField(kFlagNames[i], offset, 1, StateFieldCategory::kFlag);
    }
  }
}

void StateFieldMap::addField(const std::string &name, unsigned offset,
                             unsigned size, StateFieldCategory category,
                             bool volatile_sep) {
  StateField field;
  field.name = name;
  field.offset = offset;
  field.size = size;
  field.category = category;
  field.is_volatile_separator = volatile_sep;

  offset_to_field_[offset] = field;
  name_to_offset_[name] = offset;
}

std::optional<StateField> StateFieldMap::fieldAtOffset(unsigned offset) const {
  auto it = offset_to_field_.find(offset);
  if (it != offset_to_field_.end()) {
    return it->second;
  }
  return std::nullopt;
}

std::optional<StateField> StateFieldMap::fieldByName(
    llvm::StringRef name) const {
  auto it = name_to_offset_.find(name);
  if (it != name_to_offset_.end()) {
    return fieldAtOffset(it->getValue());
  }
  return std::nullopt;
}

std::optional<StateField> StateFieldMap::resolveGEP(
    llvm::GetElementPtrInst *GEP) const {
  if (!data_layout_) return std::nullopt;

  llvm::APInt offset(64, 0);
  if (!GEP->accumulateConstantOffset(*data_layout_, offset)) {
    return std::nullopt;
  }

  return fieldAtOffset(static_cast<unsigned>(offset.getZExtValue()));
}

std::optional<StateField> StateFieldMap::resolvePointer(
    llvm::Value *ptr) const {
  if (!data_layout_) return std::nullopt;

  // Walk through bitcasts and GEPs accumulating a constant byte offset.
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(*data_layout_, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      break;
    }

    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }

    break;
  }

  // Check if we resolved back to the State pointer argument.
  if (isStatePointer(base) && total_offset >= 0) {
    return fieldAtOffset(static_cast<unsigned>(total_offset));
  }

  return std::nullopt;
}

bool StateFieldMap::isStatePointer(llvm::Value *V) const {
  // The State pointer is conventionally the first argument of lifted functions.
  if (auto *arg = llvm::dyn_cast<llvm::Argument>(V)) {
    return arg->getArgNo() == 0;
  }
  return false;
}

llvm::SmallVector<StateField, 16> StateFieldMap::getGPRs() const {
  llvm::SmallVector<StateField, 16> result;
  for (auto &[offset, field] : offset_to_field_) {
    if (field.category == StateFieldCategory::kGPR) {
      result.push_back(field);
    }
  }
  return result;
}

llvm::SmallVector<StateField, 8> StateFieldMap::getFlags() const {
  llvm::SmallVector<StateField, 8> result;
  for (auto &[offset, field] : offset_to_field_) {
    if (field.category == StateFieldCategory::kFlag) {
      result.push_back(field);
    }
  }
  return result;
}

llvm::SmallVector<StateField, 32> StateFieldMap::getVectorRegs() const {
  llvm::SmallVector<StateField, 32> result;
  for (auto &[offset, field] : offset_to_field_) {
    if (field.category == StateFieldCategory::kVector) {
      result.push_back(field);
    }
  }
  return result;
}

}  // namespace omill

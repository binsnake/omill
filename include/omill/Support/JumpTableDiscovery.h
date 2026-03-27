#pragma once

/// Binary-level jump table discovery for x86-64.
///
/// Supports two jump table dispatch patterns:
///
/// 1. RIP-relative (LLVM default):
///   lea base_reg, [rip + disp32]    (load jump table base)
///   movsxd entry, [base + idx*4]    (read 32-bit signed relative entry)
///   add target, base                (compute absolute target)
///   jmp target                      (indirect jump)
///
/// 2. Image-base-relative (OLLVM CFF / MSVC):
///   mov reg32, [base_reg + idx*4 + table_rva]  (load 32-bit RVA entry)
///   add reg64, base_reg                         (compute absolute target)
///   jmp reg64                                   (indirect jump)

#include "omill/Analysis/BinaryMemoryMap.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <vector>

namespace omill {

/// Discover RIP-relative jump table targets by scanning a code region.
///
/// For each `lea reg, [rip + disp32]`, checks whether the computed address
/// points to a valid table of 32-bit signed offsets relative to the LEA result.
///
/// \param mem          Binary memory map with section data.
/// \param func_va      Start of the scan region.
/// \param max_scan     Maximum number of bytes to scan from func_va.
/// \returns            Unique target addresses discovered from jump tables.
inline std::vector<uint64_t>
discoverJumpTableTargets(const BinaryMemoryMap &mem, uint64_t func_va,
                         size_t max_scan = 2048) {
  std::vector<uint64_t> targets;

  std::vector<uint8_t> bytes(max_scan);
  if (!mem.read(func_va, bytes.data(), static_cast<unsigned>(max_scan)))
    return targets;

  // Scan for LEA reg, [RIP + disp32]:
  //   [REX.W] 8D [ModRM: mod=00 rm=101] [disp32]
  for (size_t i = 0; i + 7 <= max_scan; ++i) {
    uint8_t b0 = bytes[i];
    if ((b0 & 0xF8) != 0x48)
      continue;
    if (bytes[i + 1] != 0x8D)
      continue;
    uint8_t modrm = bytes[i + 2];
    if ((modrm & 0xC7) != 0x05)
      continue;

    int32_t disp;
    std::memcpy(&disp, &bytes[i + 3], 4);

    uint64_t next_ip = func_va + i + 7;
    uint64_t table_base = next_ip + static_cast<int64_t>(disp);

    std::vector<uint64_t> candidate;
    for (unsigned j = 0; j < 1024; ++j) {
      auto entry_opt = mem.readInt(table_base + j * 4, 4);
      if (!entry_opt)
        break;
      int32_t entry = static_cast<int32_t>(*entry_opt);
      uint64_t target = table_base + static_cast<int64_t>(entry);
      if (target < func_va - 0x100000 || target > func_va + 0x100000)
        break;
      if (target == table_base)
        break;
      candidate.push_back(target);
    }

    if (candidate.size() >= 4) {
      targets.insert(targets.end(), candidate.begin(), candidate.end());
      break;
    }
  }

  std::sort(targets.begin(), targets.end());
  targets.erase(std::unique(targets.begin(), targets.end()), targets.end());
  return targets;
}

/// Discover image-base-relative jump table targets by scanning a code region.
///
/// Unlike discoverImageBaseRelativeTargets(), this does not require the exact
/// indirect jump PC. It scans forward from a candidate handler entry for the
/// MOV-with-SIB pattern used by MSVC / OLLVM flattened dispatches and requires
/// an indirect register jump to appear shortly afterward.
inline std::vector<uint64_t> discoverImageBaseRelativeTargetsInRegion(
    const BinaryMemoryMap &mem, uint64_t image_base, uint64_t func_va,
    size_t max_scan = 2048) {
  std::vector<uint64_t> targets;
  if (image_base == 0)
    return targets;

  std::vector<uint8_t> bytes(max_scan);
  if (!mem.read(func_va, bytes.data(), static_cast<unsigned>(max_scan)))
    return targets;

  for (size_t i = 0; i + 7 <= max_scan; ++i) {
    size_t opcode_index = i;
    if ((bytes[opcode_index] & 0xF0) == 0x40) {
      if (opcode_index + 8 > max_scan)
        continue;
      ++opcode_index;
    }
    if (bytes[opcode_index] != 0x8B)
      continue;

    uint8_t modrm = bytes[opcode_index + 1];
    if ((modrm >> 6) != 2 || (modrm & 7) != 4)
      continue;

    uint8_t sib = bytes[opcode_index + 2];
    if ((sib >> 6) != 2)
      continue;

    size_t inst_len = (opcode_index - i) + 7;

    bool has_indirect_jmp = false;
    for (size_t j = i + inst_len; j + 1 < std::min(max_scan, i + 24); ++j) {
      if (bytes[j] == 0xFF && (bytes[j + 1] & 0xF8) == 0xE0) {
        has_indirect_jmp = true;
        break;
      }
    }
    if (!has_indirect_jmp)
      continue;

    uint32_t table_rva = 0;
    std::memcpy(&table_rva, &bytes[opcode_index + 3], 4);
    uint64_t table_va = image_base + table_rva;

    std::vector<uint64_t> candidate;
    for (unsigned j = 0; j < 256; ++j) {
      auto entry_opt = mem.readInt(table_va + j * 4, 4);
      if (!entry_opt)
        break;

      uint32_t entry = static_cast<uint32_t>(*entry_opt);
      if (entry == 0)
        break;

      uint64_t target = image_base + entry;
      if (target < func_va - 0x100000 || target > func_va + 0x100000)
        break;

      candidate.push_back(target);
    }

    if (candidate.size() >= 2) {
      targets.insert(targets.end(), candidate.begin(), candidate.end());
      break;
    }
  }

  std::sort(targets.begin(), targets.end());
  targets.erase(std::unique(targets.begin(), targets.end()), targets.end());
  return targets;
}

/// Discover jump table targets from an image-base-relative dispatch pattern.
///
/// Scans backward from the indirect jump instruction to find:
///   [REX] 8B [ModRM: mod=10 rm=SIB] [SIB: scale=4] [disp32]
///   [REX.W] 03 [ModRM: mod=11]
///
/// The disp32 in the MOV is the table RVA. Each 4-byte table entry is an
/// unsigned RVA; the absolute target is image_base + entry.
///
/// \param mem          Binary memory map with section data.
/// \param image_base   PE image base address.
/// \param jmp_pc       Virtual address of the indirect jump instruction.
/// \returns            Unique target addresses discovered from the table.
inline std::vector<uint64_t>
discoverImageBaseRelativeTargets(const BinaryMemoryMap &mem,
                                 uint64_t image_base, uint64_t jmp_pc) {
  std::vector<uint64_t> targets;
  if (image_base == 0)
    return targets;

  constexpr size_t kMaxBackScan = 32;
  uint64_t scan_start = jmp_pc > kMaxBackScan ? jmp_pc - kMaxBackScan : 0;
  size_t scan_len = static_cast<size_t>(jmp_pc - scan_start);

  std::vector<uint8_t> bytes(scan_len);
  if (!mem.read(scan_start, bytes.data(), static_cast<unsigned>(scan_len)))
    return targets;

  uint32_t table_rva = 0;
  bool found = false;

  for (size_t i = 0; i + 7 <= scan_len; ++i) {
    size_t opcode_index = i;
    if ((bytes[opcode_index] & 0xF0) == 0x40) {
      if (opcode_index + 8 > scan_len)
        continue;
      ++opcode_index;
    }
    if (bytes[opcode_index] != 0x8B)
      continue;

    uint8_t modrm = bytes[opcode_index + 1];
    if ((modrm >> 6) != 2)
      continue;
    if ((modrm & 7) != 4)
      continue;

    uint8_t sib = bytes[opcode_index + 2];
    if ((sib >> 6) != 2)
      continue;

    std::memcpy(&table_rva, &bytes[opcode_index + 3], 4);
    found = true;
  }

  if (!found)
    return targets;

  uint64_t table_va = image_base + table_rva;

  for (unsigned j = 0; j < 256; ++j) {
    auto entry_opt = mem.readInt(table_va + j * 4, 4);
    if (!entry_opt)
      break;

    uint32_t entry = static_cast<uint32_t>(*entry_opt);
    if (entry == 0)
      break;

    uint64_t target = image_base + entry;
    if (target < jmp_pc - 0x100000 || target > jmp_pc + 0x100000)
      break;

    targets.push_back(target);
  }

  std::sort(targets.begin(), targets.end());
  targets.erase(std::unique(targets.begin(), targets.end()), targets.end());
  return targets;
}

}  // namespace omill

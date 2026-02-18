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

/// Discover jump table targets from an image-base-relative dispatch pattern.
///
/// Scans backward from the indirect jump instruction to find:
///   [REX] 8B [ModRM: mod=10 rm=SIB] [SIB: scale=4] [disp32]
///   [REX.W] 03 [ModRM: mod=11]
///
/// The disp32 in the MOV is the table RVA.  Each 4-byte table entry is an
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

  // Read up to 32 bytes before the indirect jump instruction.
  constexpr size_t kMaxBackScan = 32;
  uint64_t scan_start = jmp_pc > kMaxBackScan ? jmp_pc - kMaxBackScan : 0;
  size_t scan_len = static_cast<size_t>(jmp_pc - scan_start);

  std::vector<uint8_t> bytes(scan_len);
  if (!mem.read(scan_start, bytes.data(), static_cast<unsigned>(scan_len)))
    return targets;

  // Look for MOV reg32, [base + idx*4 + disp32] instruction.
  // Encoding: [REX] 8B [ModRM] [SIB] [disp32]  (8 bytes)
  //   ModRM: mod=10 (disp32), rm=100 (SIB follows)
  //   SIB:   scale=10 (×4)
  // Use the last (closest to jmp) match.
  uint32_t table_rva = 0;
  bool found = false;

  for (size_t i = 0; i + 8 <= scan_len; ++i) {
    uint8_t rex = bytes[i];
    if ((rex & 0xF0) != 0x40)
      continue;
    if (bytes[i + 1] != 0x8B)
      continue;
    uint8_t modrm = bytes[i + 2];
    if ((modrm >> 6) != 2)
      continue; // mod must be 10 (disp32)
    if ((modrm & 7) != 4)
      continue; // rm must be 100 (SIB)
    uint8_t sib = bytes[i + 3];
    if ((sib >> 6) != 2)
      continue; // scale must be 10 (×4)

    std::memcpy(&table_rva, &bytes[i + 4], 4);
    found = true;
    // Continue scanning to prefer the match closest to the jmp.
  }

  if (!found)
    return targets;

  uint64_t table_va = image_base + table_rva;

  // Read 32-bit unsigned RVA entries from the table.
  for (unsigned j = 0; j < 256; ++j) {
    auto entry_opt = mem.readInt(table_va + j * 4, 4);
    if (!entry_opt)
      break;

    uint32_t entry = static_cast<uint32_t>(*entry_opt);
    if (entry == 0)
      break;

    uint64_t target = image_base + entry;

    // Sanity: target should be within ~1 MB of the jump site.
    if (target < jmp_pc - 0x100000 || target > jmp_pc + 0x100000)
      break;

    targets.push_back(target);
  }

  std::sort(targets.begin(), targets.end());
  targets.erase(std::unique(targets.begin(), targets.end()), targets.end());
  return targets;
}

} // namespace omill

#pragma once

#include "omill/Analysis/BinaryMemoryMap.h"

#include <llvm/Object/COFF.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/MemoryBuffer.h>

#include <cstdint>
#include <deque>
#include <map>
#include <string>
#include <vector>

namespace omill::e2e {

/// Information extracted from a PE file for testing.
struct PEInfo {
  /// Persistent storage for section data (memory_map points into these).
  /// Uses deque so that push_back never invalidates existing element pointers.
  std::deque<std::vector<uint8_t>> section_storage;
  BinaryMemoryMap memory_map;              // All sections mapped at VA
  std::map<std::string, uint64_t> exports; // export name -> virtual address
  uint64_t text_base = 0;                  // VA of .text section
  uint64_t text_size = 0;                  // Size of .text section
  uint64_t image_base = 0;
};

/// Load a PE file and populate PEInfo with sections + exports.
/// Returns false on failure (logs to errs()).
inline bool loadPE(llvm::StringRef path, PEInfo &out) {
  auto buf_or_err = llvm::MemoryBuffer::getFile(path);
  if (!buf_or_err) {
    llvm::errs() << "loadPE: cannot open " << path << ": "
                 << buf_or_err.getError().message() << "\n";
    return false;
  }

  auto obj_or_err = llvm::object::COFFObjectFile::create(
      (*buf_or_err)->getMemBufferRef());
  if (!obj_or_err) {
    llvm::errs() << "loadPE: not a valid COFF/PE: "
                 << llvm::toString(obj_or_err.takeError()) << "\n";
    return false;
  }
  auto &coff = **obj_or_err;

  out.image_base = coff.getImageBase();

  // Map each section — copy data into section_storage for lifetime safety.
  for (const auto &sec : coff.sections()) {
    auto name_or_err = sec.getName();
    if (!name_or_err) {
      llvm::consumeError(name_or_err.takeError());
      continue;
    }
    llvm::StringRef name = *name_or_err;

    auto contents_or_err = sec.getContents();
    if (!contents_or_err) {
      llvm::consumeError(contents_or_err.takeError());
      continue;
    }
    llvm::StringRef contents = *contents_or_err;

    // For PE images, SectionRef::getAddress() already returns the full VA
    // (ImageBase + section RVA).
    uint64_t va = sec.getAddress();

    // Copy section data into persistent storage.
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();

    out.memory_map.addRegion(va, stored.data(), stored.size());

    if (name == ".text") {
      out.text_base = va;
      out.text_size = stored.size();
    }
  }

  // Parse exports.
  for (const auto &exp : coff.export_directories()) {
    llvm::StringRef exp_name;
    if (auto ec = exp.getSymbolName(exp_name)) {
      continue;
    }
    uint32_t rva = 0;
    if (auto ec = exp.getExportRVA(rva)) {
      continue;
    }
    out.exports[exp_name.str()] = out.image_base + rva;
  }

  return true;
}

}  // namespace omill::e2e

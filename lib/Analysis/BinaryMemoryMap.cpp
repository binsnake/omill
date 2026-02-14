#include "omill/Analysis/BinaryMemoryMap.h"

#include <algorithm>
#include <cstring>

namespace omill {

llvm::AnalysisKey BinaryMemoryAnalysis::Key;

void BinaryMemoryMap::addRegion(uint64_t base, const uint8_t *data,
                                size_t size) {
  regions_.push_back({base, data, size});
  // Keep sorted by base address for binary search.
  std::sort(regions_.begin(), regions_.end(),
            [](const Region &a, const Region &b) { return a.base < b.base; });
}

bool BinaryMemoryMap::read(uint64_t addr, uint8_t *out, unsigned size) const {
  // Binary search for the region containing addr.
  auto it = std::upper_bound(
      regions_.begin(), regions_.end(), addr,
      [](uint64_t a, const Region &r) { return a < r.base; });

  if (it == regions_.begin())
    return false;
  --it;

  uint64_t offset = addr - it->base;
  if (offset + size > it->size)
    return false;

  std::memcpy(out, it->data + offset, size);
  return true;
}

void BinaryMemoryMap::addImport(uint64_t iat_va, std::string module,
                                std::string function) {
  imports_[iat_va] = {std::move(module), std::move(function)};
}

const BinaryMemoryMap::ImportEntry *BinaryMemoryMap::lookupImport(
    uint64_t iat_va) const {
  auto it = imports_.find(iat_va);
  return (it != imports_.end()) ? &it->second : nullptr;
}

std::optional<uint64_t> BinaryMemoryMap::readInt(uint64_t addr,
                                                  unsigned byte_size) const {
  uint8_t buf[8];
  if (byte_size > 8 || !read(addr, buf, byte_size))
    return std::nullopt;

  // Little-endian decode.
  uint64_t val = 0;
  for (unsigned i = 0; i < byte_size; ++i)
    val |= static_cast<uint64_t>(buf[i]) << (i * 8);
  return val;
}

BinaryMemoryAnalysis::Result BinaryMemoryAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  return std::move(map_);
}

}  // namespace omill

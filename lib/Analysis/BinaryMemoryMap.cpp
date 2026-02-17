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

void BinaryMemoryMap::addRelocation(uint64_t va, uint8_t size) {
  relocs_.push_back({va, size});
  relocs_sorted_ = false;
}

void BinaryMemoryMap::finalizeRelocations() {
  std::sort(relocs_.begin(), relocs_.end(),
            [](const RelocEntry &a, const RelocEntry &b) {
              return a.va < b.va;
            });
  relocs_sorted_ = true;
}

bool BinaryMemoryMap::isRelocated(uint64_t addr, unsigned size) const {
  if (relocs_.empty())
    return false;

  // Find the first relocation that could overlap [addr, addr+size).
  // A relocation at VA R with size S overlaps if R < addr+size && R+S > addr.
  auto it = std::lower_bound(
      relocs_.begin(), relocs_.end(), addr,
      [](const RelocEntry &e, uint64_t a) { return e.va + e.size <= a; });

  if (it != relocs_.end() && it->va < addr + size)
    return true;

  return false;
}

RelocValueKind BinaryMemoryMap::classifyRelocatedValue(
    uint64_t addr, unsigned size, uint64_t on_disk_value) const {
  if (!isRelocated(addr, size))
    return RelocValueKind::NotRelocated;

  // Check if the on-disk value looks like a valid absolute VA within the image.
  if (image_base_ != 0 && image_size_ != 0) {
    if (on_disk_value >= image_base_ &&
        on_disk_value < image_base_ + image_size_)
      return RelocValueKind::NormalAddress;
  }

  return RelocValueKind::Suspicious;
}

bool BinaryMemoryMap::isSuspiciousImageBase() const {
  if (image_base_ == 0)
    return true;

  // Kernel-mode range (above 0x8000'0000'0000'0000).
  if (image_base_ >= 0x8000000000000000ULL)
    return true;

  // System DLL range: ntdll/kernel32 typically load at 0x7FF*'****'0000.
  // A preferred base here would always collide, forcing non-zero delta.
  if (image_base_ >= 0x7FF000000000ULL && image_base_ < 0x800000000000ULL)
    return true;

  // Low addresses that are typically reserved (below 64KB).
  if (image_base_ < 0x10000)
    return true;

  return false;
}

BinaryMemoryAnalysis::Result BinaryMemoryAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  return std::move(map_);
}

}  // namespace omill

#include "omill/Analysis/ExceptionInfo.h"

#include "omill/Analysis/BinaryMemoryMap.h"

#include <cstring>

namespace omill {

llvm::AnalysisKey ExceptionInfoAnalysis::Key;

ExceptionInfoAnalysis::Result ExceptionInfoAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  return std::move(info_);
}

// Synthetic DC base address — in an unused high VA range.
static constexpr uint64_t kSyntheticDCBase = 0x7FFE000000000000ULL;
static constexpr unsigned kDCSize = 0x50;  // 80 bytes
static constexpr unsigned kDCHandlerDataOffset = 0x38;
static constexpr unsigned kDCImageBaseOffset = 0x08;

// Synthetic CONTEXT base address — separate high VA range.
static constexpr uint64_t kSyntheticCtxBase = 0x7FFD000000000000ULL;
static constexpr unsigned kCtxSize = 0x100;  // 256 bytes (covers up to Rip+8)
static constexpr unsigned kCtxRipOffset = 0xF8;

void ExceptionInfo::buildSyntheticDCs(
    std::deque<std::vector<uint8_t>> &storage, BinaryMemoryMap &mem_map,
    uint64_t image_base) {
  uint64_t idx = 0;
  for (auto &entry : entries_) {
    if (entry.handler_data_va == 0) {
      ++idx;
      continue;
    }

    uint64_t dc_va = kSyntheticDCBase + idx * 0x100;
    storage.emplace_back(kDCSize, 0);
    auto &buf = storage.back();

    // [+0x38] = HandlerData VA
    std::memcpy(buf.data() + kDCHandlerDataOffset, &entry.handler_data_va,
                sizeof(uint64_t));
    // [+0x08] = ImageBase
    std::memcpy(buf.data() + kDCImageBaseOffset, &image_base, sizeof(uint64_t));

    mem_map.addRegion(dc_va, buf.data(), buf.size());
    entry.dc_synthetic_va = dc_va;

    // Build synthetic CONTEXT with Rip = begin_va (exception address).
    uint64_t ctx_va = kSyntheticCtxBase + idx * 0x200;
    storage.emplace_back(kCtxSize, 0);
    auto &ctx_buf = storage.back();
    std::memcpy(ctx_buf.data() + kCtxRipOffset, &entry.begin_va,
                sizeof(uint64_t));
    mem_map.addRegion(ctx_va, ctx_buf.data(), ctx_buf.size());
    entry.ctx_synthetic_va = ctx_va;

    ++idx;
  }
}

}  // namespace omill

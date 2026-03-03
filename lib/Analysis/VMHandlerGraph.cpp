#include "omill/Analysis/VMHandlerGraph.h"

#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <cstring>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

llvm::AnalysisKey VMHandlerGraphAnalysis::Key;

VMHandlerGraph VMHandlerGraphAnalysis::run(llvm::Module &,
                                           llvm::ModuleAnalysisManager &) {
  return std::move(graph_);
}

VMHandlerGraph::VMHandlerGraph(const BinaryMemoryMap &mem, uint64_t image_base,
                               uint64_t vmenter_va, uint64_t vmexit_va)
    : image_base_(image_base),
      vmenter_va_(vmenter_va),
      vmexit_va_(vmexit_va) {
  scanDispatchPatterns(mem);
  scanVMEntrySites(mem);
  buildHandlerGraph();
}

/// Try to extract an RVA from a `mov eXX, imm32` at an exact position.
/// Returns the RVA if the opcode matches, std::nullopt otherwise.
static std::optional<uint32_t> tryExtractMovRVA(const uint8_t *data, size_t pos,
                                                 size_t region_size,
                                                 uint8_t mov_opcode) {
  if (pos + 5 > region_size)
    return std::nullopt;
  if (data[pos] != mov_opcode)
    return std::nullopt;
  // Reject if preceded by REX prefix — would be mov r64, imm64 (10 bytes),
  // and the 4 bytes we'd extract are only the low half of a 64-bit immediate.
  if (pos > 0 && (data[pos - 1] & 0xF0) == 0x40)
    return std::nullopt;
  uint32_t rva;
  std::memcpy(&rva, &data[pos + 1], 4);
  return rva;
}

void VMHandlerGraph::scanDispatchPatterns(const BinaryMemoryMap &mem) {
  // Scan all regions for the dispatch epilogue pattern.
  //
  // Primary pattern (rax, 15 bytes):
  //   B8 xx xx xx xx              mov eax, <RVA32>
  //   49 03 84 24 E0 00 00 00     add rax, [r12+0xE0]
  //   FF E0                       jmp rax
  //
  // Register variants (rax-rdi):
  //   (B8+reg) xx xx xx xx        mov e<reg>, <RVA32>
  //   49 03 (84|reg<<3) 24 E0 00 00 00   add r<reg>, [r12+0xE0]
  //   FF (E0|reg)                 jmp r<reg>
  //
  // Register variants (r8-r15):
  //   41 (B8+(reg-8)) xx xx xx xx     mov e<reg>d, <RVA32>
  //   4D 03 (84|(reg-8)<<3) 24 E0 00 00 00  add r<reg>, [r12+0xE0]
  //   41 FF (E0|(reg-8))              jmp r<reg>

  // Upper bound on valid RVAs — anything beyond image size is bogus.
  uint64_t image_size = mem.imageSize();

  mem.forEachRegion([&](uint64_t base, const uint8_t *data, size_t size) {
    if (size < 15)
      return;

    for (size_t i = 0; i + 10 <= size; ++i) {
      // Look for the add+jmp core pattern first (most selective).
      // Pattern: REX 03 ModRM 24 E0 00 00 00 [41?] FF (E0|reg)
      //
      // Case 1: REX=49 (rax-rdi destination)
      //   49 03 ModRM 24 E0 00 00 00 FF (E0|reg)  — 10 bytes
      //
      // Case 2: REX=4D (r8-r15 destination)
      //   4D 03 ModRM 24 E0 00 00 00 41 FF (E0|reg)  — 11 bytes

      if (data[i + 1] != 0x03 || data[i + 3] != 0x24 ||
          data[i + 4] != 0xE0 || data[i + 5] != 0x00 ||
          data[i + 6] != 0x00 || data[i + 7] != 0x00)
        continue;

      uint8_t rex = data[i];
      uint8_t modrm = data[i + 2];

      // ModRM must be mod=10 (disp32), r/m=100 (SIB follows).
      if ((modrm & 0xC7) != 0x84)
        continue;

      uint8_t reg_field = (modrm >> 3) & 0x07;

      if (rex == 0x49) {
        // Case 1: rax-rdi variant.
        // Full pattern: (B8+reg) imm32 | 49 03 ModRM 24 E0000000 | FF (E0|reg)
        //               5 bytes          8 bytes                    2 bytes
        if (i + 10 > size)
          continue;
        if (data[i + 8] != 0xFF || data[i + 9] != (0xE0 | reg_field))
          continue;

        // The mov is exactly 5 bytes before the add — no backward scan.
        // Any gap means intervening instructions that could clobber the
        // register, and in practice EAC's dispatch has no gap.
        uint8_t mov_opcode = 0xB8 + reg_field;
        if (i < 5)
          continue;
        auto rva = tryExtractMovRVA(data, i - 5, size, mov_opcode);
        if (!rva || (image_size > 0 && *rva >= image_size))
          continue;

        uint64_t target_va = image_base_ + *rva;
        uint64_t dispatch_va = base + (i - 5);
        dispatch_targets_[dispatch_va] = target_va;
        dispatch_rvas_[dispatch_va] = *rva;
        rva_to_target_[*rva] = target_va;

      } else if (rex == 0x4D) {
        // Case 2: r8-r15 variant.
        // Full pattern: 41 (B8+reg) imm32 | 4D 03 ModRM 24 E0000000 | 41 FF (E0|reg)
        //               6 bytes              8 bytes                    3 bytes
        if (i + 11 > size)
          continue;
        if (data[i + 8] != 0x41 || data[i + 9] != 0xFF ||
            data[i + 10] != (0xE0 | reg_field))
          continue;

        // mov is 6 bytes before add: 41 prefix + B8+reg + imm32.
        uint8_t mov_opcode = 0xB8 + reg_field;
        if (i < 6)
          continue;
        if (data[i - 6] != 0x41)
          continue;
        auto rva = tryExtractMovRVA(data, i - 5, size, mov_opcode);
        if (!rva || (image_size > 0 && *rva >= image_size))
          continue;

        uint64_t target_va = image_base_ + *rva;
        uint64_t dispatch_va = base + (i - 6);  // Include 41 prefix.
        dispatch_targets_[dispatch_va] = target_va;
        dispatch_rvas_[dispatch_va] = *rva;
        rva_to_target_[*rva] = target_va;
      }
    }
  });

  llvm::errs() << "VMHandlerGraph: found " << dispatch_targets_.size()
               << " dispatch sites\n";
}

void VMHandlerGraph::scanVMEntrySites(const BinaryMemoryMap &mem) {
  // Scan for E8 (near call) instructions targeting vmenter_va.
  // call rel32: E8 xx xx xx xx  →  target = (addr + 5) + rel32

  mem.forEachRegion([&](uint64_t base, const uint8_t *data, size_t size) {
    if (size < 5)
      return;

    for (size_t i = 0; i + 5 <= size; ++i) {
      if (data[i] != 0xE8)
        continue;

      int32_t rel32;
      std::memcpy(&rel32, &data[i + 1], 4);
      uint64_t call_addr = base + i;
      uint64_t target = call_addr + 5 + static_cast<int64_t>(rel32);

      if (target == vmenter_va_) {
        // The instruction AFTER the call is the return address / next handler.
        // But for VM entry, the code before the call is the entry point we
        // want to track.  The handler that contains this call site is the
        // VM entry wrapper.
        //
        // Actually, in EAC's VM, vmenter is the first handler itself.
        // The call sites just tell us which non-VM functions transition
        // into the VM.  We add vmenter_va as a handler entry.
      }
    }
  });

  // Always include vmenter as a handler entry — it's the root of the graph.
  handler_set_.insert(vmenter_va_);
}

void VMHandlerGraph::buildHandlerGraph() {
  // Collect all unique target VAs from dispatch patterns.
  llvm::DenseSet<uint64_t> target_set;
  for (auto &[dispatch_addr, target_va] : dispatch_targets_) {
    target_set.insert(target_va);
  }

  // Add vmenter as a handler entry.
  target_set.insert(vmenter_va_);

  // All dispatch targets are potential handler entries.
  for (uint64_t va : target_set) {
    handler_set_.insert(va);
  }

  // Build sorted vectors.
  handler_entries_.assign(handler_set_.begin(), handler_set_.end());
  llvm::sort(handler_entries_);

  all_target_vas_.assign(target_set.begin(), target_set.end());
  llvm::sort(all_target_vas_);

  llvm::errs() << "VMHandlerGraph: " << handler_entries_.size()
               << " handler entries, " << all_target_vas_.size()
               << " unique targets\n";
}

std::optional<uint64_t>
VMHandlerGraph::getDispatchTarget(uint64_t dispatch_addr) const {
  auto it = dispatch_targets_.find(dispatch_addr);
  if (it != dispatch_targets_.end())
    return it->second;
  return std::nullopt;
}

std::optional<uint32_t>
VMHandlerGraph::getDispatchRVA(uint64_t dispatch_addr) const {
  auto it = dispatch_rvas_.find(dispatch_addr);
  if (it != dispatch_rvas_.end())
    return it->second;
  return std::nullopt;
}

std::optional<uint64_t> VMHandlerGraph::resolveRVA(uint32_t rva) const {
  auto it = rva_to_target_.find(rva);
  if (it != rva_to_target_.end())
    return it->second;
  return std::nullopt;
}

llvm::SmallVector<uint64_t, 4>
VMHandlerGraph::getHandlerTargets(uint64_t handler_va) const {
  // Find the range of binary addresses that belong to this handler.
  // A dispatch site at addr X belongs to handler H if H is the largest
  // handler entry <= X and X < next handler entry after H.

  auto it = std::upper_bound(handler_entries_.begin(), handler_entries_.end(),
                             handler_va);
  uint64_t next_handler =
      (it != handler_entries_.end()) ? *it : UINT64_MAX;

  llvm::SmallVector<uint64_t, 4> targets;
  llvm::DenseSet<uint64_t> seen;

  for (auto &[dispatch_addr, target_va] : dispatch_targets_) {
    if (dispatch_addr >= handler_va && dispatch_addr < next_handler) {
      if (seen.insert(target_va).second)
        targets.push_back(target_va);
    }
  }

  return targets;
}

}  // namespace omill

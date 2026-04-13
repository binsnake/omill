#pragma once

#include <cstdint>

#include "llvm/ADT/ArrayRef.h"
#include "omill/Arch/ArchABI.h"
#include "omill/BC/LiftDatabase.h"
#include "omill/BC/LiftTargetPolicy.h"

namespace remill {
class Arch;
}  // namespace remill

namespace omill {

class BinaryMemoryMap;
class VMTraceMap;

struct StaticLiftBuilderOptions {
  bool refresh_existing = false;
  bool compute_loops = true;
  bool compute_use_def = true;
};

struct StaticLiftOverlayKey {
  uint64_t handler_va = 0;
  uint64_t incoming_hash = 0;
};

class StaticLiftBuilder {
 public:
  StaticLiftBuilder(const remill::Arch *arch, const BinaryMemoryMap *memory_map,
                    TargetArch target_arch,
                    StaticLiftBuilderOptions options = {});

  bool buildFunction(uint64_t entry_va, LiftDatabase &db) const;
  bool buildFunctions(llvm::ArrayRef<uint64_t> entry_vas,
                      LiftDatabase &db) const;

  void importTraceMapAsOverlays(const VMTraceMap &trace_map,
                                llvm::ArrayRef<StaticLiftOverlayKey> overlay_keys,
                                LiftDatabase &db) const;

 private:
  const remill::Arch *arch_ = nullptr;
  const BinaryMemoryMap *memory_map_ = nullptr;
  TargetArch target_arch_ = TargetArch::kX86_64;
  StaticLiftBuilderOptions options_;
};

}  // namespace omill

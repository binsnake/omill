#pragma once

#include "omill/Analysis/VirtualModel/Types.h"

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/PassManager.h>

namespace llvm {
class Module;
}

namespace omill {

struct VirtualModelRunTelemetry {
  bool dirty_scope_requested = false;
  bool session_graph_projection_used = false;
  bool session_graph_handler_scope_used = false;
  bool session_graph_handler_projection_used = false;
  bool session_graph_boundary_projection_used = false;
  bool session_graph_vip_projection_used = false;
  bool session_graph_propagation_projection_used = false;
  bool session_graph_canonical_state_projection_used = false;
  bool session_graph_direct_callee_projection_used = false;
  bool session_graph_seed_projection_used = false;
  bool selected_handler_iteration_used = false;
  unsigned seed_handler_count = 0;
  unsigned summarized_handlers = 0;
  unsigned cached_summary_hits = 0;
  unsigned cached_summary_misses = 0;
  unsigned root_slice_cache_hits = 0;
  unsigned root_slice_cache_misses = 0;
  unsigned dispatch_handler_count = 0;
  unsigned callsite_handler_count = 0;
  unsigned exit_handler_count = 0;
  unsigned root_slice_count = 0;
  std::string scope_reason;
};

class VirtualMachineModel {
 public:
  llvm::ArrayRef<VirtualBoundaryInfo> boundaries() const { return boundaries_; }
  llvm::ArrayRef<VirtualHandlerSummary> handlers() const { return handlers_; }
  llvm::ArrayRef<VirtualStateSlotInfo> slots() const { return slots_; }
  llvm::ArrayRef<VirtualStackCellInfo> stackCells() const { return stack_cells_; }
  llvm::ArrayRef<VirtualRegionSummary> regions() const { return regions_; }
  llvm::ArrayRef<VirtualRootSliceSummary> rootSlices() const {
    return root_slices_;
  }
  const VirtualModelRunTelemetry &telemetry() const { return telemetry_; }

  const VirtualBoundaryInfo *lookupBoundary(llvm::StringRef name) const;
  const VirtualHandlerSummary *lookupHandler(llvm::StringRef name) const;
  const VirtualStateSlotInfo *lookupSlot(unsigned id) const;
  const VirtualRegionSummary *lookupRegion(unsigned id) const;
  const VirtualRegionSummary *lookupRegionForHandler(llvm::StringRef name) const;
  const VirtualRegionSummary *lookupRegionForBoundary(llvm::StringRef name) const;
  const VirtualRootSliceSummary *lookupRootSlice(uint64_t root_va) const;

  std::vector<const VirtualHandlerSummary *> candidateHandlers() const;

  std::vector<VirtualBoundaryInfo> &mutableBoundaries() { return boundaries_; }
  std::vector<VirtualStateSlotInfo> &mutableSlots() { return slots_; }
  std::vector<VirtualStackCellInfo> &mutableStackCells() { return stack_cells_; }
  std::vector<VirtualHandlerSummary> &mutableHandlers() { return handlers_; }
  std::vector<VirtualRegionSummary> &mutableRegions() { return regions_; }
  std::vector<VirtualRootSliceSummary> &mutableRootSlices() {
    return root_slices_;
  }
  VirtualModelRunTelemetry &mutableTelemetry() { return telemetry_; }

  bool empty() const {
    return boundaries_.empty() && slots_.empty() && stack_cells_.empty() &&
           handlers_.empty() && regions_.empty() && root_slices_.empty();
  }

  bool invalidate(llvm::Module &, const llvm::PreservedAnalyses &,
                  llvm::ModuleAnalysisManager::Invalidator &) {
    return false;
  }

 private:
  friend class VirtualMachineModelAnalysis;
  std::vector<VirtualBoundaryInfo> boundaries_;
  std::vector<VirtualStateSlotInfo> slots_;
  std::vector<VirtualStackCellInfo> stack_cells_;
  std::vector<VirtualHandlerSummary> handlers_;
  std::vector<VirtualRegionSummary> regions_;
  std::vector<VirtualRootSliceSummary> root_slices_;
  VirtualModelRunTelemetry telemetry_;
};

class VirtualMachineModelAnalysis
    : public llvm::AnalysisInfoMixin<VirtualMachineModelAnalysis> {
  friend llvm::AnalysisInfoMixin<VirtualMachineModelAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = VirtualMachineModel;

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

}  // namespace omill

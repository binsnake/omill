#include "omill/Analysis/VirtualModel/Analysis.h"

#include <algorithm>

#include <llvm/ADT/STLExtras.h>

namespace omill {

namespace {

static std::string normalizeBoundaryName(llvm::StringRef name) {
  return name.lower();
}

}  // namespace

const VirtualBoundaryInfo *VirtualMachineModel::lookupBoundary(
    llvm::StringRef name) const {
  auto needle = normalizeBoundaryName(name);
  auto it = std::find_if(boundaries_.begin(), boundaries_.end(),
                         [&](const VirtualBoundaryInfo &info) {
                           return normalizeBoundaryName(info.name) == needle;
                         });
  return (it == boundaries_.end()) ? nullptr : &*it;
}

const VirtualHandlerSummary *VirtualMachineModel::lookupHandler(
    llvm::StringRef name) const {
  auto it = std::find_if(handlers_.begin(), handlers_.end(),
                         [&](const VirtualHandlerSummary &summary) {
                           return summary.function_name == name;
                         });
  return (it == handlers_.end()) ? nullptr : &*it;
}

const VirtualStateSlotInfo *VirtualMachineModel::lookupSlot(unsigned id) const {
  auto it = std::find_if(slots_.begin(), slots_.end(),
                         [&](const VirtualStateSlotInfo &info) {
                           return info.id == id;
                         });
  return (it == slots_.end()) ? nullptr : &*it;
}

const VirtualRegionSummary *VirtualMachineModel::lookupRegion(unsigned id) const {
  auto it = std::find_if(regions_.begin(), regions_.end(),
                         [&](const VirtualRegionSummary &summary) {
                           return summary.id == id;
                         });
  return (it == regions_.end()) ? nullptr : &*it;
}

const VirtualRegionSummary *VirtualMachineModel::lookupRegionForHandler(
    llvm::StringRef name) const {
  auto needle = name.str();
  auto it = std::find_if(regions_.begin(), regions_.end(),
                         [&](const VirtualRegionSummary &summary) {
                           return llvm::is_contained(summary.handler_names,
                                                     needle);
                         });
  return (it == regions_.end()) ? nullptr : &*it;
}

const VirtualRegionSummary *VirtualMachineModel::lookupRegionForBoundary(
    llvm::StringRef name) const {
  auto needle = normalizeBoundaryName(name);
  auto it = std::find_if(regions_.begin(), regions_.end(),
                         [&](const VirtualRegionSummary &summary) {
                           return std::any_of(
                               summary.boundary_names.begin(),
                               summary.boundary_names.end(),
                               [&](const std::string &boundary_name) {
                                 return normalizeBoundaryName(boundary_name) ==
                                        needle;
                               });
                         });
  return (it == regions_.end()) ? nullptr : &*it;
}

const VirtualRootSliceSummary *VirtualMachineModel::lookupRootSlice(
    uint64_t root_va) const {
  auto it = std::find_if(root_slices_.begin(), root_slices_.end(),
                         [&](const VirtualRootSliceSummary &summary) {
                           return summary.root_va == root_va;
                         });
  return (it == root_slices_.end()) ? nullptr : &*it;
}

std::vector<const VirtualHandlerSummary *>
VirtualMachineModel::candidateHandlers() const {
  std::vector<const VirtualHandlerSummary *> candidates;
  for (const auto &summary : handlers_) {
    if (summary.is_candidate)
      candidates.push_back(&summary);
  }
  return candidates;
}

}  // namespace omill

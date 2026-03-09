#include "omill/Analysis/VMTraceMap.h"

#include <llvm/Support/raw_ostream.h>

#include <algorithm>

#include "omill/Analysis/VMTraceEmulator.h"

namespace omill {

llvm::AnalysisKey VMTraceMapAnalysis::Key;

VMTraceMap VMTraceMapAnalysis::run(llvm::Module &,
                                   llvm::ModuleAnalysisManager &) {
  return std::move(trace_map_);
}

void VMTraceMap::noteHandler(uint64_t va) {
  if (va == 0)
    return;
  if (handler_set_.insert(va).second)
    handler_entries_.push_back(va);
}

void VMTraceMap::sortHandlers() {
  llvm::sort(handler_entries_);
}

void VMTraceMap::recordTraceTargets(
    uint64_t handler_va, llvm::ArrayRef<uint64_t> successors) {
  noteHandler(handler_va);
  for (uint64_t succ : successors)
    noteHandler(succ);

  if (successors.empty()) {
    trace_targets_.erase(handler_va);
  } else {
    trace_targets_[handler_va] =
        llvm::SmallVector<uint64_t, 2>(successors.begin(), successors.end());
  }

  sortHandlers();
}

void VMTraceMap::rebuildAggregateTargets(uint64_t handler_va) {
  auto it = trace_records_.find(handler_va);
  if (it == trace_records_.end() || it->second.empty()) {
    trace_targets_.erase(handler_va);
    return;
  }

  llvm::SmallVector<uint64_t, 2> aggregate;
  llvm::DenseSet<uint64_t> seen;
  for (const auto &record : it->second) {
    for (uint64_t succ : record.successors) {
      if (succ != 0 && seen.insert(succ).second)
        aggregate.push_back(succ);
    }
  }

  if (aggregate.empty()) {
    trace_targets_.erase(handler_va);
  } else {
    trace_targets_[handler_va] = std::move(aggregate);
  }
}

void VMTraceMap::recordTrace(VMTraceRecord trace) {
  noteHandler(trace.handler_va);
  for (uint64_t succ : trace.successors)
    noteHandler(succ);

  auto &records = trace_records_[trace.handler_va];
  auto existing = std::find_if(records.begin(), records.end(),
                               [&](const VMTraceRecord &current) {
                                 return current.incoming_hash == trace.incoming_hash;
                               });
  if (existing == records.end())
    records.push_back(std::move(trace));
  else
    *existing = std::move(trace);

  rebuildAggregateTargets(trace.handler_va);
  sortHandlers();
}

void VMTraceMap::mergeTraceResults(const VMTraceEmulator &trace) {
  size_t handlers_before = handler_entries_.size();
  unsigned mapped = 0;

  for (const auto &entry : trace.traceEntries()) {
    VMTraceRecord record;
    record.handler_va = entry.handler_va;
    record.incoming_hash = entry.incoming_hash;
    record.outgoing_hash = entry.outgoing_hash;
    record.exit_target_va = entry.exit_target_va;
    record.native_target_va = entry.native_target_va;
    record.successors = entry.successors;
    record.passed_vmexit = entry.passed_vmexit;
    record.is_vmexit = entry.is_vmexit;
    record.is_error = entry.is_error;

    if (record.successors.empty() && record.is_vmexit && vmexit_va_ != 0)
      record.successors.push_back(vmexit_va_);

    recordTrace(std::move(record));
    if (!entry.successors.empty() || entry.is_vmexit)
      ++mapped;
  }

  sortHandlers();

  llvm::errs() << "VMTraceMap: merged " << trace.traceEntries().size()
               << " trace entries ("
               << (handler_entries_.size() - handlers_before)
               << " new handlers, " << mapped << " mapped dispatches)\n";
}

llvm::SmallVector<uint64_t, 2>
VMTraceMap::getTraceTargets(uint64_t handler_va) const {
  auto it = trace_targets_.find(handler_va);
  if (it != trace_targets_.end())
    return it->second;
  return {};
}

std::optional<VMTraceRecord>
VMTraceMap::getTraceForHash(uint64_t handler_va, uint64_t incoming_hash) const {
  auto it = trace_records_.find(handler_va);
  if (it == trace_records_.end())
    return std::nullopt;
  auto match = std::find_if(it->second.begin(), it->second.end(),
                            [&](const VMTraceRecord &record) {
                              return record.incoming_hash == incoming_hash;
                            });
  if (match == it->second.end())
    return std::nullopt;
  return *match;
}

llvm::ArrayRef<VMTraceRecord>
VMTraceMap::getTraceRecords(uint64_t handler_va) const {
  auto it = trace_records_.find(handler_va);
  if (it == trace_records_.end())
    return {};
  return it->second;
}

VMFlatTraceResult
VMTraceMap::followFlatTrace(uint64_t handler_va, uint64_t incoming_hash,
                            unsigned max_steps) const {
  VMFlatTraceResult result;
  result.stop_handler_va = handler_va;
  result.stop_hash = incoming_hash;

  auto pack = [](uint64_t handler, uint64_t hash) {
    return hash ^ (handler + 0x9E3779B97F4A7C15ull + (hash << 6) + (hash >> 2));
  };

  llvm::DenseSet<uint64_t> visited;
  uint64_t current_handler = handler_va;
  uint64_t current_hash = incoming_hash;

  for (unsigned step = 0; step < max_steps; ++step) {
    uint64_t key = pack(current_handler, current_hash);
    if (!visited.insert(key).second) {
      result.stop_reason = VMFlatTraceStopReason::LoopDetected;
      result.stop_handler_va = current_handler;
      result.stop_hash = current_hash;
      return result;
    }

    auto record = getTraceForHash(current_handler, current_hash);
    if (!record) {
      result.stop_reason = VMFlatTraceStopReason::MissingRecord;
      result.stop_handler_va = current_handler;
      result.stop_hash = current_hash;
      return result;
    }

    result.records.push_back(*record);
    result.stop_handler_va = record->handler_va;
    result.stop_hash = record->incoming_hash;

    if (record->is_error) {
      result.stop_reason = VMFlatTraceStopReason::Error;
      return result;
    }

    if (record->is_vmexit &&
        (record->successors.empty() ||
         (record->successors.size() == 1 && record->successors.front() == vmexit_va_))) {
      result.stop_reason = VMFlatTraceStopReason::VmExit;
      return result;
    }

    if (record->successors.size() != 1) {
      result.stop_reason = VMFlatTraceStopReason::AmbiguousSuccessor;
      return result;
    }

    uint64_t next_handler = record->successors.front();
    if (next_handler == 0 || next_handler == vmexit_va_) {
      result.stop_reason = VMFlatTraceStopReason::VmExit;
      return result;
    }

    current_handler = next_handler;
    current_hash = record->outgoing_hash != 0 ? record->outgoing_hash : current_hash;
  }

  result.stop_reason = VMFlatTraceStopReason::StepLimit;
  result.stop_handler_va = current_handler;
  result.stop_hash = current_hash;
  return result;
}

}  // namespace omill
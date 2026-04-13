#include "omill/BC/LiftDatabase.h"

#include <algorithm>

namespace omill {
namespace {

template <typename T>
static void PushUnique(std::vector<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

}  // namespace

LiftDbManifest &LiftDatabase::manifest(void) {
  return manifest_;
}

const LiftDbManifest &LiftDatabase::manifest(void) const {
  return manifest_;
}

LiftDbFunctionRecord &LiftDatabase::upsertFunction(uint64_t entry_va) {
  auto &record = functions_[entry_va];
  record.entry_va = entry_va;
  return record;
}

LiftDbBasicBlockRecord &LiftDatabase::upsertBlock(uint64_t function_entry_va,
                                                  uint64_t block_entry_va) {
  auto &function = upsertFunction(function_entry_va);
  auto &record = blocks_[block_entry_va];
  record.entry_va = block_entry_va;
  record.function_entry_va = function_entry_va;
  PushUnique(function.block_entries, block_entry_va);
  return record;
}

LiftDbInstructionRecord &LiftDatabase::upsertInstruction(uint64_t va) {
  auto &record = instructions_[va];
  record.va = va;
  return record;
}

LiftDbTraceOverlayRecord &LiftDatabase::upsertTraceOverlay(
    const std::string &overlay_key) {
  auto &record = trace_overlays_[overlay_key];
  record.overlay_key = overlay_key;
  return record;
}

LiftDbFunctionRecord *LiftDatabase::function(uint64_t entry_va) {
  auto it = functions_.find(entry_va);
  return it == functions_.end() ? nullptr : &it->second;
}

const LiftDbFunctionRecord *LiftDatabase::function(uint64_t entry_va) const {
  auto it = functions_.find(entry_va);
  return it == functions_.end() ? nullptr : &it->second;
}

LiftDbBasicBlockRecord *LiftDatabase::block(uint64_t entry_va) {
  auto it = blocks_.find(entry_va);
  return it == blocks_.end() ? nullptr : &it->second;
}

const LiftDbBasicBlockRecord *LiftDatabase::block(uint64_t entry_va) const {
  auto it = blocks_.find(entry_va);
  return it == blocks_.end() ? nullptr : &it->second;
}

LiftDbInstructionRecord *LiftDatabase::instruction(uint64_t va) {
  auto it = instructions_.find(va);
  return it == instructions_.end() ? nullptr : &it->second;
}

const LiftDbInstructionRecord *LiftDatabase::instruction(uint64_t va) const {
  auto it = instructions_.find(va);
  return it == instructions_.end() ? nullptr : &it->second;
}

LiftDbTraceOverlayRecord *LiftDatabase::traceOverlay(
    const std::string &overlay_key) {
  auto it = trace_overlays_.find(overlay_key);
  return it == trace_overlays_.end() ? nullptr : &it->second;
}

const LiftDbTraceOverlayRecord *LiftDatabase::traceOverlay(
    const std::string &overlay_key) const {
  auto it = trace_overlays_.find(overlay_key);
  return it == trace_overlays_.end() ? nullptr : &it->second;
}

const std::map<uint64_t, LiftDbFunctionRecord> &LiftDatabase::functions(
    void) const {
  return functions_;
}

const std::map<uint64_t, LiftDbBasicBlockRecord> &LiftDatabase::blocks(
    void) const {
  return blocks_;
}

const std::map<uint64_t, LiftDbInstructionRecord> &LiftDatabase::instructions(
    void) const {
  return instructions_;
}

const std::map<std::string, LiftDbTraceOverlayRecord> &
LiftDatabase::traceOverlays(void) const {
  return trace_overlays_;
}

void LiftDatabase::clearFunction(uint64_t entry_va) {
  auto func_it = functions_.find(entry_va);
  if (func_it == functions_.end()) {
    return;
  }

  for (auto block_entry_va : func_it->second.block_entries) {
    auto block_it = blocks_.find(block_entry_va);
    if (block_it == blocks_.end()) {
      continue;
    }
    for (auto inst_va : block_it->second.instruction_vas) {
      instructions_.erase(inst_va);
    }
    blocks_.erase(block_it);
  }

  functions_.erase(func_it);
}

void LiftDatabase::rebuildPredecessors(uint64_t function_entry_va) {
  auto *function = this->function(function_entry_va);
  if (!function) {
    return;
  }

  for (auto block_entry_va : function->block_entries) {
    if (auto *bb = block(block_entry_va)) {
      bb->predecessors.clear();
    }
  }

  for (auto block_entry_va : function->block_entries) {
    auto *bb = block(block_entry_va);
    if (!bb) {
      continue;
    }
    for (const auto &edge : bb->successors) {
      auto *succ = block(edge.target_block_va);
      if (!succ) {
        continue;
      }
      PushUnique(succ->predecessors, bb->entry_va);
    }
  }
}

void LiftDatabase::bumpRevision(void) {
  ++manifest_.db_revision;
}

std::string LiftDbOverlayKey(uint64_t handler_va, uint64_t incoming_hash) {
  return std::to_string(handler_va) + ":" + std::to_string(incoming_hash);
}

}  // namespace omill

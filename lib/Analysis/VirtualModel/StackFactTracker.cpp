#include "Analysis/VirtualModel/Internal.h"

#include <set>

namespace omill::virtual_model::detail {

namespace {

using MaterializedStackKey = std::tuple<unsigned, int64_t, unsigned>;

std::optional<int64_t> stackBaseDeltaForExpr(const VirtualValueExpr &expr,
                                            unsigned slot_id) {
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id == slot_id)
    return 0;

  if (expr.kind == VirtualExprKind::kStackCell && expr.slot_id == slot_id &&
      expr.stack_offset.has_value()) {
    return *expr.stack_offset;
  }

  if ((expr.kind == VirtualExprKind::kAdd || expr.kind == VirtualExprKind::kSub) &&
      expr.operands.size() == 2) {
    if (auto nested = stackBaseDeltaForExpr(expr.operands[0], slot_id);
        nested && expr.operands[1].constant.has_value()) {
      int64_t delta = static_cast<int64_t>(*expr.operands[1].constant);
      if (expr.kind == VirtualExprKind::kSub)
        delta = -delta;
      return *nested + delta;
    }
    if (expr.kind == VirtualExprKind::kAdd &&
        expr.operands[0].constant.has_value()) {
      if (auto nested = stackBaseDeltaForExpr(expr.operands[1], slot_id)) {
        return *nested + static_cast<int64_t>(*expr.operands[0].constant);
      }
    }
  }

  return std::nullopt;
}

void mergeMaterializedStackFact(std::map<unsigned, VirtualValueExpr> &dst,
                                unsigned cell_id,
                                const VirtualValueExpr &value) {
  auto it = dst.find(cell_id);
  if (it == dst.end()) {
    dst.emplace(cell_id, value);
    return;
  }
  if (exprEquals(it->second, value))
    return;
  if (auto merged = mergeIncomingExpr(it->second, value)) {
    it->second = std::move(*merged);
    return;
  }
  it->second = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                : value.bit_width);
}

void mergeMaterializedStructuralFact(
    std::map<StackCellKey, VirtualValueExpr> &dst, const StackCellKey &key,
    const VirtualValueExpr &value) {
  auto it = dst.find(key);
  if (it == dst.end()) {
    dst.emplace(key, value);
    return;
  }
  if (exprEquals(it->second, value))
    return;
  if (auto merged = mergeIncomingExpr(it->second, value)) {
    it->second = std::move(*merged);
    return;
  }
  it->second = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                : value.bit_width);
}

std::optional<unsigned> resolveBaseSlotIdForSummary(
    const VirtualMachineModel &model, const VirtualStackCellSummary &summary) {
  if (summary.canonical_base_slot_id.has_value())
    return summary.canonical_base_slot_id;

  auto slot_ids = buildSlotIdMap(model);
  VirtualStateSlotSummary slot;
  slot.base_name = summary.base_name;
  slot.offset = summary.base_offset;
  slot.width = summary.base_width;
  slot.from_argument = summary.base_from_argument;
  slot.from_alloca = summary.base_from_alloca;
  return lookupSlotIdForSummary(slot, slot_ids);
}

}  // namespace

std::optional<int64_t> inferTrackedStackBaseDeltaForSlot(
    const std::map<unsigned, VirtualValueExpr> &slot_facts, unsigned slot_id) {
  std::optional<int64_t> found_delta;

  auto consider_delta = [&](const VirtualValueExpr &value) {
    auto delta = stackBaseDeltaForExpr(value, slot_id);
    if (!delta)
      return true;
    if (!found_delta) {
      found_delta = *delta;
      return true;
    }
    return *found_delta == *delta;
  };

  if (auto it = slot_facts.find(slot_id); it != slot_facts.end()) {
    if (!consider_delta(it->second))
      return std::nullopt;
  }
  for (const auto &[fact_slot_id, value] : slot_facts) {
    if (fact_slot_id == slot_id)
      continue;
    if (!consider_delta(value))
      return std::nullopt;
  }

  return found_delta;
}

bool mergeTrackedStackFact(TrackedFactState &state,
                           const CanonicalStackFactKey &key,
                           const VirtualValueExpr &value) {
  auto it = state.stack_facts.find(key);
  if (it == state.stack_facts.end()) {
    state.stack_facts.emplace(key, value);
    return true;
  }
  if (exprEquals(it->second, value))
    return false;
  if (auto merged = mergeIncomingExpr(it->second, value)) {
    if (!exprEquals(it->second, *merged)) {
      it->second = std::move(*merged);
      return true;
    }
    return false;
  }
  auto unknown = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                  : value.bit_width);
  if (!exprEquals(it->second, unknown)) {
    it->second = std::move(unknown);
    return true;
  }
  return false;
}

std::optional<CanonicalStackFactKey> canonicalStackFactKeyForCellId(
    const VirtualMachineModel &model, const TrackedFactState &state,
    unsigned cell_id) {
  auto cell_info = buildStackCellInfoMap(model);
  auto it = cell_info.find(cell_id);
  if (it == cell_info.end())
    return std::nullopt;

  int64_t delta = 0;
  if (auto delta_it = state.stack_base_deltas.find(it->second->base_slot_id);
      delta_it != state.stack_base_deltas.end()) {
    delta = delta_it->second;
  }

  return CanonicalStackFactKey{it->second->base_slot_id,
                               it->second->cell_offset - delta,
                               it->second->width};
}

std::optional<CanonicalStackFactKey> canonicalStackFactKeyForSummary(
    const VirtualMachineModel &model, const TrackedFactState &state,
    const VirtualStackCellSummary &summary) {
  auto base_slot_id = resolveBaseSlotIdForSummary(model, summary);
  if (!base_slot_id)
    return std::nullopt;

  int64_t delta = 0;
  if (auto delta_it = state.stack_base_deltas.find(*base_slot_id);
      delta_it != state.stack_base_deltas.end()) {
    delta = delta_it->second;
  }

  return CanonicalStackFactKey{*base_slot_id, summary.offset - delta,
                               summary.width};
}

bool assignTrackedStackFactForCellId(const VirtualMachineModel &model,
                                     TrackedFactState &state, unsigned cell_id,
                                     const VirtualValueExpr &value) {
  auto key = canonicalStackFactKeyForCellId(model, state, cell_id);
  if (!key)
    return false;
  bool changed = mergeTrackedStackFact(state, *key, value);
  state.materialized_stack_facts = materializeTrackedStackFacts(model, state);
  return changed;
}

bool assignTrackedStackFactForSummary(const VirtualMachineModel &model,
                                      TrackedFactState &state,
                                      const VirtualStackCellSummary &summary,
                                      const VirtualValueExpr &value) {
  auto key = canonicalStackFactKeyForSummary(model, state, summary);
  if (!key)
    return false;
  bool changed = mergeTrackedStackFact(state, *key, value);
  state.materialized_stack_facts = materializeTrackedStackFacts(model, state);
  return changed;
}

std::map<unsigned, VirtualValueExpr> materializeTrackedStackFacts(
    const VirtualMachineModel &model, const TrackedFactState &state) {
  std::map<MaterializedStackKey, unsigned> cell_ids;
  for (const auto &cell : model.stackCells()) {
    cell_ids.emplace(MaterializedStackKey{cell.base_slot_id, cell.cell_offset,
                                          cell.width},
                     cell.id);
  }

  std::map<unsigned, VirtualValueExpr> materialized;
  for (const auto &[key, value] : state.stack_facts) {
    int64_t delta = 0;
    if (auto delta_it = state.stack_base_deltas.find(key.base_slot_id);
        delta_it != state.stack_base_deltas.end()) {
      delta = delta_it->second;
    }
    auto current_offset = key.cell_offset + delta;
    auto id_it =
        cell_ids.find(MaterializedStackKey{key.base_slot_id, current_offset,
                                           key.width});
    if (id_it == cell_ids.end())
      continue;
    mergeMaterializedStackFact(materialized, id_it->second, value);
  }

  return materialized;
}

std::map<StackCellKey, VirtualValueExpr> materializeTrackedStructuralStackFacts(
    const VirtualMachineModel &model, const TrackedFactState &state) {
  auto slot_info = buildSlotInfoMap(model);
  std::map<StackCellKey, VirtualValueExpr> materialized;
  for (const auto &[key, value] : state.stack_facts) {
    auto slot_it = slot_info.find(key.base_slot_id);
    if (slot_it == slot_info.end())
      continue;
    int64_t delta = 0;
    if (auto delta_it = state.stack_base_deltas.find(key.base_slot_id);
        delta_it != state.stack_base_deltas.end()) {
      delta = delta_it->second;
    }
    StackCellKey structural{
        SlotKey{slot_it->second->base_name, slot_it->second->offset,
                slot_it->second->width, slot_it->second->from_argument,
                slot_it->second->from_alloca},
        key.cell_offset + delta, key.width};
    mergeMaterializedStructuralFact(materialized, structural, value);
  }
  return materialized;
}

llvm::SmallDenseSet<unsigned, 16> materializeTrackedWrittenStackCellIds(
    const VirtualMachineModel &model, const TrackedFactState &state,
    const std::set<CanonicalStackFactKey> &written_stack_keys) {
  std::map<MaterializedStackKey, unsigned> cell_ids;
  for (const auto &cell : model.stackCells()) {
    cell_ids.emplace(MaterializedStackKey{cell.base_slot_id, cell.cell_offset,
                                          cell.width},
                     cell.id);
  }

  llvm::SmallDenseSet<unsigned, 16> materialized;
  for (const auto &key : written_stack_keys) {
    int64_t delta = 0;
    if (auto delta_it = state.stack_base_deltas.find(key.base_slot_id);
        delta_it != state.stack_base_deltas.end()) {
      delta = delta_it->second;
    }
    auto it = cell_ids.find(MaterializedStackKey{key.base_slot_id,
                                                 key.cell_offset + delta,
                                                 key.width});
    if (it != cell_ids.end())
      materialized.insert(it->second);
  }
  return materialized;
}

void normalizeLocalizedOutgoingFacts(const VirtualMachineModel &model,
                                     CallsiteLocalizedOutgoingFacts &localized) {
  localized.tracked_state =
      buildTrackedFactState(model, localized.outgoing_slots,
                            localized.outgoing_stack,
                            &localized.structural_outgoing_stack);

  std::set<CanonicalStackFactKey> normalized_written_keys =
      localized.written_stack_keys;

  for (unsigned cell_id : localized.written_stack_cell_ids) {
    if (auto key =
            canonicalStackFactKeyForCellId(model, localized.tracked_state,
                                           cell_id)) {
      normalized_written_keys.insert(*key);
    }
  }

  for (const auto &structural_key : localized.written_structural_stack_keys) {
    VirtualStackCellSummary summary;
    summary.base_name = structural_key.base_slot.base_name;
    summary.base_offset = structural_key.base_slot.offset;
    summary.base_width = structural_key.base_slot.width;
    summary.base_from_argument = structural_key.base_slot.from_argument;
    summary.base_from_alloca = structural_key.base_slot.from_alloca;
    summary.offset = structural_key.cell_offset;
    summary.width = structural_key.width;
    if (auto key =
            canonicalStackFactKeyForSummary(model, localized.tracked_state,
                                            summary)) {
      normalized_written_keys.insert(*key);
    }
  }

  localized.written_stack_keys = std::move(normalized_written_keys);
  localized.outgoing_stack = localized.tracked_state.materialized_stack_facts;
  localized.structural_outgoing_stack =
      materializeTrackedStructuralStackFacts(model, localized.tracked_state);
  localized.written_stack_cell_ids.clear();
  for (unsigned cell_id : materializeTrackedWrittenStackCellIds(
           model, localized.tracked_state, localized.written_stack_keys)) {
    localized.written_stack_cell_ids.insert(cell_id);
  }
}

TrackedFactState buildTrackedFactState(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &slot_facts,
    const std::map<unsigned, VirtualValueExpr> &stack_facts,
    const std::map<StackCellKey, VirtualValueExpr> *structural_stack_facts) {
  TrackedFactState state;
  state.slot_facts = slot_facts;
  refreshTrackedFactState(model, state);

  for (const auto &[cell_id, value] : stack_facts)
    (void) assignTrackedStackFactForCellId(model, state, cell_id, value);

  if (structural_stack_facts) {
    for (const auto &[key, value] : *structural_stack_facts) {
      VirtualStackCellSummary summary;
      summary.base_name = key.base_slot.base_name;
      summary.base_offset = key.base_slot.offset;
      summary.base_width = key.base_slot.width;
      summary.base_from_argument = key.base_slot.from_argument;
      summary.base_from_alloca = key.base_slot.from_alloca;
      summary.offset = key.cell_offset;
      summary.width = key.width;
      (void) assignTrackedStackFactForSummary(model, state, summary, value);
    }
  }

  state.materialized_stack_facts = materializeTrackedStackFacts(model, state);
  return state;
}

void refreshTrackedFactState(const VirtualMachineModel &model,
                             TrackedFactState &state) {
  state.stack_base_deltas.clear();
  for (const auto &slot : model.slots()) {
    if (auto delta =
            inferTrackedStackBaseDeltaForSlot(state.slot_facts, slot.id)) {
      state.stack_base_deltas.emplace(slot.id, *delta);
    }
  }
  state.materialized_stack_facts = materializeTrackedStackFacts(model, state);
}

std::optional<TrackedStackLookupResult> lookupTrackedStackFact(
    const VirtualMachineModel &model, const TrackedFactState &state,
    const VirtualStackCellSummary &summary) {
  auto base_slot_id = resolveBaseSlotIdForSummary(model, summary);
  if (!base_slot_id)
    return std::nullopt;

  int64_t delta = 0;
  if (auto delta_it = state.stack_base_deltas.find(*base_slot_id);
      delta_it != state.stack_base_deltas.end()) {
    delta = delta_it->second;
  }

  std::set<CanonicalStackFactKey> candidates;
  auto add_candidate = [&](int64_t offset) {
    candidates.insert(
        CanonicalStackFactKey{*base_slot_id, offset, summary.width});
  };

  add_candidate(summary.offset);
  add_candidate(summary.offset - delta);
  if (delta != 0) {
    add_candidate(summary.offset + delta);
    add_candidate(summary.offset - (2 * delta));
    add_candidate(summary.offset + (2 * delta));
  }

  bool first = true;
  for (const auto &candidate : candidates) {
    auto it = state.stack_facts.find(candidate);
    if (it == state.stack_facts.end())
      continue;
    return TrackedStackLookupResult{candidate, it->second, !first};
  }

  return std::nullopt;
}

VirtualValueExpr resolveTrackedStackExpr(
    const VirtualMachineModel &model, const TrackedFactState &state,
    const VirtualValueExpr &expr, const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids, unsigned depth) {
  if (depth >= 6)
    return expr;

  auto summary = extractStackCellSummaryFromExpr(expr, exprByteWidth(expr));
  if (summary) {
    if (auto resolved = lookupTrackedStackFact(model, state, *summary);
        resolved && !exprEquals(resolved->value, expr)) {
      auto nested = resolveTrackedStackExpr(model, state, resolved->value,
                                            slot_ids, stack_cell_ids,
                                            depth + 1);
      annotateExprSlots(nested, slot_ids);
      annotateExprStackCells(nested, stack_cell_ids, slot_ids);
      return nested;
    }
  }

  if (expr.operands.empty())
    return expr;

  VirtualValueExpr rewritten = expr;
  rewritten.operands.clear();
  rewritten.operands.reserve(expr.operands.size());
  bool changed = false;
  for (const auto &operand : expr.operands) {
    auto resolved = resolveTrackedStackExpr(model, state, operand, slot_ids,
                                            stack_cell_ids, depth + 1);
    if (!exprEquals(resolved, operand))
      changed = true;
    rewritten.operands.push_back(std::move(resolved));
  }

  if (!changed)
    return expr;
  annotateExprSlots(rewritten, slot_ids);
  annotateExprStackCells(rewritten, stack_cell_ids, slot_ids);
  return rewritten;
}

}  // namespace omill::virtual_model::detail

# Devirtualization Rework Plan

## Goal
Collapse the current devirtualization pipeline into a single library-owned graph/session engine with one source of truth for discovery, exit state, and materialization.

## Problem Summary
The current pipeline spreads ownership across:
- `IterativeLiftingSession`
- `DevirtualizationSession`
- projected `SessionGraphState`
- runtime output-recovery loops
- driver callback policy in `tools/omill-lift/main.cpp`

That creates duplicate representations for the same facts: unresolved exits, frontier work, edge facts, boundary facts, closure work items, and late recovery state.

## Target Architecture
1. One canonical session owns all iterative devirtualization state.
2. Discovered control-flow facts are represented once as typed graph entities.
3. Iteration is fixed-phase and library-owned.
4. ABI/no-ABI lowering consumes stable graph state after convergence.
5. The driver becomes orchestration-only.
6. `VirtualMachineModel` becomes a derived view, not a co-owner of mutable truth.

## Canonical Data Model
- `RegionId(entry_pc, vip_context, mode)`
- `ExitId(region_id, site_index)`
- `BoundaryId(target_pc)`

Canonical records:
- `RegionRecord`
- `ExitRecord`
- `BoundaryRecord`
- `NormalizedUnitCacheEntry`

Properties currently split across `FrontierWorkItem`, `UnresolvedExitSite`, `SessionEdgeFact`, `SessionBoundaryFact`, and closure items should converge into these records.

## Fixed Iteration Loop
1. Seed roots.
2. Discover dirty exits.
3. Lift missing regions.
4. Normalize lifted regions.
5. Recompute dirty summaries/model state only.
6. Resolve exits and classify boundaries.
7. Repeat until no dirty graph records remain.
8. Materialize CFG.
9. Run final ABI/no-ABI shaping.
10. Verify invariants.

## Migration Order
### Slice 1: Remove duplicated frontier state
- Keep one canonical frontier/edge store in `DevirtualizationSession`.
- Delete session-owned compatibility mirrors like:
  - `late_frontier`
  - `late_frontier_identities`
  - `discovered_frontier_pcs`
  - `discovered_frontier_identities`
  - `discovered_frontier_work_items`
  - `late_frontier_work_items`
- Derive compatibility outputs from canonical edge facts when needed.

### Slice 2: Stop graph projection round-trips
- Remove `publishSessionGraphProjection` / `findSessionGraphProjection` as mutable synchronization glue.
- Feed virtual-model dirty scope from one immutable session snapshot or direct session-owned state.

### Slice 3: Fold output recovery into normal iteration
- Replace runtime callback-driven frontier replay with session-owned actions.
- Treat child imports, boundary replay, and closure discovery as ordinary graph work.

### Slice 4: Collapse `IterativeLiftingSession` into the devirtualization session boundary
- Move pending target scheduling and lift graph ownership under the same canonical session.
- Leave `IterativeLiftingSession` as a thin lifting backend or remove it entirely.

## Current Implementation Decision
Proceed with Slice 1 first. It is the highest-leverage simplification that can land without rewriting the whole pipeline:
- it reduces duplicate mutable state immediately,
- it removes synchronization code,
- it is compatible with later graph/session unification.

## Acceptance For Slice 1
- `DevirtualizationSession` has one canonical frontier representation.
- compatibility frontier lists are removed or reduced to derived outputs only.
- orchestrator refresh no longer rebuilds multiple frontier mirrors.
- targeted devirtualization build/tests still pass.

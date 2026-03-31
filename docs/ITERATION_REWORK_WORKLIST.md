# Iteration Rework Work List

## Summary

This is the canonical active backlog for the current devirtualization rework.
It replaces milestone-first tracking with an architecture-first work list.

The current primary problems are:

1. iteration ownership is still split between `DevirtualizationSession`,
   `main.cpp`, and ABI late-cleanup loops
2. `VirtualMachineModel` still reruns at whole-module scope instead of
   dirty/frontier scope
3. discovery, bookkeeping, and lowering are still entangled, so newly found
   edges can be reclassified or collapsed before the session finishes
   iterating on them

Sample-specific ABI and nested-child polish is blocked behind these iteration
tracks except for crash fixes needed to keep default and compact runs usable.

## Active Tracks

### Track A: Session-Owned Iteration

Required outcomes:

- `DevirtualizationSession` is the only owner of iterative work state
- `main.cpp` no longer owns late ABI or no-ABI iteration policy
- frontier items, continuation discovery, retry state, child-root import
  decisions, and failure reasons all live in library code

Current work:

- move `abi_late_vm_continuations`, `abi_late_output_root_closure`, and nested
  VM-enter child-import control out of `main.cpp` and into orchestrator-owned
  APIs
- keep `late_frontier`, discovered-PC lists, and similar structures as derived
  compatibility views only
- remove remaining module-rescan fallback scheduling from active iteration
  paths
- make secondary-root and nested-child recovery use the same session work queue
  instead of driver-local loops

Completion criteria:

- `main.cpp` is orchestration-only for iterative devirtualization
- every newly discovered target is durable session work with kind, status, and
  failure reason
- no late ABI or no-ABI loop decides iteration policy locally

### Track B: Dirty-Scope Virtual-Model Iteration

Required outcomes:

- `VirtualMachineModelAnalysis::run` stops recomputing full propagation and
  summarization for the whole module on every late iteration
- analysis phases operate on dirty/frontier subsets whenever possible

Current work:

- split virtual-model execution into explicit reusable phases:
  - state propagation
  - dispatch and callsite summarization
  - root-slice summarization
  - materialization support data
- introduce dirty-handler, dirty-root, and dirty-callsite scoping so late
  iterations only rerun affected subsets
- preserve stable phase outputs between iterations instead of rebuilding them
  from scratch
- make late invalidation depend on newly lifted units, changed unresolved
  exits, and changed frontier classifications only

Completion criteria:

- late iteration cost is dominated by changed subgraphs, not full-model reruns
- whole-model phase-3.8-style recomputation is no longer the default
- iteration telemetry reports dirty scope, reused scope, and why a rerun
  happened

### Track C: Separate Edge Discovery From Lowering

Required outcomes:

- discovery and classification do not immediately force final ABI or no-ABI
  lowering decisions
- lowering consumes stable session and bookkeeping state after iteration
  converges for that scope

Current work:

- represent resolved edges, boundary classifications, VM-enter edges, and
  native-reenter edges as session facts first
- move ABI and no-ABI canonicalization to a narrower consume-stable-state stage
- enforce stable precedence rules:
  - explicit `vm_enter` and `nested_vm_enter` modeling beats decoder heuristics
  - native-reenter edges keep continuation data until lowering consumes them
  - executable placeholders are not collapsed only because a direct call is
    decodable
- preserve imported nested-child frontier and boundary state until parent
  integration is complete

Completion criteria:

- ABI finalization cannot rewrite a tracked nested VM-enter region into a plain
  native target unless the session explicitly reclassified it
- native-reenter stubs, VM-enter placeholders, and executable-target
  placeholders all come from one stable policy layer

## Blocked Follow-On Tracks

### Track D: Nested Child Recovery

This track is blocked by Tracks A-C except for crash triage.

Required outcomes:

- nested VM-enter child import becomes safe and generic
- default and compact use the same library-owned mechanism
- the env-gated child-import path can be retired

Current work:

- keep `OMILL_ENABLE_NESTED_VM_ENTER_CHILD_IMPORT` as a probe only until the
  compact late-frontier crash is explained
- after Tracks A-C land, reintroduce nested-child import through the session
  work queue instead of a driver hook
- preserve child unresolved edges and reenter stubs during parent integration
- only then resume deeper ABI semantic flattening of imported children

Completion criteria:

- default and compact both survive nested-child import in the normal path
- no env gate is required for nested VM-enter recursion
- imported child closure is not a special-case ABI feature

## Current Known Regressions

- Compact ABI normal path still crashes during late ABI frontier advancement
  after `abi_late_vm_continuations`. This is the main crash blocker for Track A.
- Default nested-child import probe is stable with
  `OMILL_ENABLE_NESTED_VM_ENTER_CHILD_IMPORT=1`, but that path is still
  experimental and not safe to enable generally.
- `VirtualMachineModelAnalysis::run` still spends late iteration time in
  whole-model propagation and downstream summarization instead of frontier- or
  dirty-scoped recomputation.

## Acceptance Checks

Required validation for the rework:

- unit coverage proving session-owned frontier advancement is library-only
- coverage proving no ABI or no-ABI late iteration policy remains in `main.cpp`
- tests for explicit VM-enter precedence over decoded direct native targets
- tests for native-reenter bookkeeping surviving until lowering
- tests for dirty-scope virtual-model reruns only touching changed
  handlers/sites
- regression checks for:
  - default ABI normal path
  - compact ABI normal path
  - default ABI nested-child probe path
  - compact nested-child probe crash reproduction until fixed

Acceptance gates before resuming broader ABI polish:

- default and compact ABI are both clean on the normal path
- nested-child import is safe for both, or remains explicitly blocked with a
  documented reason
- no whole-module fallback scan or whole-model rerun is required for late
  iteration in the common path

## Historical Notes / Moved Items

- `docs/GENERIC_STATIC_DEVIRTUALIZATION_TODO.md` remains the historical
  implementation log for generic devirtualization milestones and sample
  outcomes.
- `docs/ITERATIVE_LIFTING_TODO.md` remains a historical checklist for the
  original iterative-lifting rollout.
- `docs/VMP_DNA_PORTING_PLAN.md` remains the architecture reference note for
  the Dna-inspired direction, not the active execution backlog.

When moving items out of the old TODOs:

- move corpus-specific ABI polish under Track D unless it is a crash blocker
  for Tracks A-C
- move old milestone-style notes into history sections with short pointers only
- keep active blockers summarized here instead of duplicating them across
  multiple docs

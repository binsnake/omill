# Dna Strategy Porting Plan

## Summary

Port the architectural strengths of `Dna-master` into `omill` without porting its
trace-first VMProtect pipeline. The target shape is a library-owned,
block-lift-first devirtualization flow where one session owns discovery,
unresolved exits remain explicit typed state, every lift unit is normalized
before reuse, and CFG materialization consumes cached normalized units instead
of wrapper-heavy or driver-owned recovery logic.

This note is the stable reference for the redesign work and should be updated as
the implementation moves forward.

## Core Principles

1. One `DevirtualizationSession` owns iterative state.
2. Unresolved exits are typed state, not implicit pipeline failures.
3. Cache normalized lift units, not raw partially lowered IR.
4. Remill normalization is a hard gate before reuse or materialization.
5. Materialization composes cached normalized units and explicit exit state.
6. The CLI is only a thin request/event layer.

## Session Ownership

`DevirtualizationSession` should own:

- discovered roots and frontier PCs
- unresolved exit sites and their completeness state
- dirty functions and newly lifted functions
- normalized block-cache entries
- invalidation reasons and round telemetry
- epoch summaries for machine-checkable diagnostics

Driver logic in `tools/omill-lift/main.cpp` should not own late replay policy,
sample-specific recovery policy, or frontier scheduling.

## Unresolved Exit Model

Use a typed unresolved-exit subsystem:

- `UnresolvedExitKind`
  - dispatch jump
  - dispatch call
  - protected boundary
  - unknown continuation
- `ExitCompleteness`
  - complete
  - incomplete
  - invalidated
- `ExitEvidence`
  - resolved targets
  - predecessor count
  - last epoch touched
  - invalidation reason

Rules:

- unresolved exits remain first-class session state until proven complete
- completeness is monotonic unless new predecessor evidence invalidates it
- frontier scheduling comes from unresolved-exit state, not module rescans
- materialization must preserve incomplete exits explicitly

## Normalized Lift-Unit Cache

The session owns a normalized cache keyed by:

- VA
- lift mode
- target architecture

Cache entries track:

- the normalized lifted function or block
- discovered exits
- dirty dependencies
- exported facts needed by materialization
- cache status: fresh, reused, invalidated

Rules:

- only admit units after Remill normalization completes
- relift cache misses or invalidated units only
- repeated continuation discovery updates metadata without rebuilding stable
  units

## Normalization Gate

Remill normalization is a hard gate:

- every newly lifted or dirtied unit must be normalized before analysis or cache
  admission
- materialization must consume normalized cache entries only
- leaked `__remill_*` runtime or control-flow artifacts block admission for
  epochs that require canonical state
- legacy `__omill_dispatch_*` names are compatibility inputs only and should be
  normalized away immediately

## VIP And Control State

Virtual control state should be modeled explicitly instead of inferred from
late dispatch cleanup or sample-specific heuristics. The generic virtual-model
pipeline is now the source of truth for this data, with VMProtect-specific
heuristics layered on top.

Core model additions:

- `VirtualInstructionPointerSummary`
  - canonical VIP carrier
  - expression before and after dispatch
  - resolved virtual PC when constant
  - source kind such as named slot, stack cell, bytecode read, or dispatch
    operand
- `VirtualExitSummary`
  - exit disposition
  - native target when known
  - continuation VIP and continuation PC when known
  - stack-delta classification relative to handler entry
  - partial-exit, full-exit, and re-entry flags

Classification rules:

- `vmenter` is any boundary that seeds canonical VIP state and crosses from
  native control into virtual control
- `vmexit` is terminal only when VIP leaves virtual control and no virtual
  continuation is proven
- a native call from the VM is represented as a partial exit when a native or
  boundary-like target is paired with continuation VIP or stack-delta evidence
- loops are keyed by normalized VIP state, not only by lifted function identity

The virtual-model pipeline should recover VIP from the strongest available
evidence in this order:

1. existing `NEXT_PC` facts
2. dispatch-specialized targets
3. bytecode-derived reads feeding dispatch
4. handler-local structural loads that feed indirect dispatch

Trace or emulator data remains optional corroboration only:

- `VMTraceMap` can enrich exit summaries with `passed_vmexit`, `is_vmexit`,
  native targets, and trace successors
- static VIP and exit classification must not depend on trace availability
- callers that want trace corroboration must register `VMTraceMapAnalysis`
  explicitly

Session ownership implications:

- unresolved exits should carry VIP-at-site and continuation VIP where known
- normalized cache entries should record whether VIP is resolved, symbolic, or
  still unknown
- frontier scheduling should use VIP-aware identities so the same lifted
  function can be revisited under distinct virtual states when required

## Phases

The devirtualization pipeline should run in these fixed phases:

1. Initial lift and normalization
2. Detection and seed extraction
3. Frontier scheduling from unresolved exits
4. Incremental block lift
5. Normalization and cache admission
6. CFG materialization from cached normalized units
7. Continuation closure and invalidation check
8. Final ABI or no-ABI shaping
9. Final invariant verification

Each phase should emit telemetry for:

- units lifted
- units reused
- unresolved exits complete, incomplete, invalidated
- normalization failures
- dispatches materialized
- leaked runtime artifacts

## Compact Fixed-Point Bundle

Keep Dna's useful fixed-point idea, but only as a compact canonicalization
bundle used where phase ordering matters:

- resolved-dispatch lowering
- Remill semantics/runtime lowering already required by normalization
- simple folding and CFG cleanup needed for materialization
- a limited rerun budget scoped to dirty units only

This bundle belongs in the library pipeline, not the CLI driver.

## Explicit Non-Goals

Do not port:

- trace-first handler lifting
- compile-to-exe or reload loops
- Dna's parameterized register-alloca ABI model
- hardcoded VMProtect register-role assumptions from Dna
- any workflow that abandons the single LLVM module/session as the main source
  of truth

## Test Expectations

Focused tests should cover:

- unresolved-exit completeness transitions and invalidation
- cache reuse when a round discovers no invalidating changes
- normalization as a hard requirement before cache admission
- materialization from cached normalized units without `_native` wrappers
- consistency between model-level resolved targets and final dispatch rewrites
- compatibility acceptance of legacy dispatch names while final outputs remain
  canonical
- absence of sample-name or export-VA branching in production scheduling

End-to-end acceptance should continue to cover:

- `Corpus.dll`
- `CorpusVMP.compact.dll`
- `CorpusVMP.default.dll`

Required output assertions:

- detect -> schedule -> lift -> normalize -> cache -> materialize -> finalize
  event flow
- cache reuse on repeated or expanding rounds where applicable
- no leaked Remill memory/runtime/control-flow artifacts
- no wrapper ladders in finalized output
- no production-path `Corpus*` special casing

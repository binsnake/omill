# Iterative Lifting Rework Plan

## Summary

- Start from a separate local worktree on `codex/iterative-lifting-arch` at
  `D:\binsnake\omill-iterative-arch`, created from the current `HEAD`.
- The main architectural issue is that iterative discovery is split across two
  incompatible models: trace-based lifting plus late fresh-module relifting,
  and block-based lifting plus merge-back.
- The second core issue is that cross-function state stays memory-backed for
  too long. `OptimizeState` only promotes intra-function state and flushes
  around calls, while ABI recovery recreates large local state/stack allocas in
  wrappers, which is why late cleanup is needed just to rediscover constants.
- The rework should make block-level lifting the single iterative substrate,
  keep one long-lived Remill/LLVM session, move all discoverability before ABI
  recovery, and treat virtual context as a summarized cross-function value flow
  instead of something re-materialized into allocas at each boundary.

## Key Changes

- Add a single long-lived `IterativeLiftingSession` object, owned by
  `omill-lift`, that holds one `LLVMContext`, one Remill `Arch`, one semantics
  module, one binary memory map, one canonical output module, and the discovery
  caches.
- Make `BlockLifter`-style lifting the canonical discovery engine. Keep Remill
  instruction lifting, but stop using recursive `TraceLifter` as the iterative
  backbone.
- Replace the current `TraceLiftAnalysis` / `BlockLiftAnalysis` callback split
  with one session-backed analysis/service that can lift a new block, resolve
  an unresolved edge in-place, and mark affected blocks/functions dirty for
  scoped re-optimization.
- Introduce a first-class `LiftGraph` with block nodes and typed control-flow
  edges.
- Remove the late fresh-module relift/link path entirely once parity is
  reached.
- Delay semantic-body/internalization cleanup until discovery is closed.
- Replace the current narrow IPCP with summary-driven propagation based on a
  `VirtualContextSummary`.
- Add a `ContextSSARewriter` stage before ABI recovery.
- Narrow ABI recovery to a final lowering stage.
- Fold VM-specific side channels into the same architecture.

## Public Interfaces / Types

- Add `IterativeLiftingSession` as the single mutable lifting service exposed
  to the pass pipeline.
- Add `LiftGraph`, `LiftNode`, and `LiftEdge` types to represent discovered
  code and pending/resolved control flow.
- Add `VirtualContextSummary` and `ContextSSARewriter` as the cross-function
  state abstraction.
- Keep CLI flags stable (`--resolve-targets`, `--block-lift`), but internally
  reinterpret `--block-lift` as the default discovery architecture over time.
- Keep output naming stable for `sub_<va>` and `_native` functions after
  convergence.

## Test Plan

- Add unit coverage for one-session discovery without duplicate lifted
  definitions.
- Extend block-lift tests to cover iterative promotion of indirect edges into
  direct ones and merge-back to stable `sub_<va>` functions.
- Add cross-function context tests proving that non-escaping vmcontext/state
  slots stay in SSA across direct-call chains.
- Add regression tests for current late-discovery cases.
- Keep existing target resolution, VM dispatch, ABI recovery, and block-lift
  tests passing during migration.

## Assumptions

- Isolation is via local worktree, not remote fork.
- The isolation worktree is created from current `HEAD`.
- Public CLI behavior stays compatible; internal C++ APIs and pass boundaries
  may change substantially.
- The intended end state is one iterative architecture, not permanent support
  for both trace-first and block-first discovery paths.

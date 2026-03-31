# Iterative Lifting Todo

## Active Backlog

The active iteration backlog has moved to `docs/ITERATION_REWORK_WORKLIST.md`.

Use that file as the canonical source of truth for current iteration work.
Keep this document as the historical checklist for the original iterative
lifting rollout and items that have already landed.

- [x] Introduce a shared iterative lifting session and lift graph.
- [x] Move iterative target/block discovery onto the shared session.
- [x] Remove the late fresh-module relift path and keep one long-lived lifting world.
- [x] Rework the pipeline into pre-resolution, iterative, boundary, and final cleanup epochs.
- [x] Register iterative/session analyses consistently in tools and test harnesses.
- [x] Make the session the real scheduler for iterative work.
  Use dirty nodes and unresolved edges to drive reruns before falling back to whole-module scans.
- [ ] Make lifted-function discovery fully session-owned.
  Collapse the remaining split between `LiftedFunctionAnalysis` and the mutable session state.
- [ ] Separate resolved-edge bookkeeping from final dispatch lowering.
  Let the graph/session represent newly resolved direct targets first, then run a narrower lowering sweep over those edges.
- [x] Add per-iteration summaries to the session.
- [x] Add driver-side iteration telemetry and unresolved-edge reporting.
- [x] Add stalled-convergence diagnostics.
  Report whether unresolved edges are still dynamic, missing lifted targets, or otherwise blocked.
- [ ] Make block-lift the default iterative substrate and keep trace-lift as a compatibility path.
- [ ] Scope ABI reruns and late cleanup strictly to newly lifted or newly dirtied functions.
- [ ] Convert late constant `inttoptr` call sites into named/direct lifted calls in final ABI artifacts.
  Compact VM samples now complete in block-lift mode, but the final IL still carries many constant direct-call encodings instead of recovered direct edges.
- [x] Add a medium-complexity integration corpus before moving to the nastiest binaries.
  Initial coverage now includes iterative-pipeline e2e runs for `cw_combined` and `ollvm_sha256`.
- [ ] Run the compact/default VMP corpus differential on the stabilized block-lift path.
  The compact corpus is now good enough to use as the baseline before moving to `CorpusVMP.default.dll`.
- [ ] Remove the remaining whole-module fallback scan from iterative scheduling.
  Once all discovery paths mark the session consistently, the scheduler should never need to rediscover affected functions by rescanning the module.

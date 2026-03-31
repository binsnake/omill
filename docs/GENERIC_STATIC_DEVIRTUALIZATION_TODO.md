# Generic Static Devirtualization Todo

## Active Backlog

The active architecture-first backlog has moved to
`docs/ITERATION_REWORK_WORKLIST.md`.

Use that file as the canonical source of truth for current iteration work.
Keep this document as the historical implementation log for generic
devirtualization milestones, sample results, and older investigation notes.

## Goal

Build a generic, static devirtualization pipeline that does not depend on
concrete traces, VM-specific emulators, or hardcoded handler semantics.

## Progress

- [x] Create a dedicated generic virtualization analysis/model separate from
  legacy trace-driven VM passes.
- [x] Register the generic virtualization model as a module analysis.
- [x] Add initial unit coverage for generic protected-boundary detection and
  handler/state-summary recovery from IR shape alone.
- [x] Recover initial symbolic dispatch expressions and state-transfer
  summaries from candidate handlers without using trace data.
- [x] Canonicalize recovered virtual-state slots into stable symbolic IDs
  across handlers.
- [x] Propagate initial abstract virtual-state facts across direct handler
  calls to a module-local fixpoint.
- [x] Materialize resolved virtual-handler CFG edges back into normal lifted IR.
- [x] Materialize resolved constant dispatches to protected VM boundaries as
  explicit named `vm_entry_*` edges.
- [x] Support compare-driven symbolic dispatch expressions (`icmp` +
  `select`) in the generic expression model and materializer.
- [x] Preserve small conflicting incoming abstract facts as finite `phi`
  choice sets instead of collapsing them immediately to `unknown`.
- [x] Materialize small finite multi-target dispatches as structured CFG
  (`switch` / direct-call cases) instead of leaving opaque dispatches.
- [x] Add analysis-level regression coverage proving conflicting incoming
  handler facts survive as `phi(...)` summaries instead of degrading to
  `unknown`.
- [x] Make exhaustive `phi`-choice dispatch materialization erase the original
  opaque dispatch fallback instead of keeping it in an unreachable default path.
- [x] Add driver wiring for generic static devirtualization so it can be run on
  real samples without relying on legacy VM-specific passes.
- [x] Summarize boundary-adjacent connected candidate-handler regions so the
  model can reason about helper chains near protected VM handoff points.
- [x] Use region-level abstract facts as a fallback when materializing
  boundary-adjacent dispatches that depend on helper side effects across a
  protected helper chain.
- [x] Extend the generic model with explicit dispatch-successor summaries and
  root-slice summaries (`reachable`, `frontier`, `closed`).
- [x] Make generic materialization iterative and root-scoped, including
  boundary continuation into already-lifted canonical targets.
- [x] Add bounded generic handler specialization for root-scoped,
  callsite-dependent dispatches.
- [x] Gate specialization and devirtualization rewrites behind semantic
  validation.
- [x] Run structure-recovery cleanup only after a root slice is actually
  closed.
- [x] Enrich the abstract state/model so helper-written control-transfer state
  like `NEXT_PC` can become a resolved successor instead of a permanent
  `dynamic_target` frontier.
- [x] Model remill memory helper reads/writes and rebase bounded VM-stack facts
  across constant stack-pointer updates.
- [x] Propagate bounded non-state argument facts (including root/lifted entry
  PCs) through the generic model so local helper/root stores of `argN + const`
  can collapse before materialization.
- [x] Normalize virtual slot / stack-cell width handling so nested symbolic
  `slot(...)` and `stack(...)` expressions can canonicalize back to the same
  byte-sized slot/cell IDs used by propagated facts.
- [x] Repair direct-callee helper fact import so structurally described
  slot/stack expressions remap back into caller-local coordinates before
  root-slice dispatch summarization.
- [x] Rebase direct-callee written stack-cell IDs alongside rebased outgoing
  stack facts, so SP-delta helpers still import their caller-local VM-stack
  writes after stack-pointer adjustment.
- [x] Import leaf-helper effects from callsite-local specialized summaries
  instead of only the globally merged helper summary, so unrelated helper
  callsites stop polluting compact's final `RETURN_PC` / `NEXT_PC` chain.
- [x] Skip terminal `__remill_missing_block` stubs during closed-slice ABI
  wrapper recovery, so verifier-clean ABI output does not try to native-wrap
  synthetic fallback blocks.

## Ordered Remaining Work

These items should be finished before moving on to the full end-to-end
validation sweep.

1. Repo-wide cleanup and deletion of legacy compatibility paths
   - [ ] Remove the remaining `_native` wrapper machinery from the production
     devirtualization pipeline, not just bypass it.
   - [x] Gate wrapper-derived late discovery and trace-emulator enrichment in
     `omill-lift` when `disable_native_wrappers` is enabled, so direct mode
     does not keep running `_native`-shaped helper discovery paths that it
     will never materialize.
   - [x] Fix or retire legacy wrapper-era rewrite assumptions that still show
     up in focused coverage, including
     `RewriteLiftedCallsToNativeTest.ClosedRootSliceScopeSkipsUnmarkedCallers`.
   - [x] Remove remaining production-path renaming/mirroring of Remill
     control-flow/runtime symbols under `__omill_*`; keep raw `__remill_*`
     naming canonical internally and in final outputs.
   - [x] Delete or quarantine leftover production-path sample-specific
     `Corpus*` helpers/fixups so corpus knowledge lives only in regression
     harnesses, manifests, or debug adapters.
   - [x] Audit the tree for remaining wrapper-ladder and legacy-dispatch
     assumptions in passes, tests, and cleanup stages.

2. Finish wiring explicit exit semantics through materialization/final lowering
   - [ ] Make `VirtualCFGMaterialization` and related final-lowering passes
     consume `VirtualExitDisposition` directly for:
     - `kStayInVm`
     - `kVmExitTerminal`
     - `kVmExitNativeCallReenter`
     - `kVmExitNativeExecUnknownReturn`
     - `kVmEnter`
     - `kNestedVmEnter`
   - [x] Preserve partial exits and native-call/re-entry metadata explicitly
     instead of flattening them back into generic unresolved dispatch.
   - [x] Preserve virtual-exit attrs through declared-continuation,
     continuation-shim, and constant missing-block rewrites, including fallback
     to callee-carried exit metadata when the callsite is still bare.
   - [x] Ensure terminal exits, native calls, and continuation edges stay
     distinguishable in finalized ABI and no-ABI output.

3. Strengthen VIP-aware iterative behavior and invalidation rules
   - [x] Treat the same lifted function reached under different VIP states as
     distinct frontier/invalidation work where required.
   - [x] Add stronger loop/re-entry handling across continuation closure so
     revisiting a handler with the same normalized VIP state converges
     cleanly, while distinct VIP states remain separable.
   - [x] Expand unresolved-exit completeness/invalidation bookkeeping to use
     VIP-aware identities consistently across scheduling, cache reuse, and
     continuation closure.

4. Broaden VIP/control-state regression coverage
   - [x] Add stress tests for loops that revisit the same lifted function under
     different VIP states.
   - [x] Add regression coverage for native calls from inside the VM that do
     not represent full `vmexit`.
   - [x] Add nested re-entry / nested `vmenter` coverage.
   - [x] Add dispatch/materialization consistency checks proving that if the
     model resolves VIP/exit state, materialization lowers the same control
     shape.

5. Wire optional trace corroboration cleanly
   - [x] Expose `VMTraceMap` corroboration only through explicitly registered
     analysis users; do not make it a hidden requirement of the static model.
   - [x] Add tests showing trace evidence can refine or corroborate
     `VirtualExitSummary` without changing the static pipeline's source of
     truth.
   - [x] Keep trace support strictly optional for the generic static
     devirtualization path.

6. Full end-to-end validation
   - [ ] Run the full `Corpus.dll`, `CorpusVMP.compact.dll`, and
     `CorpusVMP.default.dll` matrix after the cleanup/integration items above
     are complete.
   - [ ] Extend the acceptance assertions to check VIP-aware lifecycle output,
     including `vmenter`, `vmexit`, native-call/re-enter, loop handling, and
     absence of leaked wrapper/legacy-dispatch artifacts.

## Current Slice

- Added `VirtualMachineModelAnalysis` as the new generic substrate.
- The model currently records:
  - protected boundary declarations/functions
  - candidate handler functions
  - dispatch intrinsic counts
  - generic state-like slot reads/writes off a common base
- It now also records:
  - structured symbolic summaries for dispatch targets
  - structured symbolic summaries for state-slot transfers
  - canonical virtual-state slot IDs shared across handlers
  - incoming/outgoing abstract facts propagated across direct handler calls
  - root-scoped specialization seeds for specialized generic handler clones
- A new `VirtualCFGMaterializationPass` now consumes those facts and rewrites
  proven constant dispatches into direct lifted callsites / musttail edges.
- It now also rewrites proven constant dispatches to recognized protected
  boundary stubs into explicit named boundary calls such as `vm_entry_<va>`.
- The generic expression model now understands integer comparisons, which lets
  the materializer collapse compare-driven `select` dispatches when abstract
  facts make the predicate constant.
- Direct-call fact propagation now keeps small conflicting values as explicit
  `phi` choices, which allows the materializer to recover multi-target
  dispatch structure instead of losing that information to `unknown`.
- The model now also groups connected candidate handlers that touch a protected
  boundary into region summaries, including merged live/written slots and
  region-level incoming/outgoing abstract facts.
- The generic materializer now consults those region summaries when a handler's
  own outgoing facts are not enough to resolve a dispatch, which helps with
  helper-written state that only becomes visible across a boundary-adjacent
  region.
- The generic materializer now also performs bounded root-scoped callsite
  specialization for unresolved handlers when a reachable direct callsite
  supplies constant slot facts; specialized clones carry explicit
  specialization attrs/facts so the generic model can re-analyze them on the
  next iteration.
- The verified generic materializer now snapshots the pre-pass module and, when
  Z3 validation is enabled, restores any changed preexisting function whose
  rewrite fails semantic validation instead of aborting the whole run.
- Closed root slices now annotate their reachable functions with explicit
  `omill.closed_root_slice*` attrs plus a module scope flag so post-closure
  cleanup and ABI/native recovery only run on actually-closed generic slices.
- Tiny closed-slice `blk_*` / `block_*` helpers are now marked for inlining
  before boundary cleanup, and the existing signature-recovery /
  lifted-to-native / state-elimination passes now honor closed-slice scoping.
- `omill-lift` now exposes generic static devirtualization through dedicated
  driver flags:
  - `--generic-static-devirtualize`
  - `--verify-generic-static-devirtualization`
  - `--dump-virtual-model`
- This is intentionally VM-agnostic and does not read from `VMTraceMap`,
  `VMTraceEmulator`, or other legacy trace-driven machinery.

## Notes

- Legacy VM-specific passes remain in the tree for compatibility, but they are
  not part of this new design direction.
- Real compact-corpus status:
  - `TvmpBytecodeVm` no longer stops at `vm_entry_180042ba4` in the generic
    `--no-abi` path; the root-scoped materializer now continues that boundary
    into lifted `blk_180055365`.
  - Z3-backed validation is now enabled in the main build and the verified
    materializer regression path is exercised locally, including rollback on
    forced validation failure and musttail-preserving jump rewrites.
  - Bounded callsite specialization is now implemented and unit-tested, but it
    does not change the current compact frontier because the remaining edge in
    `blk_180064933` is not callsite-constant; it still depends on helper-written
    `NEXT_PC`.
- The root-scoped compact no-ABI slice now closes end-to-end again:
  `compact_vm_generic_model.calllocal1.noabi.txt` reports
  `reachable=16 frontier=0 closed=true`, and
  `CorpusVMP.compact.vm.block.generic-on.calllocal1.noabi.ll` contains no
  `__omill_dispatch_jump` and no `vm_entry_*` references.
- Closed-slice cleanup / recovery scoping now fires on the compact sample too:
  the regenerated IR carries `omill.closed_root_slice*` attrs/module flags and
  the previously open `blk_180064933` dispatch is rewritten into a direct edge.
- The remaining caveat is output quality rather than dispatch closure:
  the final compact successor currently materializes as
  `blk_ffffffffac9b1737`, a lifted missing-block stub that ends in
  `__remill_missing_block`. So the generic path now closes the reachable slice
  structurally, but further lifting/continuation work is still needed if we
  want that final post-VM edge to look like recovered original code instead of
  a terminal missing-block shim.
- The compact ABI path now also closes cleanly and verifies under
  `--verify-each`: `compact_vm_generic_model.calllocal2.verifyabi.txt`
  reports `reachable=16 frontier=0 closed=true`, the emitted ABI LL has zero
  `__omill_dispatch_jump` and zero `vm_entry_*`, and `llvm-as` accepts the
  output without errors.
- The ABI verifier failure was caused by trying to recover a `_native` wrapper
  for the synthetic missing-block fallback `blk_ffffffffac9b1737`. Closed-slice
  ABI recovery now skips terminal `__remill_missing_block` stubs, so the ABI
  path remains verifier-clean while still keeping the fallback edge explicit.
- Terminal synthetic missing-block shims now collapse one step further in the
  generic materializer. On the compact sample, the no-ABI IR now tails directly
  to `__remill_missing_block` instead of materializing a surviving
  `blk_ffffffffac9b1737` symbol, and the ABI/native path lowers that terminal
  edge to `__omill_missing_block_handler` without generating invalid
  `ret void poison` IR. Fresh artifacts
  `CorpusVMP.compact.vm.block.generic-on.stubcollapse4.noabi.ll` and
  `CorpusVMP.compact.vm.block.generic-on.stubcollapse4.verifyabi.ll` keep
  `frontier=0 closed=true`, contain zero `__omill_dispatch_jump` / `vm_entry_*`
  refs, and verify cleanly under `--verify-each` plus `llvm-as`.
- Closed-slice ABI recovery now force-inlines small `blk_*_native` /
  `block_*_native` helpers before the post-ABI inliner, while still preserving
  outlined VM wrappers and registry-marked virtual callees. On the compact
  sample, fresh artifact
  `CorpusVMP.compact.vm.block.generic-on.nativeinline1.verifyabi.ll` keeps
  `frontier=0 closed=true`, zero `__omill_dispatch_jump`, and zero `vm_entry_*`
  refs, but reduces the ABI wrapper ladder from `7` `_native` definitions / `60`
  `_native` call edges in `...stubcollapse4.verifyabi.ll` down to just
  `sub_180001850_native` with `0` remaining `_native` call edges. The terminal
  missing-block edge stays explicit as `__omill_missing_block_handler`. The
  next output-quality gap is now narrower: the compact ABI artifact still has
  `6` lifted `blk_*` continuation declarations/calls inside the monolithic
  root wrapper, so the next cleanup target is lifted-to-native continuation
  collapse rather than more wrapper-chain inlining.
- Investigated that continuation-cleanup gap directly with a new
  root-slice continuation-discovery pass. The useful finding is architectural:
  the remaining compact `blk_*` continuation calls live in the reachable
  lifted body (`sub_180001850`) rather than only in the `_native` wrapper, so
  any continuation lifting must follow the closed-slice direct-call closure,
  not just scan `_native` helpers. A pre-ABI experimental pass now exists
  behind `OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY=1`; it lifts
  declared `blk_*` continuations from that reachable closed-slice graph and
  has env-gated round diagnostics under
  `OMILL_DEBUG_LATE_CLOSED_SLICE_CONTINUATION=1`.
- Current compact result for that experimental continuation discovery is mixed,
  not shippable: it safely extends the slice and can lift multiple continuation
  rounds before ABI recovery, but it exposes deeper continuation layers faster
  than the current ABI/native cleanup can collapse them. In practice the
  compact default artifact remains the known-good baseline
  `...nativeinline1.verifyabi.ll` (`6` lifted `blk_*` declare/call edges),
  while the experimental artifacts (`...latecont10/11/12.verifyabi.ll`) trade
  some of those first-layer declarations for deeper ones plus additional
  `_native` helpers. Because that is not yet a net quality win, the discovery
  pass is intentionally disabled by default while we work on the follow-up:
  post-lift continuation collapse/cleanup between rounds.
- Helper-written out-parameter facts now remap back onto caller-local slots,
  including named allocas like `NEXT_PC`, and there is unit coverage proving a
  helper-written `NEXT_PC` chain can now collapse a `dispatch_jump` to a direct
  edge. On the real compact sample, though, the remaining frontier still feeds
  through a stack/memory-derived `POPI`/`LEAI`/`JMPI` chain, so the target is
  more precise than before but still not constant.
- The generic model now has a bounded VM-stack memory domain keyed by
  stack-base slot + constant offset, and helper summaries preserve/import those
  stack-memory effects across direct calls and region facts. Unit coverage now
  proves a `PUSHI`-style helper can write a constant target into VM stack
  memory, a `POPI`-style helper can reload it into `NEXT_PC`, and the generic
  materializer resolves the resulting dispatch to a direct edge. Unsupported
  stack offsets now surface as `unsupported_memory_target` root-slice
  frontiers instead of anonymous `dynamic_target`s.
- Fresh compact validation is working again in this checkout through the
  block-lift driver path (`--block-lift`). The earlier apparent CLI "hang" was
  the wrong trace-lift path for this sample; the generic compact artifact now
  regenerates successfully in about 46s end-to-end.
- The new bounded stack-memory domain does not fire on the real compact sample
  yet (`stack_cells 0` in the dumped model), which means the remaining
  `POPI` / `LEAI` / `JMPI` case is narrower than simple stack-slot recovery:
  it still needs pointer/value recovery through helper semantics rather than
  only stack-base + constant-offset tracking.
- The generic model now understands `__remill_read_memory_*` /
  `__remill_write_memory_*` helper semantics as bounded VM-stack effects, and
  propagation rebases those stack facts across constant `SP` updates. On the
  compact sample this materially improved the final frontier:
  `compact_vm_generic_model.rebase1.noabi.txt` now reports `stack_cells 13`
  instead of `0`, `POPI` resolves to `stack(slot(arg1+0x908)+0x0)` instead of
  plain `unknown`, and the root frontier reason tightened to
  `unsupported_memory_target`.
- The generic model now also propagates bounded argument facts across lifted
  roots and direct helper/block calls, seeded from known lifted entry VAs.
  There is unit coverage proving an `omill.output_root` can now fold a local
  `program_counter + const` state write to a concrete outgoing fact, and the
  compact sample no longer crashes the generic pass when that propagation is
  enabled because unsupported/deep argument expressions are explicitly dropped
  instead of being merged unboundedly.
- Direct-callee propagation now also maps simple caller facts into callee
  live-ins through the actual call operand mapping, with regression coverage
  for helpers that access state through argument-relative slots rather than the
  caller's raw slot numbering. Identity-style callee writebacks also no longer
  clobber a more precise caller-local constant fact.
- Direct-callee effect import now also repairs caller-local slot/stack
  coordinates for helper outputs that were still expressed structurally
  (`slot(argN+off)` / `stack(slot(argN+off)+cell)`), even when the imported
  expression no longer carried a usable canonical slot/cell ID. There is new
  unit coverage for the concrete helper-relative VM-stack case that originally
  showed up in compact: a helper taking state in a nonstandard argument
  position can now still write `NEXT_PC` through caller-local facts and drive
  direct materialization.
- On the real compact sample, the helper-import repair plus callsite-local
  leaf-helper effect import were the pair that finally closed the slice.
  First the model stopped leaking helper-relative `stack(slot(arg1+0x908)+0x0)`
  state into `blk_180064933`; then the leaf-helper local import stopped
  unrelated `CALLI` / `LEAI` / `JMPI` callsites from polluting the final
  `RETURN_PC` / `NEXT_PC` chain with merged `phi` / `unknown` values.
- The virtual-model dump now prints the canonical slot and stack-cell tables,
  which made it possible to diagnose a real canonicalization bug: nested
  symbolic slot/cell expressions were being matched using bit widths while the
  canonical slot summaries use byte widths. That mismatch is now fixed in the
  expression annotator and summary builders.
- On `CorpusVMP.compact.dll`, that new argument-fact propagation concretely
  improves the model but does not close the slice yet:
  `compact_vm_generic_model.argfacts3.noabi.txt` still reports
  `reachable=15 frontier=1 closed=false`, but the root now carries at least
  one concrete entry-PC-derived outgoing fact (`out slot[32] = 0x1800041c0`)
  instead of leaving all such local `arg1 + const` stores symbolic.
- After the slot-width canonicalization fix, the compact root still remains
  open (`compact_vm_generic_model.widthfix1.noabi.txt` reports
  `reachable=15 frontier=1 closed=false`), but the surviving frontier is now
  clearly expressed in terms of canonical state aliases like
  `slot(arg0+0x918)`, `slot(arg0+0x8e8)`, and `slot(arg0+0x8f8)` rather than
  silently failing to attach canonical IDs to nested slot references. That is
  useful progress because the remaining gap is now squarely a value/provenance
  problem instead of a slot-ID bookkeeping bug.
- Direct-callee effect import now refuses to let unknown-like helper writes
  clobber a more precise caller fact, which keeps partially summarized helpers
  from erasing useful stack/register provenance. On the compact sample this
  shrank the last frontier again: `compact_vm_generic_model.unknownskip.noabi.txt`
  now carries the final stack cell as a smaller phi over concrete register
  slots like `slot(arg0+0x978)` / `slot(arg0+0x8c8)` plus remaining unknown
  arms, instead of collapsing that cell immediately to a single opaque unknown.
- Bounded slot-provenance support is now implemented for generic state facts:
  recursive slot aliases, bounded `add/sub(slot, const)` facts, bounded helper
  slot-alias import, and slot-backed `NEXT_PC` dispatch evaluation all have
  unit coverage. The virtual-model dump now also prints incoming argument facts
  and the last non-unknown specialized dispatch target for unresolved edges.
- On the real compact sample, that new slot-provenance layer is a genuine model
  improvement but it does not close the last slice yet:
  `compact_vm_generic_model.slotprov3.noabi.txt` still reports
  `reachable=15 frontier=1 closed=false`, and
  `CorpusVMP.compact.vm.block.generic-on.slotprov3.noabi.ll` still contains one
  live `call ptr @__omill_dispatch_jump` with zero `vm_entry_*` references.
  The emitted no-ABI IR is byte-identical to the earlier
  `widthfix1.noabi.ll`, which means this work strengthened generic reasoning
  and diagnostics without changing the final recovered compact CFG yet.
- Generic helper memory-read modeling now also handles helpers that take the
  memory address as a plain integer argument. `__remill_read_memory_*`
  summaries can now produce `argN` / `argN + const` stack-cell expressions,
  localized leaf-helper imports fall back to full caller remap/specialization
  when the "already localized" assumption is false, and caller summaries now
  intern stack cells that only appear as address expressions like
  `add(slot(RSP), 0x10)`. Unit coverage now proves dispatch materialization
  through a helper that reads memory via an address argument.
- On the real compact sample, that work materially tightened the last open
  edge without closing it yet. `compact_vm_generic_model.readmemfix3.noabi.txt`
  now includes a canonical caller-local `[RSP+0x10]` stack cell
  (`stack-cell 36 base=arg0 base_offset=0x908 cell_offset=0x10`), and the
  surviving `blk_180026dce` dispatch specializes to
  `sub(slot(arg0+0x8A8), 0xf5dd)` instead of a helper-relative or untracked
  memory expression. The slice is still open at
  `reachable=18 frontier=1 closed=false`, so the remaining blocker has shifted
  again: it is now upstream provenance for state slot `arg0+0x8A8`, not
  helper-address remap or stack-cell canonicalization.
- Closed root-slice continuation discovery now has a real collapse step between
  lift rounds instead of just marking newly lifted targets. The pass now:
  preserves `omill.closed_root_slice*` metadata across `MergeBlockFunctions`,
  reruns merge/inlining/boundary cleanup after each lift round, and widens the
  inline budget for single-caller closed-slice continuation helpers so deeper
  lifted/native wrappers can still collapse back into the root slice.
- That continuation-discovery path is now enabled by default for generic static
  devirtualization and can be disabled with
  `OMILL_SKIP_CLOSED_SLICE_CONTINUATION_DISCOVERY=1`. The old opt-in
  `OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY` gate is no longer needed.
- On `CorpusVMP.compact.dll` from `0x180001850`, the default ABI artifact now
  materially beats the previous `nativeinline1` / `postgate2` baseline.
  `compact_vm_generic_model.autocont2.verifyabi.txt` reports
  `reachable=15 frontier=0 closed=true`, and
  `CorpusVMP.compact.vm.block.generic-on.autocont2.verifyabi.ll` contains:
  `define_native=1`, `declare_blk=0`, `call_blk=0`, `dispatch=0`,
  `vm_entry=0`. The only remaining `_native` definition is the root
  `sub_180001850_native`.
- Remaining architectural work is now ordered as:
  1. improve post-closure continuation quality so closed slices end in lifted
     native-looking code more often and fall back to `__remill_missing_block`
     less often
  2. reduce or canonicalize synthetic fallback targets like
     `blk_ffffffffac9b1737` when the computed constant can be mapped back to a
     real lifted/native continuation

## March 12, 2026: Bounded `CALLI` Return-State Recovery

- Implemented generic callsite summaries in
  `VirtualMachineModel.{h,cpp}` with:
  `resolved_target_pc`, `continuation_pc`, executable classification, and
  bounded imported return slot/stack facts for constant in-image `CALLI`
  targets.
- Added bounded helper-call continuation inference for the common compact
  pattern:
  `CALLI helper -> lifted call target -> musttail lifted continuation`.
  This now recovers `RETURN_PC` even when the helper argument itself is still
  symbolic and lets `CALLI` targets fold through `RETURN_PC`-seeded `NEXT_PC`
  facts.
- Added focused regressions:
  - `VirtualMachineModelTest.InfersHelperCallContinuationAndReturnPcSeededTarget`
  - `VirtualCFGMaterializationTest.MaterializesDispatchFromReturnPcSeededCallSiteTarget`
- Focused verification is green:
  `VirtualMachineModelTest|VirtualCFGMaterializationTest` now pass `56/56`.

- Compact impact:
  the new `CALLI` layer is now resolving the previously opaque helper chain
  substantially deeper than `readmemfix3` / early `callret` attempts. The fresh
  model dump `compact_vm_generic_model.callret5.noabi.txt` shows:
  - `reachable=50 frontier=5 closed=false`
  - `blk_180061a0e` now resolves its `CALLI` target all the way to
    `0x180026dce`
  - upstream helper-call targets now also resolve to concrete PCs like
    `0x18006601e`, `0x180066019`, `0x18000bc00`, `0x18000bc05`, and
    `0x180033d29`
  - the remaining open call frontiers are now concrete-but-bad targets with
    `reason=call_target_not_executable`, not generic dynamic targets

- Remaining blocker after bounded `CALLI` recovery:
  the last live dispatch is still the `blk_180026dce` jump on
  `sub(slot(arg0+0x8A8), 0xf5dd)`. At this point the blocker is no longer
  helper argument remap or `CALLI` return-state import. The newly recovered
  chain now reaches a mid-block continuation at `0x180061A0E`, and the real
  binary bytes immediately before that target contain a direct native
  `call 0x180024eb2` whose return value feeds `%rax` at `0x180026dce`.
  Because block lifting currently starts at `0x180061A0E`, the generic path
  still misses that prelude-produced entry state.

- Next architectural step:
  add bounded binary-backed continuation-entry recovery for mid-block targets.
  The likely generic form is:
  1. bounded backward decode around a lifted target entry
  2. detect straight-line preludes that fall through into the lifted entry
  3. if the prelude contains a constant direct call, lift/summarize that call
     target and import its return-register facts into the lifted entry state
  4. rerun model/materialization with those seeded entry facts

## March 12, 2026: Mid-Block Prelude Call Recovery

- Implemented bounded binary-backed prelude detection in
  `VirtualMachineModel.cpp` for the simplest useful mid-block case:
  a direct `call rel32` that falls through exactly into a lifted entry VA.
- Root-slice summarization now exposes those prelude targets as ordinary
  `kind=call` frontiers when the target is not yet lifted, so the existing
  generic materialization worklist can lift them on the next iteration.
- State propagation now reuses the bounded slot/stack fact domain to seed a
  lifted entry's incoming facts from the lifted prelude target's return-state
  summary when that target exists.
- Added focused regressions:
  - `VirtualMachineModelTest.AddsPreludeDirectCallTargetAsRootSliceFrontier`
  - `VirtualMachineModelTest.SeedsMidBlockEntryFromPreludeDirectCallReturnFacts`
  - `VirtualCFGMaterializationTest.MaterializesDispatchFromPreludeDirectCallReturnFacts`
- Verification is green:
  - `cmake --build build-remill --target omill-unit-tests --config RelWithDebInfo`
  - focused `ctest` for `VirtualMachineModelTest|VirtualCFGMaterializationTest`
  - direct `gtest` execution of the three new prelude regressions

- Compact impact:
  the new prelude layer does real work on `CorpusVMP.compact.dll`, but it does
  not close the root slice yet. The fresh model dump
  `compact_vm_generic_model.prelude1.noabi.txt` shows:
  - `reachable=114 frontier=13 closed=false`
  - the previously unmodeled prelude target is now discovered and lifted:
    `diag lifted target=0x180024EB2 -> blk_180024eb2`
  - `blk_180061a0e` is no longer purely "mid-block with missing entry state";
    it now carries the binary-backed prelude edge explicitly
  - the remaining blocker moved one layer deeper:
    `blk_180024eb2` itself has an unresolved call-return chain

- Current blocker after prelude recovery:
  importing return facts from a lifted prelude target is not sufficient when
  that prelude target's own outgoing state depends on its internal `CALLI`
  return chain. In the fresh compact run:
  - `blk_180061a0e` still has an open call frontier to `0x17FFEC18E`
  - `blk_180024eb2` is now visible and lifted, but it still has an open call
    frontier to `0x18007E112`
  - `blk_180026dce` still ends in a live dispatch on
    `sub(slot(arg0+0x8A8), 0xf5dd)`

- Next architectural step:
  unify prelude localization with the existing callsite-return localization so
  a lifted prelude target can carry its own bounded `CALLI` return facts into
  the entry-state seed. In practice this means:
  1. localize callsite return facts while computing prelude-target outgoing
     facts, not just direct-callee effects
  2. only then reseed the mid-block entry
  3. rerun compact and confirm whether `slot(arg0+0x8A8)` finally folds to a
     concrete successor

## March 12, 2026: Shared Nested Callsite Localization For Prelude Targets

- Extended `VirtualMachineModel.cpp` so localized outgoing-fact computation now
  imports bounded `CALLI` return facts inside localized callees and inside
  binary-backed prelude targets, instead of only importing direct-callee
  effects.
- Added focused nested-shape regressions:
  - `VirtualMachineModelTest.SeedsMidBlockEntryFromPreludeNestedCallSiteReturnFacts`
  - `VirtualCFGMaterializationTest.MaterializesDispatchFromPreludeNestedCallSiteReturnFacts`
- Verification is still green:
  - `cmake --build build-remill --target omill-unit-tests --config RelWithDebInfo`
  - focused `ctest` for `VirtualMachineModelTest|VirtualCFGMaterializationTest`

- Compact impact:
  the new shared localizer is implemented and unit-tested, but the real compact
  sample does not change yet. The fresh dump
  `compact_vm_generic_model.prelude2.noabi.txt` remains:
  - `reachable=114 frontier=13 closed=false`
  - `blk_180061a0e` still has open call frontier `0x17FFEC18E`
  - `blk_180024eb2` still has open call frontier `0x18007E112`
  - `blk_180026dce` still ends in a dispatch on
    `sub(slot(arg0+0x8A8), 0xf5dd)`

- Refined blocker after nested prelude localization:
  this is no longer just "prelude target lacks internal callsite imports."
  The compact model now shows the deeper issue more honestly:
  the lifted prelude chain is still producing `NEXT_PC` / `RETURN_PC`-relative
  state updates, but it is not yet recovering the caller-visible register fact
  for state slot `0x8A8` that the later mid-block entry actually needs.

- Next architectural step:
  add explicit tracked return-register import for localized lifted call chains.
  In practice this means:
  1. identify caller-visible register slots written by a localized lifted call
     target even when the target's control-transfer summary remains open
  2. import those bounded slot facts into the prelude target anyway
  3. rerun compact and check whether `blk_180024eb2` finally seeds
     `slot(arg0+0x8A8)` into `blk_180061a0e` / `blk_180026dce`

## March 12, 2026: Specialized Stack Address Mapping Through Repeated `PUSHI`

- Narrowed the helper-import fix in `VirtualMachineModel.cpp` so
  argument-relative slot/stack live-ins are mapped through the caller-local
  specialized argument expression, not just the raw SSA argument.
- Extended stack-cell extraction to flatten bounded nested `add/sub(slot, const)`
  chains. This specifically covers helper address forms like:
  - `add(sub(slot(RSP), 0x8), 0x10)`
  - `add(sub(sub(slot(RSP), 0x8), 0x8), 0x10)`
- Added focused regressions:
  - `VirtualMachineModelTest.ResolvesVmStackLoadAfterRepeatedPushesThroughSpecializedAddressArgs`
  - `VirtualCFGMaterializationTest.MaterializesDispatchFromVmStackLoadAfterRepeatedPushes`
- Verification is green:
  - `cmake --build build-remill --target omill-unit-tests --config RelWithDebInfo`
  - focused `ctest` for `VirtualMachineModelTest|VirtualCFGMaterializationTest`

- Compact impact:
  the old `blk_180026dce` blocker is gone in the fresh run
  `compact_vm_generic_model.stackalias1.noabi.txt`:
  - root slice improved from `frontier=13` to `frontier=12`
  - `blk_180026dce` is no longer a frontier and now has `dispatches=0`
  - the old `%rax - 0xf5dd` target is gone
  - the emitted no-ABI IR
    `CorpusVMP.compact.vm.block.generic-on.stackalias1.noabi.ll`
    has no `__omill_dispatch_jump` refs and no `vm_entry_*` refs

- Refined blocker after repeated-`PUSHI` address recovery:
  the next live model frontier is now one layer earlier:
  - `blk_180060f01` still has `dispatches=1`
  - its specialized target is now simply `slot(arg0+0x8D8)`
  - the remaining call frontiers are still concrete-but-bad targets like
    `0x17FFEC18E` and `0x18007E112`

- Next architectural step:
  recover bounded provenance for state slot `0x8D8` and separate
  "constant in mapped image" from "decodable lifted entry" for the remaining
  call frontiers. In practice this means:
  1. trace the producer chain for `slot(arg0+0x8D8)` through the preceding
     helper sequence in `blk_180060f01`
  2. add the same caller-local specialization to any remaining helper writes
     feeding that slot
  3. classify constant call targets as decodable entry vs mid-instruction /
     non-entry target before treating them as liftable continuations

## March 12, 2026: Safe Leaf-Helper Local Replay Boundary

- I wired leaf-helper-local outgoing-fact recomputation into the localized
  call/target/prelude import paths in `VirtualMachineModel.cpp`, but kept the
  stable gate narrow: it is enabled only for single-block helpers that do not
  contain `__remill_read_memory_*` or `__remill_write_memory_*`.
- That version keeps the focused suite green again:
  - `ctest --test-dir build-remill --output-on-failure -R "VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact with the safe gate:
  the compact artifact falls back to the known-good `stackalias1` plateau:
  - `reachable=114 frontier=12 closed=false`
  - the live frontier is still `blk_180060f01`
  - `blk_180060f01` now stands out more cleanly as a register-provenance issue:
    its specialized target is still `slot(arg0+0x8D8)`
  - `__omill_dispatch_jump` is still present in
    `CorpusVMP.compact.vm.block.generic-on.leaflocal2.noabi.ll`

- Refined blocker after the safe leaf-helper replay:
  the remaining loss is not generic dispatch plumbing anymore. It is helper
  summary pollution inside a mixed read/write helper chain:
  - `POPI` still summarizes `slot[10]` as
    `phi(0x18005c2f4, add(stack(slot(arg0+0x0)+0x0), 0x571a), slot(arg0+0x8d8))`
  - `ADCI` still summarizes `%rdi`-like state with merged
    `phi(..., slot(arg0+0x8d8))`
  - `blk_180060f01` then only sees `NEXT_PC <- slot(arg0+0x8D8)` instead of the
    straight-line `POPI -> ADCI -> JMPI` result

- Next architectural step:
  implement a bounded sequential helper-chain simulator for localized
  read/write-memory helpers. The stable target is:
  1. replay short straight-line helper chains in call order
  2. update temporary slot/stack state after each helper
  3. re-resolve later helper operands against that updated local state
  4. only then materialize the final `NEXT_PC` / dispatch edge

## March 12, 2026: Sequential Local Replay For Leaf Helpers

- I replaced the old narrow leaf-helper shortcut in
  `VirtualMachineModel.cpp` with a bounded local interpreter for
  single-basic-block leaf helpers. The replay keeps temporary:
  - `slot_facts`
  - `stack_facts`
  - `value_facts`
- The local replay now handles straight-line:
  - loads and stores to tracked state / out-param slots
  - bounded integer arithmetic and casts
  - bounded `phi` / `select`
  - `__remill_read_memory_*`
  - `__remill_write_memory_*`
- Unsupported instruction shapes still bail out safely to the existing
  summary-based import instead of widening unsafely.

- Added focused regressions:
  - `VirtualMachineModelTest.ReplaysSequentialLeafHelperVmMemoryEffectsLocally`
  - `VirtualMachineModelTest.FallsBackFromUnsupportedLeafHelperReplayToSummaryImport`
  - `VirtualCFGMaterializationTest.MaterializesDispatchFromSequentialLeafHelperVmMemoryReplay`
  - `VirtualCFGMaterializationTest.FallsBackFromUnsupportedLeafHelperReplayDuringMaterialization`

- Verification stayed green:
  - `cmake --build build-remill --target omill-unit-tests --config RelWithDebInfo`
  - `ctest --test-dir build-remill --output-on-failure -R "VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact:
  the live `blk_180060f01` dispatch frontier stopped collapsing to a bare
  `slot(arg0+0x8D8)` register alias and instead tightened to a concrete
  return-PC-based form:
  - specialized target improved to `add(0x18005ca5c, slot(arg0+0x811))`
  - the only remaining dynamic part was a carry/flag-like bit in
    `slot(arg0+0x811)`

- Refined blocker after sequential local replay:
  the remaining loss was no longer helper summary pollution in the replayed
  `POPI -> ADCI -> JMPI` chain. It was bounded control-transfer choice over a
  boolean flag slot that the generic target collector was still treating as an
  open symbolic addend.

## March 12, 2026: Boolean Flag Slot Choice Materialization

- I extended dispatch-target choice collection in `VirtualMachineModel.cpp`
  so bounded flag-like state slots can contribute finite `{0,1}` choices
  during successor collection instead of leaving the target open.
- The implementation canonicalizes the specialized dispatch target before
  successor collection, recognizes flag slots both by canonical slot ID and by
  structural slot-expression shape, and then enumerates the bounded boolean
  alternatives during target evaluation.

- Added focused regressions:
  - `VirtualMachineModelTest.ResolvesBooleanFlagSlotDispatchToFiniteSuccessors`
  - `VirtualCFGMaterializationTest.MaterializesDispatchFromBooleanFlagSlotChoices`
- The synthetic flag-state tests use a minimal `struct.X86State` /
  `struct.GPR` shape so `StateFieldMap` classifies offset `0x811` as an x86
  flag slot exactly like the real lifted state.

- Verification is green:
  - direct `gtest` runs for the new flag-slot cases
  - `ctest --test-dir build-remill --output-on-failure -R "VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact in
  `compact_vm_generic_model.flagchoice1.noabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.flagchoice1.noabi.ll`:
  - the old `blk_180060f01` dynamic dispatch frontier is gone
  - `blk_180060f01` still has `dispatches=1`, but it now resolves to two
    concrete lifted successors:
    - `0x18005CA5C -> blk_18005ca5c`
    - `0x18005CA5D -> blk_18005ca5d`
  - the fresh root slice is now:
    `reachable=133 frontier=15 closed=false`
  - the emitted no-ABI IR has no `__omill_dispatch_*` refs and no
    `vm_entry_*` refs

- Refined blocker after bounded flag-choice materialization:
  the remaining open work is now deeper continuation/call-target recovery, not
  the old `blk_180060f01` carry-shaped dispatch. The new exposed frontiers are
  concrete call roots like:
  - `blk_18005ca5c kind=call reason=call_target_unlifted target=0x1800675FC`
  - `blk_18003b404 kind=call reason=call_target_unlifted target=0x1800675DA`
  - several concrete-but-bad `call_target_not_executable` targets

- Next architectural step:
  keep the focus on call / continuation recovery rather than more dispatch
  algebra:
  1. classify constant call targets as decodable entry vs non-entry /
     undecodable target
  2. lift or reject those new continuation roots accordingly
  3. only then revisit any remaining frontier set once the deeper concrete
     call edges are resolved

## March 12, 2026: Decodable Entry Classification For Call Frontiers

- I added a cheap decodable-entry classifier for constant call targets in the
  generic VM model:
  - x86-64 uses the in-tree handwritten decoder from `VMTraceEmulator.cpp`
    via `canDecodeX86InstructionAt`
  - AArch64 uses a bounded alignment + 4-byte-readability check
- `VirtualCallSiteSummary` now records both:
  - `is_executable_in_image`
  - `is_decodable_entry`
- The virtual-model dump now prints `decodable_entry=...` for each callsite,
  and the root-slice frontier reasons now distinguish:
  - `call_target_not_executable`
  - `call_target_undecodable`
  - `call_target_unlifted`

- I also tightened the materialization worklist:
  it now only tries to lift call frontiers whose reason is
  `call_target_unlifted`. It no longer keeps re-attempting known-bad
  `call_target_not_executable` / `call_target_undecodable` PCs.

- Added focused regressions:
  - `VirtualMachineModelTest.MarksInImageUndecodableCallSiteTargetAsCallFrontier`
  - `VirtualMachineModelTest.MarksUndecodablePreludeDirectCallTargetAsRootSliceFrontier`
- Existing callsite / prelude return-fact regressions stayed green.

- Verification is green:
  - `cmake --build build-remill --target omill-unit-tests --config RelWithDebInfo`
  - `ctest --test-dir build-remill --output-on-failure -R "VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact in
  `compact_vm_generic_model.callclass1.noabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.callclass1.noabi.ll`:
  - the no-ABI IR still has no `__omill_dispatch_*` refs and no `vm_entry_*`
    refs
  - the remaining frontier set is now explicitly split by target quality:
    - undecodable in-image examples:
      - `blk_180066019 -> 0x18000BC05`
      - `blk_18005ca5c -> 0x1800675FC`
      - `blk_18004fb26 -> 0x1800057C4`
    - not-executable examples:
      - `blk_180055365 -> 0x1800754F1`
      - `blk_180061a0e -> 0x17FFEC18E`
  - the fresh root slice is:
    `reachable=120 frontier=18 closed=false`

- Refined blocker after decodable-entry classification:
  the remaining work is now clearly continuation-entry recovery, not dispatch
  recovery:
  1. for `call_target_unlifted`, lift and continue as before
  2. for `call_target_undecodable`, decide whether there is a recoverable
     nearby real entry (mid-block / prelude recovery) or whether the target
     should stay terminal
  3. for `call_target_not_executable`, treat the path as terminal unless
     upstream value recovery proves the PC itself is wrong

## March 12, 2026: Executable Region Tracking And Decoder Coverage Cleanup

- I fixed two concrete quality bugs in the constant-call frontier classifier:
  - `BinaryMemoryMap` regions now carry an `executable` bit, so the generic
    model distinguishes:
    - mapped-but-non-executable targets
    - real executable-region targets
  - the lightweight x86 entry probe in `VMTraceEmulator.cpp` now handles more
    first-instruction shapes that showed up in `CorpusVMP.compact.dll`,
    including:
    - `BTC r/m, r` (`0F BB`)
    - `PUSH imm32` / `PUSH imm8` (`68` / `6A`)
    - rotate-group entries like `ROL` / `ROR`
    - mixed legacy/REX prefix sequences such as `rex + rep + jcc`

- Updated focused coverage:
  - `BinaryMemoryMapTest.ExecutableRegionClassification`
  - `VirtualMachineModelTest.MarksMappedNonExecutableCallSiteTargetAsCallFrontier`
  - `VirtualMachineModelTest.MarksDecodableBtcCallSiteTargetAsUnliftedFrontier`
  - `VirtualMachineModelTest.MarksDecodableRolCallSiteTargetAsUnliftedFrontier`

- Verification is green:
  - `cmake --build build-remill --target omill-unit-tests --config RelWithDebInfo`
  - `ctest --test-dir build-remill --output-on-failure -R "BinaryMemoryMapTest|VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact in
  `compact_vm_generic_model.callclass3.noabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.callclass3.noabi.ll`:
  - the no-ABI IR still has no `__omill_dispatch_*` refs and no `vm_entry_*`
    refs
  - false `call_target_undecodable` frontiers are reduced further:
    - `0x18006601E` now lifts and becomes `blk_18006601e`
    - `0x180062EDC` now lifts and becomes `blk_180062edc`
  - several earlier "undecodable" targets are now correctly classified as
    `call_target_not_executable` instead
  - the fresh root slice is now:
    `reachable=131 frontier=17 closed=false`

- Refined blocker after executable/decoder cleanup:
  the remaining open work is now mostly true target-anchor recovery:
  - still-open undecodable roots are concentrated at:
    - `blk_180066019 -> 0x18000BC05`
    - `blk_1800319ef -> 0x18001EB75`
    - `blk_18006601e -> 0x18000BC00`
  - the next architectural step should be bounded nearby-entry / mid-block
    continuation recovery for those genuinely misaligned PCs, not more generic
    dispatch or helper-summary work

## March 12, 2026: Nearby Entry Recovery Now Prefers Lifted Continuations

- I wired the new nearby-entry fields all the way through the generic path:
  - `VirtualCallSiteSummary` now keeps `recovered_entry_pc` and
    `recovered_target_function_name`
  - the virtual-model dump prints both fields for callsites
  - `VirtualCFGMaterialization` now treats
    `call_target_nearby_unlifted` as liftable via `canonical_target_va`

- I also tightened nearby-entry selection in `VirtualMachineModel.cpp`:
  - when an exact constant call target is executable but undecodable, we now
    prefer a previously lifted earlier entry within the bounded search window
    over a merely decodable byte closer to the target
  - if such a lifted nearby entry exists, callsite localization now uses that
    recovered target summary to import bounded return slot/stack facts instead
    of bailing out immediately on the exact mid-instruction PC

- Updated focused coverage:
  - `VirtualMachineModelTest.RecoversNearbyCallSiteEntryAsCanonicalUnliftedFrontier`
  - `VirtualMachineModelTest.RecoversNearbyCallSiteEntryAsReachableMidInstructionTarget`
  - the existing undecodable callsite/prelude tests were tightened so they
    still cover truly undecodable targets with no nearby recoverable entry

- Verification is green:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - `ctest --test-dir build-remill --output-on-failure -R "BinaryMemoryMapTest|VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact in
  `compact_vm_generic_model.callnear2.noabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.callnear2.noabi.ll`:
  - the no-ABI IR still has no `__omill_dispatch_*` refs and no `vm_entry_*`
    refs
  - `blk_180066019 -> 0x18000BC05` is no longer treated as
    `call_target_nearby_unlifted` with canonical `0x18000BC04`
  - it is now a `call_target_mid_instruction` frontier with:
    - `recovered_entry=0x18000BC00`
    - `recovered_target_fn=blk_18000bc00`
    - imported bounded return facts from that recovered lifted target
  - `blk_1800319ef -> 0x18001EB75` likewise now carries:
    - `recovered_entry=0x18001EB74`
    - `recovered_target_fn=blk_18001eb74`
    - imported return facts instead of a bare unresolved target
  - the fresh root slice is now:
    `reachable=137 frontier=17 closed=false`

- Refined blocker after lifted-nearby-entry recovery:
  the remaining work is no longer “find some nearby byte that decodes.” It is:
  1. mid-instruction continuation-entry recovery for callsites that already
     have a recovered lifted target (`call_target_mid_instruction`)
  2. better classification / terminal handling for concrete
     `call_target_not_executable` paths
  3. eventually, callsite materialization/cleanup so the surviving `CALLI`
     helper scaffolding disappears once those frontiers are resolved

## March 12, 2026: Closed-Slice Call Localization And Late-Continuation Stabilization

- I finished the remaining compact root-slice closure gap in the model:
  - root-slice closure now treats a `CALLI` as semantically localized not only
    when there is a separate lifted continuation callee, but also when the
    current handler already summarizes same-handler post-call state through
    `RETURN_PC` / continuation-PC anchored outgoing facts
  - this covers the last compact frontier shape where the unresolved callee
    target was terminal/non-executable but the handler’s own outgoing state was
    already sufficient for the closed slice

- Updated focused coverage:
  - `VirtualMachineModelTest.IgnoresSameHandlerLocalizedNonExecutableCallSiteForRootSliceClosure`

- I also fixed a late pipeline stability bug that only became visible once the
  compact slice actually closed:
  - `BlockLifter` now resolves block declarations/definitions from the live
    module symbol table instead of reusing stale block-manager cache entries
    after closed-slice merge/DCE rounds
  - `LateClosedRootSliceContinuationClosurePass` now skips discovery when the
    declared continuation frontier is too large to plausibly collapse in one
    cleanup epoch, instead of expanding the IR into crashing / dispatch-heavy
    continuation recovery

- Verification is green:
  - `cmake --build build-remill --target omill-lift omill-unit-tests --config RelWithDebInfo`
  - `ctest --test-dir build-remill --output-on-failure -R "VirtualMachineModelTest|VirtualCFGMaterializationTest" -C RelWithDebInfo`

- Compact impact in
  `compact_vm_generic_model.calllocalsame5.noabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.calllocalsame5.noabi.ll`:
  - the root slice now reports:
    `reachable=137 frontier=0 closed=true`
  - the no-ABI IR writes cleanly again
  - there are `0` `__omill_dispatch_call` refs
  - there are `0` `__omill_dispatch_jump` refs
  - there are `0` `vm_entry_*` refs
  - the late continuation cleanup is now conservative:
    it leaves `7` declared `blk_*` continuation stubs with `7` direct call
    sites in the no-ABI output instead of expanding into crashing /
    dispatch-heavy continuation recovery

- Refined blocker after closure:
  the remaining work is no longer semantic closure of the compact root. It is
  output quality:
  1. collapse or eliminate the remaining declared `blk_*` continuation stubs
     without reintroducing dispatch helpers
  2. improve no-ABI readability so the closed slice looks less like lifted
     block scaffolding
  3. rerun the same closure path in ABI mode and keep the late continuation
     stage on a similarly bounded, non-regressing footing

## March 12, 2026: Stable ABI Validation On The Closed Compact Slice

- I validated the same stable closed-slice path in ABI mode with:
  - `omill-lift CorpusVMP.compact.dll --va=180001850 --block-lift`
    `--generic-static-devirtualize --verify-each`

- Verification is green:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - direct focused gtest sweep:
    `PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`
  - `llvm-as` accepts
    `CorpusVMP.compact.vm.block.generic-on.calllocalsame6.verifyabi.ll`

- Compact ABI impact in
  `compact_vm_generic_model.calllocalsame6.verifyabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.calllocalsame6.verifyabi.ll`:
  - the root slice still reports:
    `reachable=137 frontier=0 closed=true`
  - there are `0` `__omill_dispatch_call` refs
  - there are `0` `__omill_dispatch_jump` refs
  - there are `0` `vm_entry_*` refs
  - there are `0` declared `blk_*` continuation stubs
  - there are `0` live `blk_*` calls / `musttail` continuation edges
  - the ABI output collapses to a single
    `sub_180001850_native` definition with no `_native` call edges
  - the terminal fallback is explicit via `__omill_missing_block_handler`
    rather than synthetic lifted continuation stubs

- Follow-up note:
  I prototyped a second post-cleanup continuation-discovery round in the
  generic pipeline, but it reintroduced dispatch-heavy lifted continuations or
  ran far too long on the compact sample. That experiment is intentionally not
  enabled in the stable default path.

- Refined blocker after ABI validation:
  the remaining work is now primarily no-ABI output quality and more principled
  continuation recovery:
  1. collapse the residual no-ABI `blk_*` continuation chain without reopening
     dispatches
  2. keep any future continuation rediscovery bounded and root-scoped
  3. broaden validation to more roots/samples now that both compact no-ABI
     closure and ABI recovery are stable

## March 13, 2026: ABI Cleanup Bisect Shows Readability Collapse Is Stable

- I added a small IR-shape measurement helper at:
  `tools/measure_ir_shape.py`
  so we can compare final `.ll` artifacts without re-reading the full module.
  It reports:
  - `dispatch_call`
  - `dispatch_jump`
  - `vm_entry`
  - `declare_blk`
  - `call_blk`
  - `musttail_blk`
  - `define_native`
  - `call_native`
  - `missing_block`
  - `missing_block_handler`

- Baseline compact metrics:
  - `before_abi.ll`:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0 declare_blk=7 call_blk=7`
    `musttail_blk=0`
  - `CorpusVMP.compact.vm.block.generic-on.calllocalsame5.noabi.ll`:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0 declare_blk=7 call_blk=7`
    `musttail_blk=0`
  - `CorpusVMP.compact.vm.block.generic-on.calllocalsame6.verifyabi.ll`:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0 declare_blk=0 call_blk=0`
    `musttail_blk=0 define_native=1 call_native=0`

- I ran a strict compact ABI bisect from the same root
  (`0x180001850`) using the existing skip knobs one at a time and recorded the
  outputs under:
  `build-remill/test_obf/corpus/lifted/abi_bisect_summary.json`

- ABI bisect result:
  - baseline:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `153.744s`
  - `OMILL_SKIP_ABI_RECOVER_SIGNATURES`:
    `declare_blk=0 call_blk=0 define_native=0`
    runtime `151.815s`
  - `OMILL_SKIP_ABI_ALWAYS_INLINE`:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `156.525s`
  - `OMILL_SKIP_ABI_REWRITE_LIFTED_LATE`:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `152.245s`
  - `OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE`:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `154.206s`
  - `OMILL_SKIP_ABI_GLOBAL_DCE`:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `151.556s`
  - `OMILL_SKIP_ABI_FINAL_OPT`:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `154.594s`
  - `OMILL_SKIP_ABI_INLINE_VM_HANDLERS`:
    `declare_blk=0 call_blk=0 define_native=1`
    runtime `162.498s`

- Conclusion from the bisect:
  - there is no single skip knob in the current ABI sequence that explains the
    disappearance of the residual compact `blk_*` continuation chain
  - the collapse is robust across all tested ABI variants
  - `RecoverFunctionSignatures` changes wrapper shape, but it is not required
    for `declare_blk/call_blk` to drop to zero

- Chosen direction after the bisect:
  - treat ABI output as the current readability artifact for this root
  - keep no-ABI output as the faithful lifted/debug artifact
  - do not spend the next cycle on more generic continuation discovery for this
    already-closed root unless a later validation run proves ABI cleanup is not
    the reason the chain disappears

- I also added focused coverage:
  - `PipelineTest.AbiPipelineRemovesClosedSliceNativeBlockChainAndPreservesRootAttrs`
    checks that the stable ABI pipeline removes a synthetic closed-slice
    `blk_*_native` continuation chain while preserving
    `omill.closed_root_slice` / `omill.closed_root_slice_root` metadata on the
    surviving root

## March 13, 2026: `RETURN_PC`-Anchored Callsite Fix And Terminal Missing-Block Diagnostics

- I added a narrow generic fix in `VirtualMachineModel.cpp` for `CALLI`
  targets of the form `add/sub(slot(NEXT_PC), const)` when the same handler
  later materializes `NEXT_PC = add/sub(slot(RETURN_PC), const)`. In that case
  callsite resolution now re-seeds `RETURN_PC` from the concrete continuation
  PC and resolves the target from the outgoing `NEXT_PC` fact instead of
  keeping a non-executable pre-call constant.

- Focused coverage added:
  - `VirtualMachineModelTest.PrefersOutgoingNextPcAnchoredToReturnPcForCallSiteTarget`
  - `VirtualCFGMaterializationTest.MaterializesTerminalMissingBlockFromNextPcFacts`

- Verification:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - focused direct gtests for the new model/materialization cases
  - `VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`

- Compact impact from
  `compact_vm_generic_model.returnpcfix3.noabi.txt` and
  `CorpusVMP.compact.vm.block.generic-on.returnpcfix3.noabi.ll`:
  - the callsite-anchor fix is real:
    - `blk_180055365` now resolves
      `callsite target=add(slot(NEXT_PC+0x0), 0x100c1)` to
      `target_fn=blk_18006542b`
    - the root slice remains
      `reachable=154 frontier=0 closed=true`
    - there are still `0` `__omill_dispatch_*` refs and `0` `vm_entry_*` refs
  - but the no-ABI artifact still contains one live terminal
    `__remill_missing_block` call

- The new terminal-edge diagnostics make the remaining gap precise:
  - `blk_180064933` already computes a good terminal `NEXT_PC`
    (`0x180061A0E`)
  - `blk_180026dce` still computes a bad terminal `NEXT_PC`
    (`0xFFFFFFFF8A9DE25C`) in every bounded fact state
  - so the remaining issue is no longer `CALLI` target recovery and no longer
    basic missing-block lowering
  - the remaining issue is handler-local helper-chain replay for the
    `PUSHI/MOVI/LEAI/JMPI` sequence inside `blk_180026dce`

- Refined next step:
  - extend bounded sequential local replay to whole handler-local helper chains
    feeding terminal `JMPI -> __remill_missing_block`, instead of relying on
    handler-summary outgoing facts for those memory-touching helper sequences

## March 13, 2026: Localized Stack-Cell Remap Fix Restores Replay Tests, Compact Still Has A Residual `blk_*` Chain

- I fixed a localized helper-import bug in `VirtualMachineModel.cpp`: when a
  helper was replayed per callsite, stack-cell writes were still being keyed by
  the callee-local cell id instead of being remapped through the actual caller
  address argument. That broke the repeated-`PUSHI` / specialized-address
  cases by leaving stack effects anchored to helper-relative bases.

- Concretely, the localized stack import path now remaps stack-cell keys through
  the existing caller address/slot mapping logic instead of short-circuiting to
  the callee id. This restores caller-local cells like
  `(arg0+0x908, 0)` / `(arg0+0x908, 16)` for replayed helpers.

- Focused verification:
  - rebuilt `omill-unit-tests` / `omill-lift`
  - `VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`
  - current result: `85/85` passing in the focused suite

- Compact rerun from `0x180001850`:
  - no-ABI:
    `compact_vm_generic_model.localreplayfix1.noabi.txt`
    `CorpusVMP.compact.vm.block.generic-on.localreplayfix1.noabi.ll`
  - ABI + verify-each:
    `compact_vm_generic_model.localreplayfix1.verifyabi.txt`
    `CorpusVMP.compact.vm.block.generic-on.localreplayfix1.verifyabi.ll`

- Current compact state after the fix:
  - both runs still report
    `root-slice root=0x180001850 reachable=170 frontier=0 closed=true`
  - both runs still have
    `0` `__omill_dispatch_*`
  - both runs still have
    `0` `vm_entry_*`
  - neither run has a direct terminal
    `__remill_missing_block(...)` or `__omill_missing_block_handler(...)`
    call anymore
  - however, both runs still retain a residual direct `blk_*` continuation
    chain:
    - no-ABI:
      `declare_blk=8`, `call_blk=9`, `musttail_blk=1`
    - ABI:
      `declare_blk=8`, `call_blk=8`, `define_native=1`, `call_native=0`

- Important interpretation:
  - the old terminal missing-block complaint is no longer the live issue in the
    current compact artifact
  - the current issue is output-shape cleanup again: we now have a semantically
    closed slice with concrete continuation calls, but the current pipeline does
    not yet collapse that final `blk_*` chain the way the earlier
    `calllocalsame6.verifyabi` snapshot did

- Refined next step:
  - treat this as a continuation-collapse / readability regression, not a
    devirtualization regression
  - compare the current `localreplayfix1.verifyabi` pipeline shape against the
    earlier `calllocalsame6.verifyabi` shape and isolate which post-closure
    cleanup is no longer collapsing the final `blk_*` chain

## March 13, 2026: ABI Late Continuation-Call Collapse For Null-Memory `blk_*` Stubs

- Implemented a dedicated late ABI cleanup in `Pipeline.cpp`:
  `CollapseNullMemoryBlockContinuationCallsPass`.
  It runs in closed-slice scope and rewrites declaration-only synthetic
  continuation calls of the exact form:
  `call @blk_<pc>(state, <same pc>, null)`
  by replacing the call result with the null memory argument and erasing the
  now-dead call/declaration.

- Placement:
  - kept one early ABI invocation (after VM-handler inlining)
  - added a second late invocation after `ResolveIntToPtrCallsPass`, which is
    where the compact residuals finally stabilize to the null-memory shape

- Added focused coverage:
  - `PipelineTest.AbiPipelineCollapsesNullMemoryBlockContinuationCalls`
  - existing continuation-shim tests remain green in
    `VirtualCFGMaterializationTest`

- Verification:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.AbiPipelineCollapsesNullMemoryBlockContinuationCalls`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`

- Compact rerun (fresh linked binary):
  - model:
    `compact_vm_generic_model.contshim11.verifyabi.txt`
  - IR:
    `CorpusVMP.compact.vm.block.generic-on.contshim11.verifyabi.ll`
  - status:
    - root slice unchanged and still closed:
      `reachable=170 frontier=0 closed=true`
    - still `0` `__omill_dispatch_call`
    - still `0` `__omill_dispatch_jump`
    - still `0` `vm_entry_*`
    - now `0` declaration-only `blk_*` continuations
    - now `0` direct/musttail `blk_*` continuation calls
    - still `0` `__omill_missing_block_handler`

## March 13, 2026: No-ABI Closed-Slice Continuation Fallback Cleanup

- Implemented a reusable continuation cleanup pass in `Pipeline.cpp`:
  `CollapseSyntheticBlockContinuationCallsPass`.
  Behavior:
  - keeps existing null-memory declaration-call collapse
  - adds optional rewrite of unresolved declaration-only synthetic
    continuation calls to `__remill_missing_block`
  - erases dead synthetic `blk_*`/`block_*` declarations after rewrites

- Scoped the rewrite to no-ABI runs only:
  - in Phase 3.9 closed-slice cleanup the rewrite is enabled only when module
    flag `omill.no_abi_mode` is present
  - `omill-lift` now sets `omill.no_abi_mode=1` when invoked with `--no-abi`
  - ABI pipeline keeps using the same pass in null-memory-collapse mode
    (no missing-block rewrite), preserving ABI output shape

- Verification:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.AbiPipelineCollapsesNullMemoryBlockContinuationCalls`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`

- Compact reruns (`CorpusVMP.compact.dll`, root `0x180001850`):
  - no-ABI (`omill_current.noabi`):
    - `root-slice ... reachable=170 frontier=0 closed=true`
    - `dispatch_call=0`, `dispatch_jump=0`, `vm_entry=0`
    - continuation scaffolding reduced:
      `declare_blk: 2 -> 0`, `call_blk: 3 -> 1`, `musttail_blk: 1 -> 0`
    - explicit fallback now visible as `missing_block=3`
    - `missing_block_handler=0`
  - ABI verify (`omill_current.verifyabi`):
    - `root-slice ... reachable=170 frontier=0 closed=true`
    - `dispatch_call=0`, `dispatch_jump=0`, `vm_entry=0`
    - `declare_blk=0`, `call_blk=0`, `musttail_blk=0`
    - `missing_block=0`, `missing_block_handler=0`

## March 13, 2026: No-ABI Final `blk_*` Call Collapse

- Implemented an additional no-ABI closed-slice cleanup refinement in
  `Pipeline.cpp`:
  - `RelaxClosedSliceMustTailMissingBlockPass`:
    downgrades `musttail` calls to `__remill_missing_block` in closed-slice
    `blk_*` helpers during no-ABI cleanup so they can be inlined
  - widened no-ABI one/two-use inline budgets for closed-slice non-native
    helpers in `maybeMarkClosedRootSliceHelperForInlining`

- Added focused regression coverage:
  - `PipelineTest.ClosedSliceNoAbiCleanupCollapsesSingleUseBlkMustTailFallback`
    validates that a single-use closed-slice `blk_*` helper ending in
    `musttail __remill_missing_block` gets collapsed (helper call removed)

- Verification:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.ClosedSliceNoAbiCleanupCollapsesSingleUseBlkMustTailFallback:PipelineTest.AbiPipelineCollapsesNullMemoryBlockContinuationCalls`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`

- Compact rerun impact (`omill_current.noabi`):
  - root slice unchanged and still closed:
    `reachable=170 frontier=0 closed=true`
  - still `0` dispatch helpers
  - still `0` `vm_entry_*`
  - no-ABI continuation calls now fully collapsed:
    - `declare_blk=0`
    - `call_blk=0` (down from `1`)
    - `musttail_blk=0`
  - explicit terminal fallbacks remain as expected in no-ABI readability mode:
    `missing_block=3`, `missing_block_handler=0`

- ABI verification remains clean (`omill_current.verifyabi`):
  - `dispatch_call=0`, `dispatch_jump=0`, `vm_entry=0`
  - `declare_blk=0`, `call_blk=0`, `musttail_blk=0`
  - `missing_block=0`, `missing_block_handler=0`

## March 13, 2026: Default Corpus Bring-Up (Full VM)

- Semantics verification against unprotected baseline is clean for both
  protected corpora:
  - `CorpusVMP.compact.dll` matches `Corpus.dll`
  - `CorpusVMP.default.dll` matches `Corpus.dll`
  - validated via `TvmpGetAbiVersion`, `TvmpRunDigestScenario`,
    `TvmpGroundTruthDigest`

- Implemented targeted generic/materialization plumbing for default-corpus
  continuation chains:
  - `VirtualCFGMaterialization.cpp` now computes an expanded rewrite scope from
    closed-slice handlers through direct IR call-graph reachability
  - added opportunistic lifting of constant executable
    `__omill_dispatch_call/__omill_dispatch_jump` targets inside that scope
    (iterative, bounded by existing lift-failure cache)

- Implemented no-ABI cleanup safety gate in `Pipeline.cpp`:
  - `CollapseSyntheticBlockContinuationCallsPass` now rewrites unresolved
    synthetic `blk_*` continuation declarations to `__remill_missing_block`
    only when live dispatch helpers are already gone
  - when unresolved dispatch helpers remain, continuation declarations/calls are
    preserved instead of being collapsed into many missing-block fallbacks

- Added regression coverage:
  - `PipelineTest.ClosedSliceNoAbiCleanupKeepsBlkMustTailFallbackWhenDispatchLives`

- Verification:
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`
  - targeted test:
    `PipelineTest.ClosedSliceNoAbiCleanupKeepsBlkMustTailFallbackWhenDispatchLives`

- Default corpus impact (`CorpusVMP.default.dll`, root `0x180001850`,
  `--block-lift --no-abi --generic-static-devirtualize`):
  - root slice still reports closed:
    `reachable=16 frontier=0 closed=true`
  - unresolved call-dispatch count is unchanged so far:
    `dispatch_call=26`, `dispatch_jump=3`, `vm_entry=0`
  - no-ABI continuation shape is materially improved:
    - before gate (`omill_current.noabi`):
      `declare_blk=0`, `call_blk=7`, `musttail_blk=4`, `missing_block=16`
    - after gate (`omill_dispatchlift3.noabi`):
      `declare_blk=6`, `call_blk=22`, `musttail_blk=13`, `missing_block=1`

- Default ABI artifact remains clean (`omill_dispatchlift3.verifyabi`):
  - `dispatch_call=0`, `dispatch_jump=0`, `vm_entry=0`
  - `declare_blk=0`, `call_blk=0`, `musttail_blk=0`
  - `missing_block=0`, `missing_block_handler=0`

## March 13, 2026: Default No-ABI Post-Continuation Rematerialization

- Added a second generic materialization round after closed-slice continuation
  discovery, but scoped to no-ABI mode only:
  - `PipelineOptions` now carries explicit `no_abi_mode`
  - `omill-lift` sets `opts.no_abi_mode = NoABI`
  - Phase `3.86` (`post-continuation materialization`) runs only when
    `opts.no_abi_mode` is true

- Hardened repeated materialization metadata updates:
  - `VirtualCFGMaterialization` now uses
    `Module::setModuleFlag(Override, "omill.closed_root_slice_scope", ...)`
    so re-running the pass does not duplicate module-flag entries

- Default corpus impact (`CorpusVMP.default.dll`, root `0x180001850`,
  `--block-lift --no-abi --generic-static-devirtualize`):
  - artifact:
    `CorpusVMP.default.vm.block.generic-on.omill_dispatchlift5.noabi.ll`
  - root slice now expands and stays closed:
    `reachable=254 frontier=0 closed=true`
  - dispatch artifacts drop substantially:
    - before (`omill_dispatchlift3.noabi`):
      `dispatch_call=26`, `dispatch_jump=3`
    - after (`omill_dispatchlift5.noabi`):
      `dispatch_call=5`, `dispatch_jump=0`
  - continuation targets lifted in this round include previously unresolved
    call constants (`0x18015529a`, `0x1801a0cd4`, `0x1801c5ca7`,
    `0x1801d1222`, `0x180207d63`, `0x180209ad4`, `0x180234f76`,
    `0x180284ba9`, `0x18030b76a`, `0x1803679e8`, plus deeper follow-ons)
  - emitted no-ABI IR now compiles with `clang -O2 -c` (no verifier crash)

- ABI/default path remains stable and unchanged in shape:
  - artifact:
    `CorpusVMP.default.vm.block.generic-on.omill_dispatchlift7.verifyabi.ll`
  - `dispatch_call=0`, `dispatch_jump=0`, `vm_entry=0`
  - `declare_blk=0`, `call_blk=0`, `musttail_blk=0`
  - `missing_block=0`, `missing_block_handler=0`

- Verification:
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*` (`118/118` pass)

## March 13, 2026: Adjacent Wrapper Rewrite Scope For Default No-ABI

- Extended generic rewrite scope expansion in
  `VirtualCFGMaterialization.cpp`:
  - `collectReachableHandlerNames` now grows from root-slice handlers to
    adjacent modeled handlers that feed the slice via:
    - lifted direct-callee edges
    - resolved dispatch successors
    - resolved/recovered callsite target functions
  - this captures `sub_*` wrappers that are outside forward handler reachability
    but still carry rewriteable dispatch intrinsics into slice-local targets

- Added regression coverage:
  - `VirtualCFGMaterializationTest.MaterializesDispatchInAdjacentWrapperOutsideForwardReachabilityScope`

- Verification:
  - `cmake --build build-remill --target omill-unit-tests omill-lift --config RelWithDebInfo`
  - `omill-unit-tests.exe --gtest_filter=VirtualCFGMaterializationTest.MaterializesDispatchInAdjacentWrapperOutsideForwardReachabilityScope`
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*` (`119/119` pass)

- Default corpus rerun (`CorpusVMP.default.dll`, root `0x180001850`,
  `--block-lift --no-abi --generic-static-devirtualize`):
  - artifacts:
    - `CorpusVMP.default.vm.block.generic-on.omill_dispatchlift8.noabi.ll`
    - `default_vm_generic_model.omill_dispatchlift8.noabi.txt`
  - root slice remains closed:
    `reachable=254 frontier=0 closed=true`
  - dispatch helpers are now fully removed from the emitted no-ABI IR:
    - `dispatch_call=0` (down from `5`)
    - `dispatch_jump=0`
    - `vm_entry=0`
  - continuation/fallback shape after this collapse:
    - `declare_blk=2`, `call_blk=26`, `musttail_blk=6`
    - `missing_block=28`
  - emitted no-ABI IR compiles:
    `clang -O2 -c ...omill_dispatchlift8.noabi.ll`

- ABI stability check:
  - artifacts:
    - `CorpusVMP.default.vm.block.generic-on.omill_dispatchlift8.verifyabi.ll`
    - `default_vm_generic_model.omill_dispatchlift8.verifyabi.txt`
  - ABI shape stays clean:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0`
    `declare_blk=0 call_blk=0 musttail_blk=0 missing_block=0`

## March 13, 2026: Constant Continuation Target Lift Attempt (Default)

- Added a bounded opportunistic lift step in
  `VirtualCFGMaterialization.cpp`:
  - `liftConstantContinuationTargetsInReachableFunctions`
  - scans reachable functions for declaration-only `blk_*`/`block_*`
    continuation calls where the call PC argument is constant and matches the
    synthetic callee PC
  - attempts iterative lift of that target before no-ABI continuation fallback
    rewrite runs

- Verification:
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*` (`119/119` pass)

- Default corpus rerun (`omill_dispatchlift9.noabi`):
  - root slice unchanged and still closed:
    `reachable=254 frontier=0 closed=true`
  - no dispatch helpers:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0`
  - no-ABI continuation/fallback shape unchanged vs `dispatchlift8`:
    `declare_blk=2 call_blk=26 musttail_blk=6 missing_block=28`
  - emitted IR still compiles:
    `clang -O2 -c ...omill_dispatchlift9.noabi.ll`

- ABI stability rerun (`omill_dispatchlift9.verifyabi`) remains clean:
  - `dispatch_call=0 dispatch_jump=0 vm_entry=0`
  - `declare_blk=0 call_blk=0 musttail_blk=0 missing_block=0`

## March 13, 2026: Default Validation Refresh (Stable `dispatchlift11`)

- Re-ran default corpus after the adjacent-wrapper scope change and kept the
  cleanup-stage continuation-lift experiment disabled in the stable path
  (that experiment briefly reduced missing-block fallbacks but reintroduced
  live dispatch helpers in no-ABI output).

- Stable no-ABI artifact:
  - `CorpusVMP.default.vm.block.generic-on.omill_dispatchlift11.noabi.ll`
  - `default_vm_generic_model.omill_dispatchlift11.noabi.txt`
  - metrics:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0`
    `declare_blk=2 call_blk=26 musttail_blk=6 missing_block=28`
  - root slice remains closed:
    `reachable=254 frontier=0 closed=true`
  - `clang -O2 -c` succeeds on emitted `.ll`

## March 13, 2026: Default Root Closure Recovery (`decllift7`)

- Root-slice closure for `CorpusVMP.default.dll` (`--va 0x180001850`,
  `--block-lift --no-abi --generic-static-devirtualize`) is restored after
  bounded traversal/frontier filters in the generic model:
  - artifact:
    `default_vm_generic_model.decllift7.noabi.txt`
  - root status:
    `reachable=203 frontier=0 closed=true specializations=1`

- Landed model/materialization architecture fixes to stop non-control helper
  branches from re-opening the root:
  - root-slice callsite traversal/frontier now requires modeled
    `continuation_pc`
  - prelude recovery now suppresses non-candidate wrapper
    `call_target_mid_instruction` pollution when the wrapper already has local
    callsite chaining
  - direct-callee traversal in root-slice construction is gated to
    control-transfer-relevant handlers (`output_root`, `candidate`, dispatch,
    boundary, or continuation-tracked callsite)
  - unresolved non-candidate/no-dispatch callsites are treated as localized
    root-closure noise
  - adjacent-wrapper rewrite scope in `VirtualCFGMaterialization` is now
    bounded to one hop (no transitive explosion)
  - continuation/missing-target opportunistic lifting was removed from the
    semantic materialization fixpoint (kept for cleanup-stage handling)

- Verification:
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*:VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*`
    (`121/121` pass)
  - `build-remill/tools/omill-lift/omill-lift.exe ... --dump-virtual-model ...decllift7...`

- Current no-ABI default artifact status:
  - `CorpusVMP.default.vm.block.generic-on.decllift7.noabi.ll`
  - `dispatch_call=0`
  - `dispatch_jump=2`
  - `vm_entry=0`
  - `declare_blk=22`
  - `call_blk=77`
  - `musttail_blk=36`
  - `missing_block=4`
  - note: the remaining `dispatch_jump=2` calls are outside the closed
    root slice (root closure is already `frontier=0 closed=true`)

## March 14, 2026: Full-Suite Stability Fix (Iterative Analysis Registration)

- Fixed a full-unit-suite assertion in
  `ResolveDispatchTargetsTest.IterativeConvergence` caused by
  `IterativeTargetResolutionPass` assuming optional analyses were registered in
  all harnesses.

- Changes:
  - `IterativeTargetResolution.cpp` now checks
    `MAM.isPassRegistered<...>()` before querying optional module analyses
    (`BinaryMemoryAnalysis`, `IterativeLiftingSessionAnalysis`,
    `CallGraphAnalysis`).
  - If no shared iterative session analysis is registered, the pass now falls
    back to a local in-pass session object.
  - The resolve-dispatch iterative test harness explicitly registers
    `CallGraphAnalysis` and runs ITR with IPCP disabled for that isolated unit
    scenario.

- Verification:
  - `omill-unit-tests.exe --gtest_filter=ResolveDispatchTargetsTest.IterativeConvergence`
    (pass)
  - `omill-unit-tests.exe` full sweep: `712/712` passing.

- Stable ABI artifact:
  - `CorpusVMP.default.vm.block.generic-on.omill_dispatchlift11.verifyabi.ll`
  - `default_vm_generic_model.omill_dispatchlift11.verifyabi.txt`
  - metrics:
    `dispatch_call=0 dispatch_jump=0 vm_entry=0`
    `declare_blk=0 call_blk=0 musttail_blk=0 missing_block=0`
  - `clang -O2 -c` succeeds on emitted `.ll`

## March 18, 2026: Closed-Root ABI Collapse Fix

- Status:
  fixed the ABI cleanup gap that left live lifted-State IR reachable from
  `_native` wrappers even after root-slice closure. The issue was not another
  unresolved virtual frontier; it was `EliminateStateStructPass` forcing every
  `omill.output_root` lifted function to stay `NoInline`, including closed
  recovered roots that should have been allowed to collapse into their native
  wrappers.

- Implementation:
  - `EliminateStateStruct.cpp` now keeps the old `NoInline` policy only for
    non-closed output roots.
  - A lifted function that is both `omill.output_root` and
    `omill.closed_root_slice_root` is now internalized as inlinable:
    `OptimizeNone` removed, `NoInline` removed, `AlwaysInline` added.
  - Added unit coverage in `EliminateStateStructTest` for the new attribute
    policy and in `PipelineTest` for the full collapse path:
    closed lifted root inlines into `_native`, the lifted `sub_*` disappears,
    and live `__remill_read_memory_*` calls are lowered away.

- Compact/default impact:
  original corpus DLLs are not present in this workspace, so validation here
  used the existing closed no-ABI lifts plus `omill-opt --only-recover-abi`.
  Replaying ABI recovery on:
  - `CorpusVMP.compact.vm.block.generic-on.omill_current.noabi.ll`
  - `CorpusVMP.default.vm.block.generic-on.omill_current.noabi.ll`
  now produces:
  - `dispatch_call=0 dispatch_jump=0 vm_entry=0`
  - `declare_blk=0 call_blk=0`
  - `call_lifted_root=0 define_lifted_root=0 define_native_root=1`
  - `remill_read=0 remill_write=0 remill_sync=0`
  - `llc -filetype=obj -O2` succeeds on both replayed `.ll` files

- New diagnostic conclusion:
  the poor-quality ABI artifact was caused by a cleanup-policy mismatch after
  semantic recovery, not by missing dispatch resolution, missing jump-table
  recovery, or another VM-model frontier. The remaining external requirement
  is to rerun the full lift from the original corpus DLLs once those inputs are
  available in this checkout, so the stable replayed ABI shape becomes the
  default emitted artifact again.

## March 18, 2026: Default ABI VM-Context Cleanup Fix

- Status:
  fixed the remaining default-shape cleanup gap where ABI replay still kept
  dead or outlined `sub_*_native` wrappers carrying `%struct.State` allocas and
  `__remill_function_return` even after dispatches and lifted-root calls were
  gone.

- Root cause:
  - closed-slice native-helper inlining only considered `blk_*` / `block_*`
    names, so internal `sub_*_native` wrappers were excluded from the normal
    collapse path
  - dead `_native` helper internalization existed only in the late
    lift-infrastructure cleanup pipeline, not in `buildABIRecoveryPipeline`
  - on the default replay path, some surviving `_native` wrappers had already
    lost the `omill.closed_root_slice` string attr by the time the late ABI
    cleanup ran, so relying on slice attrs alone was insufficient

- Implementation:
  - `Pipeline.cpp` now treats eligible closed-slice `sub_*_native` helpers as
    native inlining candidates alongside `blk_*_native`
  - dead closed-slice native sub-wrappers bypass the inline-size budget so
    they can be internalized and dropped by `GlobalDCE`
  - `InternalizeDeadNativeHelpersPass` was hoisted into shared pipeline scope
    and added to `buildABIRecoveryPipeline`, preserving output roots via either
    native attrs or the corresponding lifted `sub_*` root metadata
  - added pipeline regressions for:
    - inlining closed-slice `sub_*_native` helpers
    - removing dead closed-slice `sub_*_native` helpers
    - removing dead native sub-helpers even when slice attrs are already gone

- Validation:
  - `omill-unit-tests.exe --gtest_filter=PipelineTest.*`:
    `35/35` pass
  - replayed ABI recovery with the rebuilt `omill-opt` on:
    - `CorpusVMP.default.vm.block.generic-on.omill_current.noabi.ll`
    - `CorpusVMP.compact.vm.block.generic-on.omill_current.noabi.ll`
  - resulting artifacts:
    - `abi_fix_probe/CorpusVMP.default.omill_current.recoverabi5.ll`
    - `abi_fix_probe/CorpusVMP.compact.omill_current.recoverabi5.ll`
  - both now report:
    - `define_sub_native=1`
    - `alloca_state=0`
    - `remill_return=0`
    - `remill_read=0`
    - `remill_write=0`
    - `dispatch_jump=0`
    - `declare_blk=0`
    - exported root shape restored to `define i64 @sub_180001850_native(ptr %0, ptr %1)`
  - `llc -filetype=obj -O2` succeeds on both replayed `.ll` files

## March 18, 2026: ABI-Run Closed-Slice Cleanup Gate Fix

- Status:
  fixed a real driver/pipeline bug in the fresh binary lift path, but did not
  finish end-to-end quality recovery for the current `omill` worktree.

- Root cause:
  - `tools/omill-lift/main.cpp` intentionally runs the main pipeline with
    `opts.recover_abi = false` and then invokes ABI recovery later as a
    separate stage
  - `buildIterativeResolutionEpoch` incorrectly used `!opts.recover_abi` to
    decide whether to schedule no-ABI-only closed-slice cleanup/materialization
    work in phase 3.9
  - as a result, normal ABI runs were taking the no-ABI phase-3.9 branch,
    including an extra `VirtualCFGMaterializationPass`
  - on fresh `CorpusVMP.compact.dll` relifts this manifested as a crash after
    `LiftConstantMissingBlockTargetsPass` / before the extra materialization

- Implementation:
  - `Pipeline.cpp` now gates the no-ABI-only phase-3.9 branch on
    `opts.no_abi_mode` instead of `!opts.recover_abi`
  - added a pass-scheduling regression in `PipelineTest`:
    `AbiIntendedPrePipelineSkipsNoAbiOnlyClosedSlicePasses`
    which verifies that ABI-intended pre-pipeline runs schedule exactly one
    `VirtualCFGMaterializationPass` and skip the no-ABI-only
    continuation/missing-block lift passes

- Validation:
  - focused tests:
    `PipelineTest.AbiIntendedPrePipelineSkipsNoAbiOnlyClosedSlicePasses`
    `PipelineTest.AbiPipelineInlinesClosedSliceNativeSubHelpers`
    `PipelineTest.AbiPipelineRemovesDeadNativeSubHelpersWithoutSliceAttrs`
    all pass
  - fresh binary relifts from:
    - `omill-main-remill/build-remill/test_obf/corpus/CorpusVMP.compact.dll`
    - `omill-main-remill/build-remill/test_obf/corpus/CorpusVMP.default.dll`
    now both complete without the previous compact crash

- Fresh compact/default impact:
  - this fixes the compact access violation in the main pipeline
  - it does **not** yet restore the high-quality closed-slice outputs in the
    current `omill` tree
  - fresh outputs remain poor:
    - compact still has live `__omill_dispatch_call`, declared/called `blk_*`,
      `%struct.State` allocas, and live Remill memory helpers
    - default still has `%struct.State` allocas, live Remill memory helpers,
      `__remill_sync_hyper_call`, and `unreachable` in the exported root
  - conclusion: the replay-only ABI cleanup fixes were valid, but the current
    `omill` source tree is still behind the sibling `omill-main-remill` tree on
    the actual generic devirtualization / continuation-closure implementation
## March 19, 2026: Late Continuation Cleanup Split and Current Residual Frontier

Status:
- Landed: experimental closed-slice continuation discovery is now opt-in via `OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY`.
- Landed: no-ABI closed-slice continuation relift/rematerialization is now opt-in via `OMILL_ENABLE_NOABI_CLOSED_SLICE_RELIFT`.
- Landed: phase 3.9 closed-slice cleanup now reseeds reachable `omill.closed_root_slice` membership around inline/DCE cleanup.
- Landed: safe constant continuation/missing-block lifting stays on by default in phase 3.9, without the unstable whole-slice rematerialization step.
- Landed: `omill-lift` now runs a bounded pre-ABI late continuation rerun for newly lifted continuation functions, scoped to those new functions only.
- Landed: env-gated diagnostics for continuation/missing-block target lifting via `OMILL_DEBUG_CONTINUATION_LIFTS=1`.

Compact impact:
- Fresh direct ABI relift no longer ends with declaration-only `blk_*` continuations.
- Current compact fresh ABI shape (`CorpusVMP.compact.dll`, `--va 0x180001850`, `--block-lift`, `--generic-static-devirtualize`):
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `call_blk=0`
  - `missing_block_handler=2`
  - `alloca_state=1`
  - `remill_read=0`
  - `remill_write=0`
- The surviving compact missing-block target is `0x5CF919FF`, which is out of image and currently looks like a genuine non-liftable boundary.

Default impact:
- Fresh direct ABI relift no longer ends with declaration-only `blk_*` continuations.
- Current default fresh ABI shape (`CorpusVMP.default.dll`, same root/options):
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `call_blk=0`
  - `missing_block_handler=5`
  - `alloca_state=4`
  - `remill_read=9`
  - `remill_write=12`
- The surviving default missing-block targets are in-image:
  - `0x18036A6B9`
  - `0x1801F77DD`
  - `0x1802181F4`
  - `0x180371172`

Newly discovered frontier shape:
- The original residual `blk_*` PCs were not decode failures. Direct lift probes for `0x18030F17A` and `0x180065449` both reached `Lifting complete`.
- `OMILL_DEBUG_CONTINUATION_LIFTS=1` showed that phase-3.9 continuation lifting successfully materializes only the first continuation layer (e.g. `0x18030F16D`, `0x18005C2F4`, `0x180031314`, `0x180065435`, `0x18005536A`, `0x180002065`).
- The remaining continuation PCs (`0x18030F17A`, `0x180065449`, `0x180055383`, `0x1800020B3`) are introduced later by those newly lifted bodies, which is why the one-shot phase-3.9 lift pass never saw them.
- The bounded late continuation rerun in `main.cpp` is what eliminates those declaration-only `blk_*` calls.
- After that rerun, the remaining frontier is no longer `blk_*` continuations. It is terminal missing-block boundaries emitted from `_native` continuations.

Next required architectural change:
- Add a bounded ABI-local recovery step for constant in-image missing-block-handler targets that appear inside late-lifted `_native` continuations.
- Do not re-enable the old blanket continuation discovery path for this. The current evidence points to a narrower ABI-local boundary continuation problem, not another generic dispatch frontier.

## March 19, 2026: ABI Late Semantic Helper Collapse and Codegen Repair

Status:
- Landed: ABI post-inline cleanup now marks small internal semantic helpers
  (`!remill.function.type`, direct-call only) for late inlining, not just
  `blk_*_native` / `sub_*_native` wrappers.
- Landed: ABI post-inline cleanup now reruns Remill lowering plus
  `DeadStateStoreDSE` + `SROA` on the final closed-slice body after those
  helpers inline.
- Landed: the semantic-helper inlining gate was widened so non-slice callers no
  longer block late ABI inlining for the helpers used by the live root.
- Landed: `omill-lift` now uses `Module::setModuleFlag` for
  `omill.no_abi_mode`, fixing duplicate module flags in fresh ABI output.

Validation:
- Focused pipeline tests pass:
  - `PipelineTest.AbiPipelineInlinesClosedSliceSemanticHelpersAndRelowersMemory`
  - `PipelineTest.AbiPipelineInlinesSemanticHelpersEvenWithNonSliceCallers`
- Fresh relifts from the sibling corpus inputs:
  - `omill-main-remill/build-remill/test_obf/corpus/CorpusVMP.default.dll`
  - `omill-main-remill/build-remill/test_obf/corpus/CorpusVMP.compact.dll`
- Fresh `verifyabi` outputs now assemble/codegen with `llc -filetype=obj -O2`
  after the module-flag fix.

Fresh compact/default impact:
- Compact fresh ABI shape (`CorpusVMP.compact.dll`, `--va 0x180001850`,
  `--block-lift`, `--generic-static-devirtualize`):
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `call_blk=0`
  - `alloca_state=1`
  - `remill_read=0`
  - `remill_write=0`
  - `semantic_calls=0`
  - live `__omill_missing_block_handler` callsites: `1`
- Default fresh ABI shape after the late semantic-helper collapse:
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `call_blk=0`
  - `alloca_state=0`
  - `remill_read=0`
  - `remill_write=0`
  - `semantic_calls=0`
  - live `__omill_missing_block_handler` callsites: `2`
- This closes the earlier “default still looks like a VM-context wrapper”
  issue. The fresh default root is now lowered/native-shaped; the remaining
  frontier is only terminal missing-block boundaries.

Newly discovered frontier shape:
- Remaining default boundary targets are now just:
  - `0x1801F77DD`
  - `0x180371172`
- Both are in-image `.7ir` entries, but they are not clean function starts.
  Current disassembly suggests mid-block / odd-entry continuation cases rather
  than a generic VM-state cleanup problem.
- Remaining compact boundary target is still `0x5CF919FF`, which is out of
  image and currently looks like a genuine external/non-liftable boundary.

Next required architectural change:
- Add a bounded ABI-local continuation/boundary recovery step for constant
  in-image `__omill_missing_block_handler` targets that survive after full ABI
  cleanup.
- Scope that work to the remaining default mid-block entries first. Compact’s
  out-of-image target should stay an explicit terminal boundary unless we add a
  separate external-target lifting mode.
## March 19, 2026: Bounded Late Missing-Block Rerun Stabilization

Status:
- Landed: added `PipelineOptions::skip_closed_slice_missing_block_lift` so a
  scoped rerun can suppress the generic phase-3.9 missing-block lift pass.
- Landed: the late missing-block rerun in `omill-lift` now uses that skip plus
  `use_block_lifting=false` for the special scoped rerun, so it does not
  re-enter the full block-discovery epoch on the newly lifted boundary roots.
- Landed: removed the extra recursive continuation wave after the late
  missing-block rerun. The scoped rerun already performs the local
  continuation-declaration lift; the extra round was what exploded into a large
  transitive continuation closure.
- Landed: added a focused pass-scheduling regression:
  `PipelineTest.ScopedLateRerunCanSkipClosedSliceMissingBlockLiftPass`.

Validation:
- Focused pipeline tests pass:
  - `PipelineTest.AbiIntendedPrePipelineSkipsNoAbiOnlyClosedSliceRematerialization`
  - `PipelineTest.ScopedLateRerunCanSkipClosedSliceMissingBlockLiftPass`
  - `PipelineTest.NoAbiPipelineRunsSafeClosedSliceContinuationLiftsByDefault`
- Fresh relifts from the sibling corpus inputs still complete and codegen:
  - `build-remill/test_obf/corpus/lifted/fresh_relift_fix17/default.ll`
  - `build-remill/test_obf/corpus/lifted/fresh_relift_fix17/compact.ll`
  - both assemble/codegen with `llc -filetype=obj -O2`

Fresh compact/default impact:
- Default fresh ABI shape (`CorpusVMP.default.dll`, `--va 0x180001850`,
  `--block-lift`, `--generic-static-devirtualize`):
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `vm_entry=0`
  - `missing_block_handler=0`
  - `declare_blk=1`
  - `call_blk=1`
  - `alloca_state=1`
  - `remill_read=0`
  - `remill_write=0`
  - `semantic_calls=0`
- Compact fresh ABI shape on the same tree:
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `vm_entry=0`
  - `declare_blk=0`
  - `call_blk=0`
  - live `__omill_missing_block_handler` callsites: `1`
  - `alloca_state=1`
  - `remill_read=0`
  - `remill_write=0`
  - `semantic_calls=0`

Newly discovered frontier shape:
- The bounded late missing-block rerun does real work on `default`: the two
  terminal `__omill_missing_block_handler` sites are gone in fresh ABI output.
- The remaining default readability issue is now ABI-local and singular:
  one external `blk_18023fe2d` continuation call survives inside
  `sub_180001850_native`, keeping one `%struct.State` alloca alive.
- That residual `blk_*` call is not present in `before_abi.ll`; it appears
  during ABI recovery, so the next fix is not another generic late
  continuation sweep. It is a post-ABI constant code-target recovery /
  continuation materialization issue.
- Compact remains on the earlier terminal external-boundary shape. The
  remaining target is still not a generic VM-state cleanup problem.

Next required architectural change:
- Add a bounded ABI-local recovery step for constant in-image continuation/code
  targets that only become visible inside closed-slice `_native` wrappers after
  ABI recovery.
- Scope it to closed-root-slice `_native` functions and require either:
  - a lifted definition is created in the same round, or
  - an existing lifted definition can be ABI-recovered in the same round.
- Do not reintroduce another blanket late continuation sweep. The stable path
  now shows that the remaining default issue is one ABI-local residual target,
  not another broad generic frontier.

## March 19, 2026: ABI Terminal Residual Continuation Classification

Status:
- Landed: added a late ABI cleanup step that rewrites terminal residual
  declaration-only `blk_*` continuation calls of the form
  `call @blk_<pc>(..., poison/null); unreachable` into explicit
  `__omill_missing_block_handler(pc)` boundaries.
- Landed: followed that rewrite with one more closed-slice-scoped
  DSE/SROA/InstCombine/GVN/ADCE/SimplifyCFG cleanup sweep so dead local
  `%struct.State` plumbing can collapse when the unresolved continuation was
  the last remaining user.
- Landed: added an ABI pipeline regression
  `PipelineTest.AbiPipelineTerminalizesPoisonMemoryBlockContinuationCalls`.

Validation:
- Focused pipeline tests pass:
  - `PipelineTest.AbiPipelineCollapsesNullMemoryBlockContinuationCalls`
  - `PipelineTest.AbiPipelineTerminalizesPoisonMemoryBlockContinuationCalls`
  - `PipelineTest.AbiIntendedPrePipelineSkipsNoAbiOnlyClosedSliceRematerialization`
  - `PipelineTest.ScopedLateRerunCanSkipClosedSliceMissingBlockLiftPass`
  - `PipelineTest.NoAbiPipelineRunsSafeClosedSliceContinuationLiftsByDefault`
- Fresh relifts from the sibling corpus inputs still complete:
  - `build-remill/test_obf/corpus/lifted/fresh_relift_fix21/default.ll`
  - `build-remill/test_obf/corpus/lifted/fresh_relift_fix21/compact.ll`
- Both fresh artifacts assemble/codegen with `llc -filetype=obj -O2`.

Fresh compact/default impact:
- Default fresh ABI shape (`CorpusVMP.default.dll`, `--va 0x180001850`,
  `--block-lift`, `--generic-static-devirtualize`):
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `call_blk=0`
  - `alloca_state=0`
  - `remill_read=0`
  - `remill_write=0`
  - live `__omill_missing_block_handler` callsites: `1`
- Compact fresh ABI shape on the same tree:
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `call_blk=0`
  - live `__omill_missing_block_handler` callsites: `1`
  - `alloca_state=1`
  - `remill_read=0`
  - `remill_write=0`

Newly discovered frontier shape:
- The remaining default residual was not a cheap continuation-lift miss.
  A direct block-lift probe of `0x18023fe2d` from the binary reached
  `AlwaysInlinerPass` and failed with LLVM out-of-memory.
- That makes this class of target a bounded terminal-boundary problem, not a
  good candidate for another automatic continuation wave.
- The new ABI terminalization step converts that residual from an external
  `blk_*` call into an explicit boundary marker and allows the wrapper-local
  state struct to disappear.

Next required architectural change:
- Add a real bounded late-target classifier for in-image residual boundaries so
  we can distinguish:
  - cheap liftable continuations
  - oversized / non-convergent targets that should terminalize immediately
- Apply that classifier before any future late continuation lifting attempt.
- Compact still has one surviving terminal boundary with `%struct.State`
  plumbing; that one now needs the same bounded classification/collapse logic
  for the remaining wrapper shape rather than more generic devirtualization.
- 2026-03-20: Landed bounded overlapping-slot partial-register import/propagation in the generic model. Compact impact: the root is still open (`reachable=66 frontier=2 closed=false`), but live predecessor handlers now carry merged wide-register facts derived from byte/word helper writes instead of dropping them. Newly observed frontier shape: the remaining `blk_180024ae7` jump-table target is blocked by nested low-lane merge-expression blowup (`or(and(...), and(...))`) rather than missing helper import/remap.
- 2026-03-20: Raised single-block leaf-helper local replay budget from `32` to `64` and added bounded finite-choice evaluation for local replay value expressions so `__remill_read_memory_*` can fold small finite image-address sets into constants/phis. Compact impact: no change yet (`reachable=66 frontier=2 closed=false`). Newly confirmed blocker shape: `blk_180024ae7` still ends as `NEXT_PC <- slot(arg0+0x8d8)` because `MOVSXI(..., arg3)` still falls back to the placeholder `stack(slot(arg3+0x0)+0x0)` and imports as `unmapped-import`; the computed table-read address is not a constant or small finite set under the current caller facts.
- 2026-03-20: Fixed the post-main no-ABI compact relift crash in `omill-lift` by bounding the late continuation rerun to one round in no-ABI mode. Validation: the previously crashing compact relift (`CorpusVMP.compact.dll --va 0x180001850 --block-lift --no-abi --generic-static-devirtualize`) now exits cleanly and emits `build-remill/test_obf/corpus/lifted/fresh_relift_fix41/compact.ll`, which also codegens with `llc -filetype=obj -O2`.
- 2026-03-20: Widened the late no-ABI rerun scope so newly lifted continuation blocks are reprocessed in closed-slice context, and added `VirtualMachineModelTest.TreatsLiftedCallsiteDispatchBlockWithMinimalStateAsCandidate` to cover lifted/block functions that carry `CALLI` plus dispatch edges with only minimal visible state. Validation: the new regression passes, and the focused `VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*` failure set remains unchanged at the existing 4 tests.
- 2026-03-20: Current compact no-ABI state after the crash fix is stable but still incomplete. Fresh artifact `build-remill/test_obf/corpus/lifted/fresh_relift_fix43/compact.ll` emits successfully, but still has live `__omill_dispatch_call=3`, `declare @blk_*=10`, and `call @blk_*=21`. The remaining issue is no longer the original jump-table frontier; it is a post-rerun call-frontier/materialization gap. The final LL contains late-lifted call blocks like `blk_180026eb7` with live `CALLI -> __omill_dispatch_call`, while the dumped virtual model still reflects only the pre-rerun closed slice. Next required architectural change: run a truthful final model/materialization pass over the post-rerun closed slice, then close or explicitly frontier those late-lifted `CALLI` blocks instead of reporting the slice as already closed.
- 2026-03-20: Landed a default no-ABI post-cleanup materialization sweep in `buildPipeline` and updated `PipelineTest` coverage. Validation: `PipelineTest.AbiIntendedPrePipelineSkipsNoAbiOnlyClosedSliceRematerialization`, `PipelineTest.NoAbiPipelineRunsSafeClosedSliceContinuationLiftsByDefault`, `PipelineTest.NoAbiPipelineCanSkipPostCleanupMaterialization`, and `PipelineTest.NoAbiPipelineEnablesExperimentalClosedSliceExpansionWhenRequested` all pass. Compact impact: the final model now matches the late no-ABI state by default, `__omill_dispatch_call` drops to `0`, and the live frontier is reported truthfully instead of as a stale pre-rerun closed slice.
- 2026-03-20: Added bounded single-bit-mask finite-choice evaluation (`x & 1` -> `{0,1}`) to the virtual model and enabled multi-successor lowering for `dispatch_jump` in `VirtualCFGMaterialization`. Validation: new regressions `VirtualMachineModelTest.ResolvesSingleBitMaskedSlotDispatchToFiniteSuccessors` and `VirtualCFGMaterializationTest.MaterializesDispatchFromSingleBitMaskedSlotChoices` pass, and the focused `VirtualMachineModelTest.*:VirtualCFGMaterializationTest.*` failure set is back to the same 4 pre-existing failures. Compact impact: `blk_180060f01` no longer stops at `unsupported_slot_provenance_target`; it now resolves to two concrete successor PCs (`0x18005CA5C`, `0x18005CA5D`) and is blocked only by `missing_lifted_target`.
- 2026-03-20: Added nearby-entry recovery for dispatch successors and covered it with `VirtualMachineModelTest.RecoversNearbyLiftedEntryForDispatchSuccessor` plus `VirtualCFGMaterializationTest.MaterializesDispatchToNearbyRecoveredLiftedEntry`. This is the generic fix for targets like `0x18005CA5C/0x18005CA5D` that land a few bytes into an already lifted `blk_*` entry.
- 2026-03-20: Added a bounded inverse fold for low-byte reconstruction patterns in the virtual-expression simplifier:
  - `or(and(x, ~0xff), and(zext(trunc(x)), 0xff)) -> x`
  - Validation: `VirtualMachineModelTest.ResolvesDispatchFromHelperMaskedLowByteReconstruction` and `VirtualCFGMaterializationTest.MaterializesDispatchFromHelperMaskedLowByteReconstruction` pass.
  - Compact impact: this targets the remaining `blk_180066044` / root frontier shape, where `NEXT_PC`-like targets are still wrapped in byte-mask reconstruction noise instead of exposing the underlying stack/slot fact.
  - Important constraint: a broader multi-round fact-specialization attempt regressed the full compact driver during `propagateVirtualStateFacts`, so it was backed out. The low-byte fold remains landed; the iterative propagation change does not.
- 2026-03-20: Split unknown dispatch frontiers into bounded executable vs terminal classes in the root-slice summary:
  - `dispatch_target_unlifted`
  - `dispatch_target_nearby_unlifted`
  - `dispatch_target_not_executable`
  - `dispatch_target_undecodable`
  - Validation: added `VirtualMachineModelTest.TreatsNonExecutableDispatchTargetAsClosedTerminalSlice`, `VirtualMachineModelTest.TreatsUndecodableDispatchTargetAsClosedTerminalSlice`, `VirtualMachineModelTest.MarksDecodableDispatchTargetAsUnliftedFrontier`, and `VirtualMachineModelTest.RecoversNearbyDispatchEntryAsCanonicalUnliftedFrontier`; all pass along with the nearby-entry and nested-phi dispatch materialization regressions.
  - Materialization impact: late lifting now attempts only executable dispatch frontiers (`dispatch_target_unlifted`, `dispatch_target_nearby_unlifted`) instead of treating every unknown dispatch PC as the same `missing_lifted_target`.
  - Compact impact: a binary-backed rerun from `CorpusVMP.compact.dll` still timed out before final emit, but the partial dump at `build-remill/test_obf/corpus/lifted/fresh_relift_fix65/compact.model.txt` confirms the live remaining handler is still `blk_180064933` with concrete successors `0x180061A0E` and `0x18006A04D`. The remaining gap is now final root-slice reporting / late attach for that mixed frontier, not more slot simplification.
- 2026-03-20: Narrowed root-slice membership and late rewrite seeding so helper semantics functions are no longer treated as devirtualized slice members by default.
  - Root-slice traversal still walks through helper semantics functions when they are the only bridge to a lifted `blk_*`, but only lifted/candidate/root/specialized code-bearing handlers are recorded in `reachable_handler_names`.
  - Late rewrite scope in `VirtualCFGMaterialization` now follows the same predicate instead of recursively pulling every defined helper callee into post-fixpoint materialization work.
  - Validation: `VirtualMachineModelTest.TraversesDirectLiftedCallChainsThroughNonCandidateBlocks` and `VirtualMachineModelTest.ExcludesVmSemanticsHelpersFromRootSliceMembers` pass, along with the existing dispatch-frontier coverage.
  - Compact impact: a short binary-backed rerun still did not reach the model dump within eight minutes, so there is no runtime delta yet, but this directly targets the helper-pollution seen in the earlier partial root-slice dump (`CALLI` / `LEAI` / `MOVI` listed as slice handlers).
- 2026-03-20: Narrowed the virtual-model initial seed set so generic devirtualization no longer starts from every `omill.vm_handler`.
  - Initial model seeding now starts from lifted/block/root/specialized/wrapper functions, then pulls helpers in only through actual direct-callee reachability.
  - This preserves helper summaries when a lifted root really calls them, but stops unreferenced semantics helpers from being summarized as full handlers up front.
  - Validation: `VirtualMachineModelTest.DoesNotSeedUnreferencedVmSemanticsHelpersIntoModel`, `VirtualMachineModelTest.ExcludesVmSemanticsHelpersFromRootSliceMembers`, `VirtualMachineModelTest.TracksVmStackFactsAcrossHelperPushPopChain`, and `VirtualCFGMaterializationTest.MaterializesDispatchFromHelperWrittenNextPcFacts` all pass on the updated tree.
  - Expected compact impact: lower handler-count and less work in `summarizeFunction` / `propagateVirtualStateFacts` before we even reach the root-scoped fixpoint loop. Runtime still needs a real binary-backed measurement.
- 2026-03-21: Tightened closed-slice code-bearing classification so `omill.closed_root_slice` alone no longer makes VM semantics helpers into virtual-model seeds.
  - Validation: added `VirtualMachineModelTest.DoesNotSeedClosedSliceTaggedVmSemanticsHelpersIntoModel`; it passes together with the existing closed-slice helper-chain regressions.
  - This fixes the specific seed pollution bug where phase 3.9 tagging could cause helper semantics functions to re-enter the generic model solely because they inherited `omill.closed_root_slice`.
- 2026-03-21: Added a no-ABI closed-slice scope rebuild pass and narrowed the phase 3.95 scoped FPM to code-bearing functions only.
  - Validation: added `PipelineTest.NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers`, while keeping `PipelineTest.AbiPipelineInlinesClosedSliceSemanticHelpersAndRelowersMemory` and `PipelineTest.AbiPipelineInlinesSemanticHelpersEvenWithNonSliceCallers` green.
  - This keeps no-ABI late cleanup from reusing helper-inline scope tags as if they were root-slice members.
- 2026-03-21: Wrapped phase 3.95 (`no-ABI post-cleanup materialization`) in a runtime closed-slice-scope guard.
  - Before this change, open-slice compact relifts still entered an unscoped late `VirtualMachineModelAnalysis` run and exploded to `summarize-handlers-done count=740`.
  - After this change, the same compact relift from `CorpusVMP.compact.dll --va 0x180001850 --block-lift --no-abi --generic-static-devirtualize` no longer re-enters that late 740-handler VM-model rebuild; the log proceeds directly from `Phase 3.95` to `Phase 4: ABI recovery`, `Phase 5: deobfuscation`, and `Final: cleanup`, and the run completes with emitted artifacts in `build-remill/test_obf/corpus/lifted/fresh_relift_fix73/`.
  - Remaining gap: the compact root slice is still open in the dumped model (`reachable=39 frontier=3 closed=false`), so the next work item is back to actual target closure (`blk_180026dce` dispatch frontier plus `blk_180055365` call frontier), not late semantics-helper performance.
- 2026-03-21: Added incremental handler-summary reuse inside `VirtualMachineModelAnalysis`.
  - The analysis now caches pre-canonicalization `summarizeFunction` results per module, keyed by LLVM structural function hash plus the function attributes that affect handler summarization (`omill.output_root`, specialization attrs, closed-slice attrs, vm-wrapper/clone attrs, etc.).
  - Validation: added `VirtualMachineModelTest.InvalidatesCachedHandlerSummaryAfterBodyChange` to prove body edits invalidate the cache; focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remain green.
  - Compact impact: the full no-ABI compact relift from `CorpusVMP.compact.dll --va 0x180001850 --block-lift --no-abi --generic-static-devirtualize` dropped from about `1137.3s` (`fresh_relift_fix73`) to about `1069.9s` (`fresh_relift_fix74`), a savings of roughly `67.5s` / `5.9%`.
  - The stage logs confirm the cache is doing real work during phase 3.8. By the final iterations the virtual-model summarize step reaches `hits=86 misses=0`, so remaining phase-3.8 cost is now dominated by propagation / successor summarization / rewrite work, not raw handler rescanning.
- 2026-03-21: Added two more low-risk phase-3.8 runtime cuts:
  - on-demand cached direct-callee discovery for the root-slice seed/worklist, instead of rebuilding a whole-module direct-callee map every `VirtualMachineModelAnalysis` run
  - removal of unnecessary final `VirtualMachineModelAnalysis` reruns in `VirtualCFGMaterialization` when the current iteration already holds a valid final model (and when dead-stub cleanup does not need a dump-accurate recompute)
  - Validation: focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remain green; the emitted compact artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix75/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift now drops again from about `1069.9s` (`fresh_relift_fix74`) to about `820.3s` (`fresh_relift_fix75`), another savings of roughly `249.6s` / `23.3%`.
  - End-to-end from the pre-optimization stable point (`fresh_relift_fix73`) to the current tree (`fresh_relift_fix75`), compact runtime dropped from about `1137.3s` to about `820.3s`, a total savings of roughly `317.1s` / `27.9%`.
  - Remaining runtime conclusion: phase 3.8 still dominates, but the repeated raw function rescans are no longer the main offender. The next real asymptotic change is to make `propagateVirtualStateFacts` and the downstream dispatch/root-slice recomputation dirty-set based instead of whole-model per iteration.
- 2026-03-21: Switched `propagateVirtualStateFacts` from whole-model outgoing recompute rounds to a conservative dirty-handler schedule.
  - Outgoing facts are now recomputed only for handlers whose incoming facts changed, whose direct callees changed outgoing facts, or which are conservatively marked callsite-sensitive after a target-summary change.
  - The incoming merge / prelude import pass is still whole-model, so this remains a low-risk scheduling optimization rather than a semantic rewrite of the propagation lattice.
  - Validation: focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remain green; the emitted compact artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix76/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift now drops again from about `820.3s` (`fresh_relift_fix75`) to about `678.9s` (`fresh_relift_fix76`), another savings of roughly `141.4s` / `17.2%`.
  - End-to-end from the earlier stable baseline (`fresh_relift_fix73`) to the current tree (`fresh_relift_fix76`), compact runtime dropped from about `1137.3s` to about `678.9s`, a total savings of roughly `458.5s` / `40.3%`.
  - Remaining runtime conclusion: phase 3.8 still dominates, but the expensive piece is now much more likely the full incoming merge / prelude import pass and the later dispatch/root-slice recomputation, not handler summarization or unconditional outgoing recompute.
- 2026-03-21: Made the remaining incoming-merge work in `propagateVirtualStateFacts` incremental as well.
  - Direct-callee incoming propagation now runs only for dirty source handlers instead of every handler with direct callees on every round.
  - Entry-prelude import now runs only for dirty prelude consumers instead of every handler with a recognized prelude on every round.
  - Incoming-fact merges now feed those two worklists explicitly, so propagation only revisits the direct-callee and prelude edges affected by a real lattice change.
  - Validation: focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remained green, and the emitted compact artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix77/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift dropped again from about `678.9s` (`fresh_relift_fix76`) to about `349.6s` (`fresh_relift_fix77`), another savings of roughly `329.3s` / `48.5%`.
  - End-to-end from the earlier stable baseline (`fresh_relift_fix73`) to `fresh_relift_fix77`, compact runtime dropped from about `1137.3s` to about `349.6s`, a total savings of roughly `787.7s` / `69.3%`.
- 2026-03-21: Removed dead broad callsite-handler invalidation from `propagateVirtualStateFacts`.
  - The propagation loop was still re-enqueuing every handler with a `callsites` summary whenever any outgoing fact changed, even though outgoing recomputation no longer applies localized callsite-return effects there.
  - That broad invalidation was dead work: handlers with real incoming changes were already being re-enqueued through the normal incoming-fact worklists, while unrelated callsite-bearing handlers were just burning extra propagation rounds.
  - Validation: focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remain green, and the emitted compact artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix78/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift dropped again from about `349.6s` (`fresh_relift_fix77`) to about `332.7s` (`fresh_relift_fix78`), another savings of roughly `16.9s` / `4.8%`.
  - End-to-end from the earlier stable baseline (`fresh_relift_fix73`) to `fresh_relift_fix78`, compact runtime dropped from about `1137.3s` to about `332.7s`, a total savings of roughly `804.6s` / `70.7%`.
  - Remaining runtime conclusion: whole-model propagation is no longer the obvious bottleneck. The next likely cost center is repeated full downstream analysis in phase 3.8 (`summarizeDispatchSuccessors`, `summarizeCallSites`, `summarizeRootSlices`, and the surrounding materialization iterations), which now needs stage timing and then a dirty-set redesign rather than another blind invalidation cut.
- 2026-03-21: Added per-stage timing inside `VirtualMachineModelAnalysis::run` and remeasured compact on the reverted `fresh_relift_fix78` baseline.
  - Validation: focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remain green, and the emitted compact artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix80/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift now measures at about `329.1s` in `fresh_relift_fix80`, essentially matching the `fresh_relift_fix78` baseline and confirming the earlier failed lookup-map rewrite was noise rather than a real win.
  - Stage-timing result: the remaining cost is overwhelmingly inside `propagateVirtualStateFacts`, not the downstream summary passes.
    - Late virtual-model runs with `~85-86` handlers spend about `41-42s` in `propagateVirtualStateFacts`.
    - The same runs spend only about `0.7-0.8s` in `summarizeCallSites`, about `0-0.002s` in dispatch/root-slice/region summarization, and only a few milliseconds in canonicalization.
    - Handler summarization is now small as well: mostly tens of milliseconds, with the cache eliminating almost all rescanning by the late iterations.
  - Updated runtime conclusion: the next real optimization target is now inside propagation itself, most likely repeated localized single-block outgoing replay and the remaining dirty-worklist churn inside `propagateVirtualStateFacts`, not `summarizeDispatchSuccessors`, `summarizeCallSites`, or `summarizeRootSlices`.
- 2026-03-21: Added a top-level localized single-block replay cache inside `propagateVirtualStateFacts`.
  - The cache is scoped to a single propagation run and keyed by:
    - handler function
    - current incoming slot facts
    - current incoming stack facts
    - current incoming argument facts
    - current direct-callee outgoing slot/stack facts
  - This avoids recomputing the same top-level localized handler replay across propagation rounds when neither the handler inputs nor the callee summaries actually changed.
  - Validation: focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regressions remain green, and the emitted compact artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix81/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift dropped again from about `329.1s` (`fresh_relift_fix80`) to about `314.1s` (`fresh_relift_fix81`), another savings of roughly `15.0s` / `4.6%`.
  - Stage-timing result: the cache gets real reuse even in late iterations, but only at the top-level handler replay layer. The late propagation-heavy runs still spend about `39-40s` in `propagateVirtualStateFacts`, so most remaining cost is deeper than the top-level replay entry.
- 2026-03-21: Tried extending the replay cache one level deeper to callsite-localized direct-callee replay inside `applySingleDirectCalleeEffects`, then reverted it.
  - The experiment did produce substantial nested cache hits, but on the real compact run it regressed total time from about `314.1s` (`fresh_relift_fix81`) to about `330.8s` (`fresh_relift_fix82`).
  - The likely reason is cache-key construction overhead on the hot nested path outweighing the saved replay work.
  - Current tree is reverted to the faster `fix81` shape, keeping the top-level propagation replay cache and the stage instrumentation while dropping the nested callsite cache complexity.
- 2026-03-21: Added iteration-level propagation diagnostics under `OMILL_DEBUG_VIRTUAL_MODEL_STAGES`.
  - `propagateVirtualStateFacts` now logs per-iteration:
    - dirty handler count
    - dirty direct-call source count
    - dirty prelude count
    - localized replay attempt/success counts
    - iteration time
  - Binary-backed compact rerun with this extra logging (`fresh_relift_fix83`) confirms the remaining late propagation cost is not mostly localized replay.
    - In the late `85-86` handler runs, top-level localized attempts stay relatively small (`~10-15` in the busiest rounds).
    - But the worklist still churns across many iterations with very large dirty sets (`~58-86` dirty handlers, `10-13` rounds in the worst runs).
    - The direct-call source worklist is already mostly gone after the first `1-2` rounds; the remaining time is dominated by repeated handler reprocessing after outgoing-change fanout, not by sustained argument-import work.
  - Updated runtime conclusion: the next real optimization target is now dirty-worklist convergence inside `propagateVirtualStateFacts` itself, especially repeated incoming-merge/prelude churn, not another replay cache layer.
- 2026-03-21: Tried restricting direct-call argument propagation to only newly tracked live-in argument IDs, then reverted it.
  - The idea was sound in isolation, but on the real compact run it regressed total time from about `314.1s` (`fresh_relift_fix81`) to about `344.5s` (`fresh_relift_fix85`).
  - Current tree is reverted to the faster `fix81` behavior, keeping the propagation diagnostics but dropping the argument-live-in gating.
  - Practical conclusion: the remaining late dirty rounds are not being driven primarily by irrelevant direct-call argument facts, so the next optimization should target outgoing-change fanout or handler-level convergence checks instead.
- 2026-03-21: Tightened localized replay output tracking to only export actually written slot / stack facts.
  - `computeLocalizedSingleBlockOutgoingFacts` now records the exact canonical slot IDs and stack-cell IDs it writes, including writes imported from nested localized direct callees.
  - `propagateVirtualStateFacts` and direct-callee import now filter localized outputs through those precise write sets instead of treating every carried-through fact in the localized state snapshot as a write.
  - Validation: the focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` runtime/regression set remained green before and after the change.
  - Compact impact: the full no-ABI compact relift dropped from about `314.1s` (`fresh_relift_fix81`) to about `278.9s` (`fresh_relift_fix87`), a savings of roughly `35.2s` / `11.2%`.
  - Semantic impact: the dumped compact root slice shape did not change; it remains `reachable=38 frontier=2 closed=false`, with the same `blk_180055365` call frontier and `blk_180026dce` dispatch frontier.
- 2026-03-21: Added a cached non-localized outgoing-facts path inside `propagateVirtualStateFacts`.
  - Non-localized outgoing fact computation is now cached per module, keyed by:
    - handler function fingerprint
    - current incoming slot facts
    - current incoming stack facts
    - current incoming argument facts
    - current direct-callee outgoing slot / stack facts
  - The cache stores the fully rebased outgoing slot / stack facts plus the stack-budget flag, so late propagation rounds can skip recomputing `computeOutgoingFacts`, `computeOutgoingStackFacts`, and `applyDirectCalleeEffects` when the effective inputs are unchanged.
  - Validation: added `VirtualMachineModelTest.InvalidatesCachedOutgoingFactsAfterCalleeBodyChange`, and the focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regression set remained green. The emitted artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix88/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift dropped again from about `278.9s` (`fresh_relift_fix87`) to about `199.5s` (`fresh_relift_fix88`), another savings of roughly `79.4s` / `28.5%`.
  - End-to-end from the earlier stable baseline (`fresh_relift_fix73`) to `fresh_relift_fix88`, compact runtime dropped from about `1137.3s` to about `199.5s`, a total savings of roughly `937.8s` / `82.5%`.
  - Updated runtime conclusion: handler-summary rescanning and plain outgoing transfer recomputation are no longer the main issue. The remaining late cost is dirty-worklist convergence in `propagateVirtualStateFacts` itself, especially repeated outgoing-change fanout across the last open frontier handlers.
- 2026-03-21: Narrowed reverse-caller invalidation to caller-visible callee output changes.
  - `propagateVirtualStateFacts` still treats any outgoing change as relevant for:
    - the handler's own direct-callee propagation
    - entry-prelude consumers
  - But reverse callers are now only re-enqueued when the callee changed outputs that a caller can actually observe:
    - written slot IDs
    - rebased written stack-cell IDs
  - This avoids reopening caller handlers when only pass-through incoming facts changed inside the callee's full outgoing map.
  - Validation: the focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regression set remained green. The emitted artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix89/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift dropped again from about `199.5s` (`fresh_relift_fix88`) to about `180.0s` (`fresh_relift_fix89`), another savings of roughly `19.5s` / `9.8%`.
  - End-to-end from the earlier stable baseline (`fresh_relift_fix73`) to `fresh_relift_fix89`, compact runtime dropped from about `1137.3s` to about `180.0s`, a total savings of roughly `957.3s` / `84.2%`.
  - Semantic impact: the compact root slice remains unchanged at `reachable=38 frontier=2 closed=false`, with the same `blk_180055365` call frontier and `blk_180026dce` dispatch frontier.
- 2026-03-21: Added persistent propagation-state reuse across successive `VirtualMachineModelAnalysis` runs.
  - Each handler now caches a stable, cross-run propagation snapshot keyed by:
    - handler function fingerprint
    - stable incoming argument facts
    - stable incoming slot facts
    - stable outgoing slot facts
    - stable incoming stack facts
    - stable outgoing stack facts
    - stack-budget flag
  - The cached facts are stored in slot/stack summary form rather than raw canonical IDs, then re-annotated against the current model on restore. That avoids relying on slot/cell ID stability across reruns.
  - New VM-model runs now restore unchanged handlers from the previous solved lattice state and seed the initial dirty worklists only from changed/new handlers plus their direct dependents.
  - Validation: the focused `VirtualMachineModelTest`, `VirtualCFGMaterializationTest`, and `PipelineTest` regression set remained green, and the emitted artifact in `build-remill/test_obf/corpus/lifted/fresh_relift_fix90/` still codegens with `llc -filetype=obj -O2`.
  - Compact impact: the same full no-ABI compact relift dropped again from about `180.0s` (`fresh_relift_fix89`) to about `67.8s` (`fresh_relift_fix90`), another savings of roughly `112.2s` / `62.3%`.
  - End-to-end from the earlier stable baseline (`fresh_relift_fix73`) to `fresh_relift_fix90`, compact runtime dropped from about `1137.3s` to about `67.8s`, a total savings of roughly `1069.5s` / `94.0%`.
  - Stage evidence: after the first VM-model run, later runs restore most handlers directly (`restored-state handlers=80+` in the late compact iterations), and many of those reruns now spend only `~0.1s-2.5s` in propagation unless a newly lifted frontier target forces a real wave through the slice.
  - Semantic impact: the compact root slice remains unchanged at `reachable=38 frontier=2 closed=false`, with the same `blk_180055365` call frontier and `blk_180026dce` dispatch frontier.
- 2026-03-21: Started structural cleanup of the generic VM model code layout.
  - Added a dedicated public folder under `include/omill/Analysis/VirtualModel/`:
    - `Types.h` for the public VM model enums / summaries / fact structs
    - `Analysis.h` for `VirtualMachineModel` and `VirtualMachineModelAnalysis`
  - Converted `include/omill/Analysis/VirtualMachineModel.h` into a compatibility umbrella that includes the new headers, so existing call sites do not need to move immediately.
  - Split stable, non-analysis implementation out of the old monolithic source into:
    - `lib/Analysis/VirtualModel/Render.cpp`
    - `lib/Analysis/VirtualModel/Model.cpp`
  - Validation: `omill-unit-tests` rebuilds cleanly, and the focused VM/pipeline regression set remains green (`7/7`).
  - Cleanup status: this is the first stage only. The heavy analysis implementation still lives in `lib/Analysis/VirtualMachineModel.cpp`, but the public types/API boundary is now isolated enough to continue decomposing propagation, replay, and root-slice logic without churning every include site.
- 2026-03-21: Split the VM-model analysis driver from the remaining monolithic implementation.
  - Added `lib/Analysis/VirtualModel/Internal.h` as the shared internal boundary for:
    - per-module VM-model cache state
    - localized replay/cache record types
    - analysis-driver-visible helper declarations
  - Moved `VirtualMachineModelAnalysis::Key` and `VirtualMachineModelAnalysis::run` into `lib/Analysis/VirtualModel/Driver.cpp`.
  - Converted the remaining VM-model implementation in `lib/Analysis/VirtualMachineModel.cpp` into the `omill::virtual_model::detail` namespace, so the file now has a real internal namespace boundary instead of a single anonymous-namespace blob.
  - Validation: full `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith is now mostly analysis-core logic rather than mixed public API + driver + rendering + caches. The next clean split point is one of:
    - propagation/caching
    - helper-local replay
    - successor/root-slice/region summarization
- 2026-03-21: Split root-slice summarization into its own VM-model file.
  - Added `lib/Analysis/VirtualModel/RootSlices.cpp` for:
    - root-slice reachability walk
    - call/dispatch frontier classification at the slice layer
    - terminal-frontier closure logic
  - Extended `lib/Analysis/VirtualModel/Internal.h` with the small internal API that root-slice summarization needs from the core analysis file:
    - entry-prelude direct-call detection
    - executable/decodable target checks
    - target-architecture query
    - nearby executable entry recovery
  - Removed the old `summarizeRootSlices` implementation from `lib/Analysis/VirtualMachineModel.cpp`, and deleted the now-dead duplicate frontier helper left behind in the monolith.
  - Validation: full `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith is smaller again and no longer owns the root-slice closure layer. The next reasonable split points are `summarizeVirtualRegions`, `summarizeDispatchSuccessors`, or the propagation/cache engine.
- 2026-03-21: Split region summarization into its own VM-model file.
  - Added `lib/Analysis/VirtualModel/Regions.cpp` for:
    - region component construction
    - boundary-adjacent region membership
    - region-level incoming/outgoing fact aggregation
  - Extended `lib/Analysis/VirtualModel/Internal.h` with the minimal additional internal API needed by region summarization:
    - `evaluateVirtualExpr`
    - `mergeIncomingExpr`
    - `unknownExpr`
    - `resolveBoundaryNameForTarget`
  - Removed the old `summarizeVirtualRegions` implementation from `lib/Analysis/VirtualMachineModel.cpp`.
  - Validation: full `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith now holds mostly:
    - propagation/caching
    - helper-local replay and call import
    - dispatch/callsite summarization
    - low-level expression/fact utilities
  - Next clean split points are `summarizeDispatchSuccessors` or the propagation/cache engine.
- 2026-03-21: Split dispatch-successor summarization into its own VM-model file.
  - Added `lib/Analysis/VirtualModel/Dispatch.cpp` for:
    - dispatch target specialization against handler/region facts
    - protected-boundary dispatch successor classification
    - nearby lifted-entry dispatch recovery
  - Removed the old `summarizeDispatchSuccessors` implementation and its dispatch-only helper cluster from `lib/Analysis/VirtualMachineModel.cpp`.
  - Kept the generic fact-map helpers in `lib/Analysis/VirtualMachineModel.cpp` for the remaining callsite summarization path, so this split does not force a larger callsite refactor yet.
  - Validation: `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith is now mostly:
    - propagation/caching
    - helper-local replay and direct-callee/callsite import
    - callsite summarization
    - low-level expression/fact utilities
  - Next clean split points are `summarizeCallSites` or the propagation/cache engine.
- 2026-03-21: Split shared fact-conversion helpers into their own VM-model file.
  - Added `lib/Analysis/VirtualModel/Facts.cpp` for the common conversions between:
    - slot fact vectors and slot-ID maps
    - stack fact vectors and cell-ID maps
    - argument fact vectors and argument-ID maps
  - Promoted those helpers through `lib/Analysis/VirtualModel/Internal.h`, so both `Dispatch.cpp` and the remaining monolith use the same internal API instead of carrying duplicate local definitions.
  - Removed the duplicate fact-conversion helpers from `lib/Analysis/VirtualMachineModel.cpp` and `lib/Analysis/VirtualModel/Dispatch.cpp`.
  - Validation: `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith is now more concentrated on:
    - propagation/caching
    - helper-local replay and direct-callee/callsite import
    - callsite summarization
    - low-level expression/fact evaluation and canonicalization
  - Next clean split point remains `summarizeCallSites`; after that, the largest remaining chunk is the propagation/cache engine.
- 2026-03-21: Split shared target/state lookup helpers out of the monolith.
  - Added `lib/Analysis/VirtualModel/Targets.cpp` for:
    - lifted-call continuation inference
    - handler lookup by entry VA
    - executable/mapped/decodable target classification
    - nearby lifted-entry / executable-entry recovery
  - Extended `lib/Analysis/VirtualModel/Facts.cpp` with the slot-info and stack-cell-info map builders that were previously private to `lib/Analysis/VirtualMachineModel.cpp`.
  - Promoted those shared helpers through `lib/Analysis/VirtualModel/Internal.h`, so dispatch, root-slice, and the remaining callsite code use the same internal target/state lookup API.
  - Removed the corresponding duplicate target helper implementations from `lib/Analysis/VirtualMachineModel.cpp` and the duplicate nearby-entry helper from `lib/Analysis/VirtualModel/Dispatch.cpp`.
  - Validation: `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith is now more clearly concentrated on:
    - propagation/caching
    - helper-local replay and direct-callee import
    - callsite/localized-return summarization
    - low-level expression/fact evaluation and canonicalization
  - Next clean split point is still the callsite/localized-return layer; this target/state extraction was the prerequisite that makes that split smaller and less coupled.
- 2026-03-21: Split callsite summarization into its own VM-model file.
  - Added `lib/Analysis/VirtualModel/CallSites.cpp` for:
    - the `summarizeCallSites` pass
    - pass-local `NEXT_PC`/`RETURN_PC` fallback matching helpers used only by that pass
  - Promoted the small shared callsite summary surface through `lib/Analysis/VirtualModel/Internal.h`:
    - `ResolvedCallSiteInfo`
    - `LocalCallSiteState`
    - `computeLocalFactsBeforeCall`
    - `resolveCallSiteInfo`
    - `computeResolvedCallTargetOutgoingFacts`
    - `normalizeLocalizedExprForCaller`
  - Also promoted the shared debug/transfer helpers needed by the new file:
    - `vmModelImportDebugLog`
    - `isBoundedLocalizedTransferExpr`
    - `rebaseWrittenStackCellIds`
  - Removed the old `summarizeCallSites` implementation and its pass-local helper block from `lib/Analysis/VirtualMachineModel.cpp`.
  - Validation: `omill-unit-tests` rebuild succeeded, and the focused VM/pipeline regression set remained green (`7/7`).
  - Cleanup status: the remaining monolith is now primarily:
    - propagation/caching
    - helper-local replay and direct-callee/localized-import machinery
    - low-level expression/fact evaluation and canonicalization
  - Next clean split points are now:
    - the direct-callee/localized-import layer
    - or the propagation/cache engine
- Refactor: moved shared transfer/rebasing helpers out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Transfers.cpp`, including localized-transfer bounding, argument detection, stack-cell rebasing, and fact-map merge helpers. Focused VM/pipeline regression set stayed green after the split.
- Refactor: moved summary key/lookup helpers and propagation-cache capture/restore helpers out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Facts.cpp` and `lib/Analysis/VirtualModel/PropagationCache.cpp`. The monolith now carries less VM data plumbing and the focused regression set stayed green after both splits.
- Refactor: moved caller/callee remap and import-normalization helpers out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Imports.cpp`, including structural slot/stack remap, caller-local normalization, and mapped caller slot/stack-cell lookup. Promoted the shared remap/import surface through `lib/Analysis/VirtualModel/Internal.h`, added the new file to `lib/CMakeLists.txt`, and kept the focused VM/pipeline regression set green (`7/7`).
- Refactor: moved pre-call state reconstruction and specialized call-argument helpers out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/CallState.cpp`, including `computeLocalFactsBeforeCall`, `summarizeSpecializedCallArg`, and `buildSpecializedCallArgumentMap`. Promoted the fixpoint-specialization helpers through `lib/Analysis/VirtualModel/Internal.h`, wired the new file in `lib/CMakeLists.txt`, and kept the focused VM/pipeline regression set green (`7/7`).
- Refactor: moved the shared localization/local-replay support layer out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Localization.cpp`, including:
  - read-only binary constant reads for replay/evaluation
  - localized replay block collection and gating
  - state-slot / stack-cell expression builders
  - caller-state argument detection and recursive localization bounds
  - specialized constant resolution and call-continuation stack seeding helpers
  - promoted the local-replay debug wrappers and localization depth cap through `lib/Analysis/VirtualModel/Internal.h`
  - added the new file to `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: moved direct callsite target resolution out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/CallSites.cpp`, including the local `RETURN_PC` seeding helper and the `resolveCallSiteInfo` implementation. This keeps callsite-resolution logic with the existing callsite summarization pass and trimmed the monolith again. Validation remained green on the focused VM/pipeline regression set (`7/7`).
- Refactor: moved the direct-callee import/application layer out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/DirectCallees.cpp`, including:
  - direct-callee per-call import
  - caller-local slot/stack remap and merge for imported callee outputs
  - call-root import path for resolved call targets
  - the public `applyDirectCalleeEffects` / `applyDirectCalleeEffectsImpl` internal entry points
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: moved the localized call-return / call-root continuation layer out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/LocalizedCalls.cpp`, including:
  - localized callsite outgoing-state import
  - resolved call-target continuation import
  - localized call-return effect application
  - entry-prelude target localization
  - promoted the replay-entry and entry-prelude hooks through `lib/Analysis/VirtualModel/Internal.h`
  - wired the new file into `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: moved the low-level state-fact / expression utility cluster out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/StateFacts.cpp`, including:
  - bit-width casting for state expressions
  - masked low-bit reconstruction simplification
  - low-bit merge into wider aliased state slots
  - aliased state-slot write propagation
  - bounded argument/state fact classification
  - identity/remappable/global-mergeable fact predicates
  - caller-local alloca-state detection
  - added the shared surface to `lib/Analysis/VirtualModel/Internal.h`
  - wired the new file into `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: moved the helper-local replay engine out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Replay.cpp`, including:
  - `computeLocalizedSingleBlockOutgoingFacts`
  - sequential local slot/stack/value replay for single-block helpers
  - bounded read-memory constant folding and tracked stack-cell replay
  - direct-callee replay integration and written slot/cell tracking
  - wired the new file into `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: moved the propagation/caching flow out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Propagation.cpp`, including:
  - `canonicalizeVirtualState`
  - `propagateVirtualStateFacts`
  - propagation-local outgoing-fact cache helpers and map comparison helpers
  - canonicalization-local slot/stack live-in collection helpers
  - added the shared referenced-slot collector to `lib/Analysis/VirtualModel/Internal.h`
  - wired the new file into `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- VM-model refactor status:
  - the previous “remaining categories” list is now cleared
  - `lib/Analysis/VirtualMachineModel.cpp` is down to about `1570` lines and now mainly holds the core summary/value-evaluation implementation rather than the model driver, propagation engine, or helper replay/import layers
- Refactor: moved the function-summary / candidate-classification layer out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Summary.cpp`, including:
  - specialization-attribute parsing helpers
  - summary-relevant function fingerprinting
  - boundary/helper/code-bearing classification helpers
  - `summarizeFunction`
  - `collectDirectCalleesForFunction`
  - wired the new file into `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: moved the expression-evaluation / specialization core out of `VirtualMachineModel.cpp` into `lib/Analysis/VirtualModel/Core.cpp`, including:
  - `isCallSiteHelper`
  - recursive `evaluateVirtualExpr` folding
  - slot/stack annotation and memory-read canonicalization helpers
  - expression equality / unknown classification / symbolic-ref counting
  - finite target/value choice collection
  - specialization and outgoing-fact construction helpers
  - boolean-flag slot/expr-key builders
  - entry-prelude direct-call detection
  - wired the new file into `lib/CMakeLists.txt`
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- VM-model refactor status:
  - `lib/Analysis/VirtualMachineModel.cpp` is now down to about `241` lines
  - it mainly holds the shared debug/cache wrappers plus boundary-name resolution glue
- Refactor: moved the final glue out of `VirtualMachineModel.cpp` and completed the folder split:
  - moved shared debug/cache wrapper definitions into `lib/Analysis/VirtualModel/Driver.cpp`
  - moved boundary-name resolution glue into `lib/Analysis/VirtualModel/Targets.cpp`
  - removed `lib/Analysis/VirtualMachineModel.cpp` from `lib/CMakeLists.txt` and deleted the file
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- VM-model refactor status:
  - the implementation now lives entirely under `lib/Analysis/VirtualModel/`
  - the public surface lives under `include/omill/Analysis/VirtualModel/`
  - `include/omill/Analysis/VirtualMachineModel.h` remains as a compatibility umbrella
- Refactor: switched internal consumers off the compatibility umbrella and onto the new public VM-model surface:
  - `lib/Analysis/VirtualModel/Internal.h` now includes `omill/Analysis/VirtualModel/Analysis.h`
  - internal consumers like `lib/Pipeline.cpp`, `lib/Passes/VirtualCFGMaterialization.cpp`, and `tests/unit/VirtualMachineModelTest.cpp` now include the `VirtualModel` headers directly
  - `include/omill/Analysis/VirtualMachineModel.h` remains only as a compatibility include
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: split the internal VM-model declaration surface so `lib/Analysis/VirtualModel/Internal.h` is now only an umbrella:
  - `lib/Analysis/VirtualModel/DetailTypes.h` now carries the internal cache/key/state structs
  - `lib/Analysis/VirtualModel/DetailDecls.h` now carries the internal function declarations
  - `lib/Analysis/VirtualModel/Internal.h` now just includes those two headers
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: split the internal declaration umbrella into categories:
  - `lib/Analysis/VirtualModel/CoreDecls.h` now carries the core/shared declaration surface
  - `lib/Analysis/VirtualModel/FlowDecls.h` now carries the analysis-flow / localization / target declarations
  - `lib/Analysis/VirtualModel/DetailDecls.h` is now only an umbrella over those category headers
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Refactor: split the remaining specialization / evaluated-choice cluster out of `lib/Analysis/VirtualModel/Core.cpp` into `lib/Analysis/VirtualModel/Specialization.cpp`, including:
  - bounded target-choice collection
  - bounded value-choice collection
  - expression specialization and fixpoint helpers
  - outgoing slot/stack fact construction
  - boolean-flag slot/key builders
  - validation: `omill-unit-tests` rebuild succeeded and the focused VM/pipeline regression set stayed green (`7/7`)
- Corpus rerun / devirtualization follow-up after the VM-model folder split:
  - tightened localized replay caller-stack lookup in `lib/Analysis/VirtualModel/Replay.cpp` so the remapped helper path now uses the same exact/equivalent/rebased lookup logic as the direct path
  - threaded fallback caller slot/stack facts through nested localized direct-callee replay (`FlowDecls.h`, `LocalizedCalls.cpp`, `DirectCallees.cpp`, `Replay.cpp`) so nested helper replay can still consult outer caller-local VM-stack state
  - validation: focused regressions stayed green:
    - `VirtualMachineModelTest.InvalidatesCachedHandlerSummaryAfterBodyChange`
    - `VirtualMachineModelTest.InvalidatesCachedOutgoingFactsAfterCalleeBodyChange`
    - `VirtualMachineModelTest.DoesNotSeedClosedSliceTaggedVmSemanticsHelpersIntoModel`
    - `VirtualMachineModelTest.TracksVmStackFactsAcrossHelperPushPopChain`
    - `VirtualMachineModelTest.RemapsHelperRelativeVmStackFactsIntoCallerLocalNextPc`
    - `PipelineTest.NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers`
  - compact rerun artifact: `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_fixreplay1/compact.model.txt`
    - root slice improved from `reachable=38 frontier=3 closed=false` to `reachable=32 frontier=1 closed=false`
    - eliminated the `blk_180055365` call frontier and the `blk_180026dce` dispatch frontier
    - remaining frontier is only `blk_180060f01` with `dynamic_target`
  - compact impact:
    - `blk_180064933` now produces caller-local `NEXT_PC = add(stack(slot(arg0+0x908)-0x40), 0x571a)`
    - `blk_180060f01` still stops at `dispatch jump target=slot(NEXT_PC+0x0)` with `specialized_target=add(slot(NEXT_PC+0x0), 0x2)`
    - no specialization clone is created yet (`specializations=0`)
  - remaining compact frontier shape:
    - localized replay does recover some `POPI` reads to constants (`0x18005c2f4`, `0x18005c2e3`)
    - the final unresolved path uses a caller-specialized structural stack cell `stack(slot(arg0+0x908)-0x40)` that has no canonical stack-cell id in the current model, so helper-local replay can carry it symbolically but cannot fold/export it as a normal tracked stack fact yet
  - default rerun remains unstable:
    - `CorpusVMP.default.dll` still exits with `0xC0000005`
- Compact follow-up after the structural stack carry work:
  - landed the actual-cell remap fix in:
    - `lib/Analysis/VirtualModel/Imports.cpp`
    - `lib/Analysis/VirtualModel/DirectCallees.cpp`
    - `lib/Analysis/VirtualModel/LocalizedCalls.cpp`
  - those paths now preserve argument-relative stack-cell base offsets when remapping helper-local expressions through caller operands
  - landed a narrow propagation improvement in `lib/Analysis/VirtualModel/Propagation.cpp`:
    - direct-callee import now treats stack/slot ids referenced by specialized dispatch/callsite targets as dynamic live-ins for the callee
    - this stayed stable on the compact corpus; a broader outgoing-fact dependency promotion was tried and reverted because it blew up memory
  - validation:
    - `VirtualMachineModelTest.RemapsHelperRelativeVmStackFactsIntoCallerLocalNextPc`
    - `VirtualMachineModelTest.TracksVmStackFactsAcrossHelperPushPopChain`
    - `VirtualMachineModelTest.AddsPreludeDirectCallTargetAsRootSliceFrontier`
    - `VirtualMachineModelTest.SeedsMidBlockEntryFromPreludeDirectCallReturnFacts`
    - `PipelineTest.NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers`
  - stable compact rerun artifact: `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_fixstruct7/compact.model.txt`
    - root slice remains `reachable=32 frontier=1 closed=false`
    - remaining frontier is still only `blk_180060f01`
    - the bad helper-relative import form `stack(slot(arg0+0x0)+0x0)` is gone; the target path is now the correct caller-local form `stack(slot(arg0+0x908)+0x0)`
  - current blocker diagnosis:
    - `0x180060F01` is reached by a real binary prelude direct call from `0x180058CD1`, with continuation entry `0x180058CD6`
    - the current prelude-localization path seeds continuation facts for `blk_180058cd6`, but it does not attach the prelude target `blk_180060f01` into the root slice with predecessor-specific facts
    - `blk_180060f01` therefore still evaluates its dispatch from `slot(NEXT_PC)` without the needed entry stack fact, even though the underlying caller-local stack expression is now correct
  - rejected experiment:
    - suppressing semantically localized prelude targets from root-slice traversal was not sound enough; it reopened multiple `call_target_unlifted` frontiers on compact and was reverted
- Compact follow-up after predecessor-localized prelude-target dispatch recovery:
  - landed a new dispatch-resolution source `prelude_localization` in:
    - `include/omill/Analysis/VirtualModel/Types.h`
    - `lib/Analysis/VirtualModel/Dispatch.cpp`
    - `lib/Passes/VirtualCFGMaterialization.cpp`
  - unresolved dispatch summarization now recognizes when the current handler is itself a lifted prelude target of some predecessor continuation handler and re-specializes the target expression through `computeEntryPreludeCallOutgoingFacts(...)`
  - added focused regressions:
    - `VirtualMachineModelTest.ResolvesPreludeTargetDispatchFromPredecessorLocalizedFacts`
    - `VirtualCFGMaterializationTest.MaterializesPreludeTargetDispatchFromPredecessorLocalizedFacts`
  - validation:
    - direct `gtest` execution of the prelude-localization regressions stayed green
    - broader focused VM/pipeline regressions also stayed green, including:
      - `VirtualMachineModelTest.RemapsHelperRelativeVmStackFactsIntoCallerLocalNextPc`
      - `VirtualMachineModelTest.AddsPreludeDirectCallTargetAsRootSliceFrontier`
      - `VirtualMachineModelTest.SeedsMidBlockEntryFromPreludeDirectCallReturnFacts`
      - `PipelineTest.NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers`
  - compact impact before pipeline follow-up:
    - with `OMILL_SKIP_NOABI_POST_CLEANUP_MATERIALIZATION=1`, the compact rerun artifact `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_preludetarget2_skip95/compact.model.txt` now reports:
      - `root-slice root=0x180001850 reachable=35 frontier=0 closed=true`
      - `blk_180060f01` is present with `dispatches=0`
    - this proved the remaining compact frontier was closed semantically by the new prelude-target localization and that the regression had moved to the late no-ABI cleanup pipeline instead
- No-ABI late-pipeline follow-up after the compact prelude-target closure:
  - added a phase-3.95 work gate in `lib/Pipeline.cpp`:
    - `NoAbiPostCleanupMaterializationPass` now runs only when a closed-root-slice-scoped module still has real post-cleanup materialization work
    - the gate only considers:
      - direct calls to `__omill_dispatch_call` / `__omill_dispatch_jump` in closed-slice reachable functions
      - declared synthetic `blk_*` / `block_*` continuation calls in closed-slice reachable functions
  - this prevents the late no-ABI post-cleanup materialization pass from reopening an already closed compact slice just because the module still carries the closed-slice scope metadata
  - compact rerun artifact after the gate:
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_preludetarget3/compact.model.txt`
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_preludetarget3/compact.ll`
  - compact result:
    - `root-slice root=0x180001850 reachable=35 frontier=0 closed=true`
    - `blk_180060f01` remains in-slice and now has `dispatches=0`
    - the emitted no-ABI IR contains:
      - zero `__omill_dispatch_call`
      - zero `__omill_dispatch_jump`
      - zero declared `blk_*`
      - one remaining internal defined helper block `blk_180064933`, reached only by direct internal calls
    - `llc -filetype=obj -O2` succeeds on the emitted compact IR
  - current interpretation:
    - the compact root is semantically closed again in no-ABI mode
    - the remaining `blk_180064933` calls are readability / cleanup leftovers, not a live generic-static-devirtualization frontier
    - the next devirtualization work item should move back to `CorpusVMP.default.dll` stability or to no-ABI readability cleanup of already-closed internal `blk_*` helpers, not more compact target recovery for `blk_180060f01`
- Default follow-up after prelude-target root-slice suppression and late-rerun triage:
  - landed a root-slice classification fix in `lib/Analysis/VirtualModel/RootSlices.cpp`:
    - executable/decodable prelude or callsite targets no longer stay as `call_target_unlifted` frontiers when the current handler already semantically localizes that edge through caller-visible `RETURN_PC` state and code-bearing direct callees
  - added focused regression coverage in `tests/unit/VirtualMachineModelTest.cpp`:
    - `SkipsPreludeDirectCallFrontierWhenSemanticallyLocalized`
    - updated the undecodable-prelude frontier expectation to accept the current nearby-entry recovery classification
  - validation:
    - focused prelude regressions stayed green:
      - `AddsPreludeDirectCallTargetAsRootSliceFrontier`
      - `SkipsPreludeDirectCallFrontierWhenSemanticallyLocalized`
      - `MarksUndecodablePreludeDirectCallTargetAsRootSliceFrontier`
      - `SeedsMidBlockEntryFromPreludeDirectCallReturnFacts`
      - `ResolvesPreludeTargetDispatchFromPredecessorLocalizedFacts`
  - corpus rerun findings:
    - `CorpusVMP.default.dll` now reaches a closed root slice semantically:
      - artifact: `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_default_frontierfix7/default.model.txt`
      - result: `root-slice root=0x180001850 reachable=1 frontier=0 closed=true`
    - `CorpusVMP.compact.dll` stays closed on the same tree:
      - artifact: `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_compact_frontierfix7/compact.model.txt`
      - result: `root-slice root=0x180001850 reachable=31 frontier=0 closed=true`
  - no-ABI late-rerun stability fix:
    - isolated the remaining `default` driver crash to `rerunLateContinuationPipeline()` in `tools/omill-lift/main.cpp`
    - verified that both `default` and `compact` still close cleanly with `OMILL_SKIP_LATE_CONTINUATION_RERUN=1`
    - changed the no-ABI late continuation rerun to be opt-in via `OMILL_ENABLE_NOABI_LATE_CONTINUATION_RERUN`
    - rationale:
      - the current generic path already closes these corpus roots before that rerun
      - reopening the graph there was destabilizing `default` and not improving closure on either sample
  - fresh no-ABI output artifacts after the driver fix:
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_default_frontierfix7/default.ll`
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260321_compact_frontierfix7/compact.ll`
  - fresh no-ABI IR shape:
    - default:
      - `dispatch_call=0`
      - `dispatch_jump=0`
      - `vm_entry=0`
      - `declare_blk=0`
      - `call_blk=4`
      - `missing_block=0`
    - compact:
      - `dispatch_call=0`
      - `dispatch_jump=0`
      - `vm_entry=0`
      - `declare_blk=0`
      - `call_blk=3`
      - `missing_block=0`
    - both fresh `.ll` files compile with `llc -filetype=obj -O2`
  - current interpretation:
    - both corpus roots are semantically closed again in no-ABI mode on this tree
    - the remaining `blk_*` calls in fresh `default` / `compact` no-ABI IR are cleanup/readability leftovers, not live devirtualization frontiers
    - the next useful work item is no-ABI readability cleanup of internal closed-slice `blk_*` helpers, or expanding validation to more roots / samples, not more target-recovery work on these two roots
- No-ABI readability cleanup follow-up:
  - tried a full extra closed-slice cleanup rerun after phase 3.95 and rejected it:
    - it perturbed `default` in the wrong direction by lifting/reintroducing different internal `blk_*` helpers
    - conclusion: the remaining issue is not “run the whole cleanup stack again”, it is “do one more narrow inline-only collapse”
  - landed a narrow final no-ABI inline sweep in `lib/Pipeline.cpp`:
    - after phase 3.95, rerun only:
      - `MarkReachableClosedRootSliceFunctionsPass`
      - `MarkClosedRootSliceHelpersForInliningPass`
      - `RepairBeforeInlinePass`
      - `AlwaysInlinerPass`
      - `GlobalDCEPass`
    - no extra continuation lifting or missing-block lifting is done in this sweep
  - added focused regression coverage in `tests/unit/PipelineTest.cpp`:
    - `ClosedSliceNoAbiCleanupCollapsesInternalBlkChain`
  - validation:
    - focused no-ABI cleanup regressions stayed green:
      - `ClosedSliceNoAbiCleanupCollapsesSingleUseBlkMustTailFallback`
      - `ClosedSliceNoAbiCleanupCollapsesInternalBlkChain`
      - `ClosedSliceNoAbiCleanupKeepsBlkMustTailFallbackWhenDispatchLives`
      - `NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers`
  - fresh artifacts after the narrow inline sweep:
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260322_default_cleanup2/default.model.txt`
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260322_default_cleanup2/default.ll`
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260322_compact_cleanup2/compact.model.txt`
    - `build-remill/test_obf/corpus/lifted/rerun_refactor_20260322_compact_cleanup2/compact.ll`
  - current no-ABI status:
    - `default`:
      - `root-slice root=0x180001850 reachable=1 frontier=0 closed=true`
      - `dispatch_call=0`
      - `dispatch_jump=0`
      - `vm_entry=0`
      - `declare_blk=0`
      - `call_blk=2` (improved from `4`)
      - `missing_block=0`
    - `compact`:
      - `root-slice root=0x180001850 reachable=31 frontier=0 closed=true`
      - `dispatch_call=0`
      - `dispatch_jump=0`
      - `vm_entry=0`
      - `declare_blk=0`
      - `call_blk=3` (unchanged)
      - `missing_block=0`
    - both fresh `.ll` files still compile with `llc -filetype=obj -O2`
  - remaining readability leftovers:
    - `default` now retains only `blk_1801f7733` with `2` direct callsites
    - `compact` retains only `blk_180064933` with `3` direct callsites
  - current interpretation:
    - the generic devirtualization work is done for these two roots; the remaining work is purely late readability shaping
    - the last helpers are not tiny single-use wrappers anymore, so another blanket inline-budget increase is unlikely to be the right next step
    - the next cleanup pass should be a more structural transform for repeated internal closed-slice `blk_*` helpers, not another whole-pipeline rerun
- Fresh no-ABI readability follow-up after the narrow final inline sweep:
  - identified that `default` and `compact` had diverged:
    - replaying the emitted `default.ll` through `omill-opt --block-lift --no-abi-mode` removed the remaining `blk_*` chain
    - replaying the emitted `compact.ll` did not change the remaining `blk_180064933`
  - conclusion:
    - `default` was not missing more VM devirtualization
    - it needed one bounded post-main cleanup replay over already-emitted closed-slice no-ABI IR
    - `compact` still needs a separate structural cleanup for the recursive `blk_180064933` helper
  - landed driver-side replay in `tools/omill-lift/main.cpp`:
    - after `Main pipeline complete`, when all of the following hold:
      - `--no-abi`
      - module flag `omill.closed_root_slice_scope=1`
      - no live `__omill_dispatch_call` / `__omill_dispatch_jump`
      - no live `vm_entry_*`
      - at least one internal defined `blk_*` / `block_*` call remains
    - rerun `buildPipeline` once more with:
      - `generic_static_devirtualize=false`
      - `resolve_indirect_targets=false`
      - `interprocedural_const_prop=false`
      - `deobfuscate=false`
      - `recover_abi=false`
      - `use_block_lifting=false`
      - `no_abi_mode=true`
      - `preserve_lifted_semantics=false`
    - added skip knob:
      - `OMILL_SKIP_NOABI_POST_MAIN_CLEANUP_REPLAY`
  - tightened phase 3.97 in `lib/Pipeline.cpp`:
    - final no-ABI sweep now reruns:
      - `RelaxClosedSliceMustTailMissingBlockPass`
      - helper marking / `AlwaysInliner`
      - `CollapseSyntheticBlockContinuationCallsPass(rewrite_to_missing_block=true, only_when_noabi_mode=true)`
      - `RewriteConstantMissingBlockCallsPass(only_when_noabi_mode=true)`
      - `GlobalDCE`
  - added focused regression coverage in `tests/unit/PipelineTest.cpp`:
    - `ClosedSliceNoAbiCleanupCollapsesRepeatedBlkMustTailFallback`
  - validation:
    - focused cleanup regressions stayed green:
      - `ClosedSliceNoAbiCleanupCollapsesSingleUseBlkMustTailFallback`
      - `ClosedSliceNoAbiCleanupCollapsesRepeatedBlkMustTailFallback`
      - `ClosedSliceNoAbiCleanupCollapsesInternalBlkChain`
      - `ClosedSliceNoAbiCleanupKeepsBlkMustTailFallbackWhenDispatchLives`
      - `NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers`
  - fresh binary-backed reruns:
    - `default`:
      - model: `build-remill/test_obf/corpus/lifted/default_cleanup_fix5/default.model.txt`
      - IR: `build-remill/test_obf/corpus/lifted/default_cleanup_fix5/default.ll`
      - result:
        - `root-slice root=0x180001850 reachable=1 frontier=0 closed=true`
        - `dispatch_call=0`
        - `dispatch_jump=0`
        - `vm_entry=0`
        - `declare_blk=0`
        - `call_blk=0`
        - `missing_block_handler=2`
      - interpretation:
        - the last repeated internal `blk_1801f7733` chain is gone in fresh no-ABI output
        - the root now ends in explicit terminal boundary handlers only
    - `compact`:
      - model: `build-remill/test_obf/corpus/lifted/compact_cleanup_fix5/compact.model.txt`
      - IR: `build-remill/test_obf/corpus/lifted/compact_cleanup_fix5/compact.ll`
      - result:
        - `root-slice root=0x180001850 reachable=31 frontier=0 closed=true`
        - `dispatch_call=0`
        - `dispatch_jump=0`
        - `vm_entry=0`
        - `declare_blk=0`
        - `call_blk=3`
        - `missing_block_handler=0`
      - interpretation:
        - the new replay does not perturb compact semantics
        - the remaining no-ABI cleanup issue is still only the recursive internal helper `blk_180064933`
  - codegen verification:
    - both fresh artifacts still compile with `llc -filetype=obj -O2`
  - next cleanup target:
    - implement a structural transform for closed-slice self-recursive internal `blk_*` helpers
    - most likely direction:
      - recognize terminal self-recursive call patterns in `blk_*`
      - rewrite them into local loops / non-recursive block chains before the final inline sweep

- Closed-slice self-recursive `blk_*` cleanup landed in `Pipeline.cpp`:
  - added `LoopifyClosedSliceSelfRecursiveBlockHelpersPass`
  - scope:
    - closed-root-slice modules only
    - no-ABI mode only
    - internal synthetic `blk_*` / `block_*` helpers only
  - transform:
    - split helper entry after allocas
    - recognize terminal self-recursive calls that reuse the original state and
      memory arguments and a stable program-counter argument
    - rewrite those recursive tail sites into backedges to the post-alloca loop
      header
    - remove unreachable blocks after the rewrite
  - scheduling:
    - phase 3.9 closed-slice cleanup
    - phase 3.97 final closed-slice collapse sweep
  - diagnostics:
    - `OMILL_DEBUG_SELFREC_LOOPIFY=1` prints transform/skip reasons
    - `OMILL_DEBUG_SELFREC_LOOPIFY_DUMP=1` additionally dumps the transformed helper
  - focused regression added in `tests/unit/PipelineTest.cpp`:
    - `ClosedSliceNoAbiCleanupLoopifiesSelfRecursiveBlkHelper`
  - validation:
    - focused no-ABI cleanup regressions are green:
      - `ClosedSliceNoAbiCleanupLoopifiesSelfRecursiveBlkHelper`
      - `ClosedSliceNoAbiCleanupCollapsesRepeatedBlkMustTailFallback`
      - `ClosedSliceNoAbiCleanupCollapsesInternalBlkChain`
      - `ClosedSliceNoAbiCleanupKeepsBlkMustTailFallbackWhenDispatchLives`
  - fresh binary-backed no-ABI reruns:
    - `compact`:
      - model: `build-remill/test_obf/corpus/lifted/compact_cleanup_fix6/compact.model.txt`
      - IR: `build-remill/test_obf/corpus/lifted/compact_cleanup_fix6/compact.ll`
      - result:
        - `root-slice root=0x180001850 reachable=31 frontier=0 closed=true`
        - `dispatch_call=0`
        - `dispatch_jump=0`
        - `vm_entry=0`
        - `declare_blk=0`
        - `define_blk=0`
        - `call_blk=0`
        - `missing_block_handler=0`
      - interpretation:
        - the remaining recursive helper `blk_180064933` is gone from fresh no-ABI output
        - compact no longer retains any synthetic block helpers in the emitted root slice
    - `default`:
      - model: `build-remill/test_obf/corpus/lifted/default_cleanup_fix6/default.model.txt`
      - IR: `build-remill/test_obf/corpus/lifted/default_cleanup_fix6/default.ll`
      - result:
        - `root-slice root=0x180001850 reachable=1 frontier=0 closed=true`
        - `dispatch_call=0`
        - `dispatch_jump=0`
        - `vm_entry=0`
        - `declare_blk=0`
        - `define_blk=0`
        - `call_blk=0`
        - `missing_block_handler=2`
      - interpretation:
        - no regression from the self-recursive helper cleanup
        - default remains on the same clean no-ABI shape as before
  - codegen verification:
    - both fresh artifacts compile with `llc -filetype=obj -O2`
  - export-level semantic verification after the self-recursive cleanup:
    - validated directly against the original corpus DLL exports:
      - `Corpus.dll`
      - `CorpusVMP.compact.dll`
      - `CorpusVMP.default.dll`
    - used the real binary ABI:
      - `TvmpGetAbiVersion() -> u32`
      - `TvmpGetCorpusDescriptor(CorpusDescriptor*)`
      - `TvmpGroundTruthDigest() -> u64`
      - `TvmpRunDigestScenario(void *out_48_bytes) -> u64`
    - result:
      - all three returned:
        - `abi=1`
        - descriptor `(abi=1, exports=9, flags=31)`
        - `ground_truth_digest=13920182619479303470`
        - `scenario_digest=13920182619479303470`
        - identical `48`-byte scenario output:
          - `febbfc32df06af0fd0f43c96afc31555aed1783211b1d697f1c7c692534a57546cf5b57f801b95a02e65a112576c2ec1`
    - interpretation:
      - the self-recursive compact cleanup changed IR shape only
      - the protected compact/default corpora still match the unprotected baseline behavior
  - follow-up triage on the remaining default no-ABI terminal boundary:
    - fresh default no-ABI output now has one live `__omill_missing_block_handler`
      callsite in `default_cleanup_fix6/default.ll`
    - that target is `0x1801F77DD`
    - binary inspection around:
      - `0x1801F77D7`
      - `0x1801F77DD`
      - nearby earlier candidates such as `0x18036A6B9`, `0x1802181F4`,
        `0x180371172`
      does not show a clean decodable function entry or obvious block boundary;
      the bytes are consistent with mid-block / data-like / non-recoverable
      continuation targets rather than a missed normal lifted target
    - interpretation:
      - the next useful change for `default` is probably better explicit
        terminal-boundary classification/reporting, not more aggressive lifting

- 2026-03-22: plain Corpus ABI cleanup for ordinary output roots
  - scope:
    - stop treating the non-VM `Corpus.dll` root as a preserved lifted call
      boundary once a `_native` wrapper exists
    - reuse the post-ABI inline/cleanup machinery for ordinary `omill.output_root`
      helper chains, not only closed root slices
  - landed:
    - `EliminateStateStructPass` now preserves the lifted boundary only for
      VM-oriented output roots (`vm_wrapper` / handler-like traced roots), while
      ordinary plain output roots become `AlwaysInline`
    - added generic output-root native-helper and semantic-helper inline
      marking in the ABI post-inline cleanup path
    - added neutralization of inlined `__remill_function_return` calls after
      helper inlining so native wrappers do not keep dead state/return
      scaffolding
  - focused regressions added/updated:
    - `EliminateStateStructTest.PlainOutputRootBecomesAlwaysInline`
    - `EliminateStateStructTest.VmOutputRootStaysNoInlineBoundary`
    - `PipelineTest.AbiPipelineRemovesOutputRootNativeBlockChain`
    - `PipelineTest.AbiPipelineNeutralizesInlinedFunctionReturnsInOutputRootHelpers`
  - validation:
    - focused `EliminateStateStructTest.*`, `LowerFunctionReturnTest.*`,
      `LowerRemillIntrinsicsTest.*`, and the new `PipelineTest.*` regressions
      pass
  - binary-backed result on `Corpus.dll --va 0x180001850 --block-lift --generic-static-devirtualize`:
    - fresh artifact:
      - `build-remill/test_obf/corpus/lifted/corpus_cleanup_probe7/Corpus.va180001850.abi.ll`
    - current shape:
      - `dispatch=0`
      - `declare_blk=0`
      - `define_blk=1`
      - `call_blk=3`
      - `alloca_state=0`
      - `remill_read=0`
      - `remill_write=0`
      - `remill_return=0`
      - `missing_block_handler=0`
      - `llc -filetype=obj -O2` succeeds
    - interpretation:
      - the plain non-VM root is now largely cleaned and no longer carries
        lifted-state / Remill scaffolding
      - one shared large helper `blk_180001910_native` still survives as an
        internal aggregate-return helper called three times
      - the next plain-corpus step is to decide whether to inline or
        structurally reclassify that final helper, rather than continuing VM
        devirtualization work on this root
## 2026-03-22: Plain Corpus dead lifted-helper cleanup and replay validation

Status:
- landed

What changed:
- `EliminateStateStructPass` now also internalizes non-output-root lifted helpers without `_native` wrappers.
- closed-slice-scoped modules no longer block that dead-helper internalization case.
- late lift-infrastructure cleanup now internalizes dead lifted helpers before `GlobalDCE`, so replayed ABI artifacts can shed dead lifted remnants even when the ABI-stage internalization did not touch them.

Coverage:
- `EliminateStateStructTest.InternalizesNonOutputLiftedHelpersWithoutNativeWrapper`
- `EliminateStateStructTest.ClosedSliceScopeStillInternalizesDeadLiftedHelpersWithoutWrappers`
- `PipelineTest.AbiCleanupDcesDeadInternalizedLiftedHelpersWithoutNativeWrappers`
- `PipelineTest.LiftInfrastructureCleanupDcesDeadExternalLiftedHelpers`

Replay impact on saved plain `Corpus.dll` ABI artifacts:
- `TvmpSimpleArithmetic`: `remill_read 687 -> 0`, `call_blk 93 -> 5`
- `TvmpRecursiveChecksum`: `remill_read 506 -> 0`, `call_blk 35 -> 3`
- `TvmpBytecodeVm`: unchanged semantically-clean shape, still `define_blk=1`, `call_blk=3`
- `TvmpInterprocPipeline`: no live remill/state residue, still `define_blk=3`, `call_blk=57`
- `TvmpGetAbiVersion`, `TvmpGetCorpusDescriptor`, `TvmpFlattenedStateMachine`: clean
- `TvmpGroundTruthDigest`, `TvmpRunDigestScenario`: still terminal boundary stubs

Conclusion:
- the suspected plain-corpus pipeline issue was real, but narrower than “memory lowering failed”.
- the live plain `_native` code was mostly clean already; the large residual `__remill_read_memory_*` counts came from dead lifted helpers surviving the final artifact.
- after the dead-helper cleanup fix, the remaining plain-corpus work is structural helper collapse (`blk_*_native`), not remill/state elimination.

Follow-up in progress:
- added `LoopifySelfRecursiveNativeBlockHelpersPass` and ABI regression `PipelineTest.AbiPipelineLoopifiesSelfRecursiveNativeBlockHelper`.
- the synthetic regression passes, but replay over the saved plain artifacts has not moved yet, so the remaining helper residue still needs a tighter artifact-backed collapse step.

## 2026-03-22: Plain `TvmpInterprocPipeline` late helper-family blocker

Status:
- investigated; not resolved yet

Current real-artifact state:
- fresh merged plain-corpus output for `Corpus.dll --va 0x180001d70 --block-lift --generic-static-devirtualize` still ends at:
  - `define_blk=2`
  - `call_blk=32`
  - `remill_read=0`
  - `remill_write=0`
  - `remill_return=0`
  - `alloca_state=0`
  - `missing_block_handler=0`
- the surviving family is still:
  - `blk_180001e80_native`
  - `blk_180001e94_native`

What the late diagnostics proved:
- this is no longer a Remill/state-lowering problem
- early ABI cleanup sees and loopifies self-recursive sites in both helpers:
  - `blk_180001e80_native recursive_sites=9`
  - `blk_180001e94_native recursive_sites=8`
- but the final emitted ABI artifact still contains an alternating two-helper call family:
  - `blk_180001e80_native -> blk_180001e94_native` (`8` direct calls)
  - `blk_180001e94_native -> blk_180001e80_native` (`8` direct calls)
- the final late-stage callee sets in the emitted `.ll` are exactly the peer pair; there is no remaining Remill/state residue hidden behind them

Attempted next step:
- added a bounded `CanonicalizeMutualRecursiveNativeBlockHelpersPass` that tries to merge a block-like native helper pair into one canonical helper before the existing self-recursive loopify/inlining cleanup
- kept the synthetic regression scaffold, but it is currently disabled because the canonicalized helper still needs a stable post-inline shape before it can be asserted cleanly

Conclusion:
- the remaining plain-corpus blocker is a late-emitted alternating `blk_*_native` SCC in `TvmpInterprocPipeline`
- the next effective step is not more lowering work; it is to make the pair canonicalization match the actual *late* helper-family shape (or to run an artifact-backed pair collapse after the final inline/repair stage where that pair reappears)

Update after bounded pair canonicalization:
- the late helper-family pass now fires on the real artifact:
  - `blk_180001e80_native + blk_180001e94_native -> blk_180001e80_pair_native`
  - the pair helper then loopifies its `16` self-recursive transition sites
- fresh full plain-corpus export sweep:
  - `build-remill/test_obf/corpus/lifted/corpus_export_refresh_merged_20260322_mutrec1/summary.json`
  - `9/9` exports still lift and compile to objects
  - `TvmpInterprocPipeline` improved from:
    - `define_blk=2`, `call_blk=32`
    - to `define_blk=1`, `call_blk=16`
  - all other plain exports are unchanged semantically/structurally from the prior merged baseline

Current plain-corpus state:
- clean:
  - `TvmpBytecodeVm`
  - `TvmpFlattenedStateMachine`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpRecursiveChecksum`
  - `TvmpSimpleArithmetic`
- terminal boundary stubs only:
  - `TvmpGroundTruthDigest`
  - `TvmpRunDigestScenario`
- remaining structural helper residue:
  - `TvmpInterprocPipeline`: one internal `blk_180001e80_pair_native`, `call_blk=16`

Next plain-corpus cleanup step:
- decide whether that last `blk_180001e80_pair_native` should be:
  - accepted as the final ordinary internal helper for this root, or
  - collapsed further with a dedicated single-helper/root-local structural rewrite

## 2026-03-22: Plain `Corpus.dll` structural helper cleanup is now clean

Status:
- resolved for the non-terminal plain-corpus exports

What changed:
- added late ABI helper-family forcing for large single-caller native block helpers
- the force-inline path is now aware of canonicalized helper-family names such as:
  - `blk_<pc>_pair_native`
- this is intentionally ABI-late and output-root-scoped; it does not reopen the VM/generic devirtualization path

Implementation:
- `Pipeline.cpp`
  - broadened native block-helper classification to include canonicalized `*_pair_native` helpers
  - added `ForceInlineSingleCallerCommonContinuationNativeHelpersPass`
  - scheduled it in the late output-root ABI helper-collapse rounds, after mutual-recursive pair canonicalization becomes visible
- `PipelineTest.cpp`
  - added `PipelineTest.AbiPipelineForceInlinesSingleCallerCommonContinuationNativeHelper`
  - existing self-recursive and mutual-recursive helper-collapse regressions remain green

Focused verification:
- `PipelineTest.AbiPipelineLoopifiesSelfRecursiveNativeBlockHelper`
- `PipelineTest.AbiPipelineCollapsesMultiSiteAggregateSelfRecursiveNativeBlockHelper`
- `PipelineTest.AbiPipelineCanonicalizesMutualRecursiveNativeBlockHelperPair`
- `PipelineTest.AbiPipelineForceInlinesSingleCallerCommonContinuationNativeHelper`
- result: `4/4` passing

Real binary-backed result:
- fresh `Corpus.dll --va 0x180001d70 --block-lift --generic-static-devirtualize`
  - artifact:
    - `build-remill/test_obf/corpus/lifted/interproc_commoncont_inline5/TvmpInterprocPipeline.va180001d70.ll`
  - metrics:
    - `define_blk=0`
    - `call_blk=0`
    - `declare_blk=0`
    - `alloca_state=0`
    - `remill_read=0`
    - `remill_write=0`
    - `remill_return=0`
    - `missing_block=0`
  - object code generation succeeds with `llc -O2`

Fresh full plain-corpus sweep:
- `build-remill/test_obf/corpus/lifted/corpus_export_refresh_merged_20260322_commoncont1/summary.json`
- `9/9` exports lift successfully
- `9/9` emitted `.ll` files compile to objects

Current plain-corpus state:
- fully clean:
  - `TvmpBytecodeVm`
  - `TvmpFlattenedStateMachine`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpSimpleArithmetic`
- terminal-boundary stubs only:
  - `TvmpGroundTruthDigest`
  - `TvmpRunDigestScenario`

Conclusion:
- the remaining plain-corpus issue is no longer generic cleanup or Remill/state lowering
- the plain non-VMP path is clean except for the two explicit terminal-boundary exports
- the next plain-corpus work, if we want complete cleanliness, is to understand or reclassify those boundary-stub roots rather than continuing structural helper cleanup

## 2026-03-23: Fresh plain Corpus.dll sweep on current tree is fully clean

Fresh full plain-corpus sweep on the current merged tree:
- `build-remill/test_obf/corpus/lifted/corpus_export_refresh_current_20260323/summary.json`
- command shape used for each export:
  - `omill-lift.exe Corpus.dll --va <va> --block-lift --deobfuscate -o <out.ll>`
- object codegen verified with:
  - `C:\Program Files\LLVM21\bin\llc.exe -filetype=obj -O2`

Current plain-corpus result:
- `9/9` exports lift successfully
- `9/9` emitted `.ll` files compile to objects
- all `9/9` exports are structurally clean:
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `vm_entry=0`
  - `declare_blk=0`
  - `define_blk=0`
  - `call_blk=0`
  - `remill_read=0`
  - `remill_write=0`
  - `remill_return=0`
  - `alloca_state=0`
  - `missing_block=0`

Exports:
- `TvmpGetAbiVersion`
- `TvmpFlattenedStateMachine`
- `TvmpGetCorpusDescriptor`
- `TvmpGroundTruthDigest`
- `TvmpInterprocPipeline`
- `TvmpRecursiveChecksum`
- `TvmpRunDigestScenario`
- `TvmpSimpleArithmetic`
- `TvmpBytecodeVm`

Conclusion:
- the plain `Corpus.dll` path is no longer the blocker
- the next devirtualization effort should move back to `CorpusVMP.compact.dll` and `CorpusVMP.default.dll`

## 2026-03-23: Fresh VMP ABI root artifacts are clean on the current tree

Issue fixed:
- fresh ABI relifts for `CorpusVMP.default.dll --va 0x180001850` were crashing
  after `Main pipeline complete`
- the crash was in the post-main late continuation driver, not ABI recovery
  itself
- debug logging showed the bad late target:
  - `0x1800b9d57`
  - inside the `.7ir` section
  - decodes as garbage and immediately fails at `0x1800b9d5c`

Root cause:
- the late continuation collector in `tools/omill-lift/main.cpp` accepted
  declaration-only `blk_*` targets blindly
- ABI mode then tried to block-lift bogus continuation PCs that are not valid
  late code roots

Fix:
- filter late continuation candidates through the same bounded
  `looksLikeLateMissingBlockRoot` decodability probe already used for late
  missing-block targets
- this keeps the late rerun from reopening `.7ir` junk while still allowing
  real late continuation roots

Validation:
- rebuilt `omill-lift`
- fresh default ABI relift now succeeds:
  - `build-remill/test_obf/corpus/lifted/vmp_abi_current_20260323_default_fixlate1/default.ll`
  - metrics:
    - `dispatch_call=0`
    - `dispatch_jump=0`
    - `declare_blk=0`
    - `define_blk=0`
    - `call_blk=0`
    - `remill_read=0`
    - `remill_write=0`
    - `remill_return=0`
    - `alloca_state=0`
    - `missing_block=0`
  - `llc -filetype=obj -O2` succeeds
- fresh compact ABI relift still succeeds and stays clean:
  - `build-remill/test_obf/corpus/lifted/vmp_abi_current_20260323_compact_fixlate1/compact.ll`
  - metrics:
    - `dispatch_call=0`
    - `dispatch_jump=0`
    - `declare_blk=0`
    - `define_blk=0`
    - `call_blk=0`
    - `remill_read=0`
    - `remill_write=0`
    - `remill_return=0`
    - `alloca_state=0`
    - `missing_block=0`
  - `llc -filetype=obj -O2` succeeds

Current takeaway:
- plain `Corpus.dll`: clean across all 9 exports
- `CorpusVMP.compact.dll` root `0x180001850`: fresh ABI output clean
- `CorpusVMP.default.dll` root `0x180001850`: fresh ABI output clean
- the next work is no longer this late ABI driver crash

## 2026-03-23: Export-level VMP sweep after late-target and native-loopify fixes

Fresh export sweeps:
- compact:
  - `build-remill/test_obf/corpus/lifted/compact_export_refresh_current_20260323/summary.json`
- default:
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260323_fixloop1/summary.json`

Additional cleanup landed:
- broadened native self-recursive helper loopify to accept
  `call self; [optional asm "int3"]; ret`
- this cleaned `CorpusVMP.default.dll!TvmpInterprocPipeline`

Current export-level state:
- `CorpusVMP.default.dll`
  - clean:
    - `TvmpGetAbiVersion`
    - `TvmpGetCorpusDescriptor`
    - `TvmpGroundTruthDigest`
    - `TvmpInterprocPipeline`
    - `TvmpRecursiveChecksum`
    - `TvmpRunDigestScenario`
    - `TvmpSimpleArithmetic`
    - `TvmpBytecodeVm`
  - remaining residual:
    - `TvmpFlattenedStateMachine`
      - `declare_blk=1`
      - `call_blk=1`
      - `alloca_state=1`
      - no dispatch/vm_entry/remill residue
- `CorpusVMP.compact.dll`
  - clean:
    - `TvmpGetAbiVersion`
    - `TvmpGetCorpusDescriptor`
    - `TvmpGroundTruthDigest`
    - `TvmpInterprocPipeline`
    - `TvmpRecursiveChecksum`
    - `TvmpRunDigestScenario`
    - `TvmpSimpleArithmetic`
    - `TvmpBytecodeVm`
  - remaining residual:
    - `TvmpFlattenedStateMachine`
      - only `missing_block=2`
      - no dispatch/vm_entry/remill residue

Tests / validation:
- focused ABI helper cleanup regressions pass, including:
  - `PipelineTest.AbiPipelineLoopifiesSelfRecursiveNativeBlockHelper`
  - `PipelineTest.AbiPipelineLoopifiesTrapTerminatedSelfRecursiveNativeBlockHelper`
  - `PipelineTest.AbiPipelineCollapsesMultiSiteAggregateSelfRecursiveNativeBlockHelper`
- fresh ABI artifacts for compact/default `TvmpBytecodeVm` compile with
  `llc -filetype=obj -O2`
- all exports in the two new sweep summaries compile to objects

Next target:
- `TvmpFlattenedStateMachine` in compact/default
- default is now down to a single declared `blk_18030f17a` continuation keeping
  one `%struct.State` wrapper alive
- compact is already terminalized to an explicit boundary for the corresponding
  export

## 2026-03-23: Default flattened continuation cleanup on actual export VAs

Targeted fix:
- the remaining `CorpusVMP.default.dll!TvmpFlattenedStateMachine` residue was a
  self-looping output-root tail calling declaration-only `@blk_18030f17a` with
  `ptr poison`
- the late terminal synthetic-block rewrite already recognized the shape, but
  it rejected suffix instructions that were still present before final cleanup:
  - `llvm.lifetime.end`
  - pure arithmetic / `inttoptr`
  - local frame stores built from that suffix-local pointer chain

Implementation:
- kept env-gated diagnostics in `RewriteTerminalSyntheticBlockCallsToMissingBlockHandlerPass`
- broadened loop-suffix matching so terminal self-loop rewriting accepts:
  - pure suffix-local instruction chains
  - stores whose pointer operand is local to the suffix or entry-frame-backed
- added regression:
  - `PipelineTest.AbiPipelineTerminalizesSelfLoopPoisonMemoryBlockContinuationWithDeadPureSuffix`

Targeted validation:
- fresh relift:
  - `build-remill/test_obf/corpus/lifted/default_flattened_fix13.ll`
- metrics:
  - `dispatch_call=0`
  - `dispatch_jump=0`
  - `declare_blk=0`
  - `define_blk=0`
  - `call_blk=0`
  - `alloca_state=0`
  - `remill_read=0`
  - `remill_write=0`
  - `remill_return=0`
  - `missing_block=2`
- `llc -filetype=obj -O2` succeeds

Important correction:
- the earlier default export sweep reused a stale VA list for several exports
- reran the full sweep using the actual DLL export table from
  `llvm-readobj --coff-exports`

Actual-export sweep:
- artifact:
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260323_actual1/summary.json`
- result:
  - all `9/9` exports lift successfully
  - all `9/9` emitted `.ll` files compile with `llc -filetype=obj -O2`

Current `CorpusVMP.default.dll` export state using actual export VAs:
- clean (`dispatch=0`, `blk*=0`, `alloca_state=0`, `missing_block=0`):
  - `TvmpBytecodeVm`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpSimpleArithmetic`
- terminal-boundary-only (`missing_block=2`, all other tracked cleanup metrics `0`):
  - `TvmpFlattenedStateMachine`
  - `TvmpGroundTruthDigest`
  - `TvmpRunDigestScenario`

Takeaway:
- the remaining default export residue is no longer structural
- all remaining non-clean outputs are explicit terminal boundary stubs only

Next:
- rerun the compact export sweep against the actual export table as well
- then decide whether the terminal-boundary-only exports should be treated as
  acceptable final ABI artifacts or need further late boundary recovery

## 2026-03-23: Compact digest-wrapper cleanup after actual export sweep

Context:
- the actual compact export sweep (`compact_export_refresh_current_20260323_actual1`)
  corrected stale VA assumptions
- it showed two additional non-clean exports that were not visible in the old
  cached summary:
  - `TvmpGroundTruthDigest` at `0x180002400`
  - `TvmpRunDigestScenario` at `0x1800023F0`
- both had the same residual shape:
  - `declare_blk=4`
  - `call_blk=4`
  - `alloca_state=4`
  - no dispatch/vm_entry/remill residue

Root cause:
- these were not terminal self-loop tails
- they were isolated declaration-only synthetic `blk_*` calls that consumed
  fresh local wrapper state, had unused returns, and were followed only by
  wrapper teardown
- they should be erased so late DCE/SROA can drop the wrapper scaffolding,
  not rewritten to `__omill_missing_block_handler`

Implementation:
- added `EraseIsolatedSyntheticBlockWrapperCallsPass`
- scheduled it beside late terminal synthetic-block cleanup in ABI recovery
- added focused regression:
  - `PipelineTest.AbiPipelineErasesIsolatedSyntheticBlockWrapperCall`

Targeted validation:
- `TvmpGroundTruthDigest`:
  - artifact:
    - `build-remill/test_obf/corpus/lifted/compact_gtd_fix4.ll`
  - metrics:
    - `declare_blk=0`
    - `define_blk=0`
    - `call_blk=0`
    - `alloca_state=0`
    - `missing_block=0`
    - `remill_read=0`
  - `llc -filetype=obj -O2` succeeds
- `TvmpRunDigestScenario`:
  - artifact:
    - `build-remill/test_obf/corpus/lifted/compact_rds_fix1.ll`
  - metrics:
    - `declare_blk=0`
    - `define_blk=0`
    - `call_blk=0`
    - `alloca_state=0`
    - `missing_block=0`
    - `remill_read=0`
  - `llc -filetype=obj -O2` succeeds

Current compact status after targeted fixes:
- clean:
  - `TvmpBytecodeVm`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpGroundTruthDigest`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpRunDigestScenario`
  - `TvmpSimpleArithmetic`
- terminal-boundary-only:
  - `TvmpFlattenedStateMachine` (`missing_block=2`, all other tracked metrics `0`)

Next:
- rerun the full compact actual-export sweep to refresh the summary on disk
- then decide whether to stop at the compact/default terminal-boundary-only
  exports or pursue more aggressive late boundary recovery for those paths

## 2026-03-23: Compact actual-export sweep refreshed after digest-wrapper cleanup

Refreshed artifact:
- `build-remill/test_obf/corpus/lifted/compact_export_refresh_current_20260323_actual2/summary.json`

Result:
- all `9/9` compact exports lift successfully
- all `9/9` emitted `.ll` files compile with `llc -filetype=obj -O2`

Current `CorpusVMP.compact.dll` export state using actual export VAs:
- clean (`dispatch=0`, `blk*=0`, `alloca_state=0`, `missing_block=0`):
  - `TvmpBytecodeVm`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpGroundTruthDigest`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpRunDigestScenario`
  - `TvmpSimpleArithmetic`
- terminal-boundary-only (`missing_block=2`, all other tracked metrics `0`):
  - `TvmpFlattenedStateMachine`

Takeaway:
- compact is now strictly cleaner than default at export level
- the only remaining compact non-clean export is a terminal boundary stub, not a
  structural cleanup failure

Next:
- decide whether to accept terminal-boundary-only exports as the final ABI
  endpoint for compact/default
- or pursue late boundary recovery specifically for:
  - `CorpusVMP.default.dll`:
    - `TvmpFlattenedStateMachine`
    - `TvmpGroundTruthDigest`
    - `TvmpRunDigestScenario`
  - `CorpusVMP.compact.dll`:
    - `TvmpFlattenedStateMachine`

## 2026-03-23: Remaining terminal-boundary targets are not cheap recovery candidates

Boundary PCs:
- default terminal-boundary-only exports all converge to:
  - `0x18030f17a` in `.7ir`
- compact terminal-boundary-only export converges to:
  - `0x1800233a3` in `.cdS`

Binary-backed evidence:
- `0x18030f17a` disassembles inside `.7ir` and does look like executable code,
  but not a clean ordinary lifted entry
- `0x1800233a3` is inside `.cdS`, also inside the obfuscation section rather
  than `.text`

Standalone recovery probes:
- default:
  - `omill-lift CorpusVMP.default.dll --va 0x18030f17a --block-lift ...`
  - fails with `LLVM ERROR: out of memory`
  - crash occurs in ABI cleanup `AlwaysInlinerPass`
- compact:
  - `omill-lift CorpusVMP.compact.dll --va 0x1800233a3 --block-lift ...`
  - fails with `LLVM ERROR: out of memory`
  - crash occurs in `MergeBlockFunctionsPass`

Takeaway:
- these targets are not “one more late continuation edge” in the ordinary
  sense
- direct standalone lifting of the boundary PCs is currently pathological
- that makes the remaining terminal-boundary-only exports reasonable stopping
  points for the current ABI cleanup pipeline

Practical recommendation:
- treat the current terminal-boundary-only exports as acceptable final ABI
  artifacts for now
- if we want to push further, the next project is not generic cleanup; it is a
  bounded mid-block / obfuscation-section boundary-recovery effort with its own
  budget and guardrails

## 2026-03-23: Explicit terminal-boundary annotation landed; default still has a separate self-loop collapse path

Implemented:
- late ABI terminal-boundary classification in `lib/Pipeline.cpp`
  - surviving `__omill_missing_block_handler(i64 pc)` callsites now carry
    call metadata `!omill.terminal_boundary`
  - the module now emits named metadata `!omill.terminal_boundaries`
  - callers with a single surviving terminal boundary now get:
    - `omill.terminal_boundary_count`
    - `omill.terminal_boundary_kind`
    - `omill.terminal_boundary_target_va`
    - `omill.terminal_boundary_summary`
- focused `PipelineTest` coverage for:
  - explicit terminal-boundary annotation
  - rewriting trivial loopified output-root self-loops to explicit
    `__omill_missing_block_handler`
  - lifted-to-native propagation of terminal-boundary candidate PCs

Validated:
- compact flattened export now carries explicit terminal-boundary reporting in:
  - `build-remill/test_obf/corpus/lifted/terminal_boundary_annotate4/compact_flattened.ll`
- current compact flattened classification is:
  - target `0x1800233a3`
  - kind `in_image_executable_decodable_target`
- `llc -O2` succeeds on the annotated compact artifact

Remaining issue:
- fresh targeted ABI relifts for default:
  - `TvmpFlattenedStateMachine`
  - `TvmpGroundTruthDigest`
  - `TvmpRunDigestScenario`
  still end as trivial self-loops in:
  - `build-remill/test_obf/corpus/lifted/terminal_boundary_annotate4/default_flattened.ll`
  - `build-remill/test_obf/corpus/lifted/terminal_boundary_annotate4/default_groundtruth.ll`
  - `build-remill/test_obf/corpus/lifted/terminal_boundary_annotate4/default_rundigest.ll`
- those outputs have:
  - no `__omill_missing_block_handler`
  - no terminal-boundary attrs/metadata
  - only the minimal `entry -> selfrec.loop -> selfrec.loop` shape

Conclusion:
- terminal-boundary reporting is solved for the explicit-handler endpoint
- compact uses that endpoint correctly
- default still has one remaining late output-root collapse path that bypasses
  the explicit-handler form entirely

Next step:
- trace the exact late ABI pass that transforms the default terminal wrapper
  from `before_abi.ll`'s `musttail call @blk_18030f17a` shape into the final
  trivial self-loop, then either:
  - stop that rewrite for output roots, or
  - carry explicit target provenance through that rewrite so the final
    terminal-boundary pass can recover the handler call

## 2026-03-23: Post-ABI terminal boundary rewrite now runs in the real final output path

Status:
- landed a final-output-path terminal-boundary rewrite rerun in
  `buildLateCleanupPipeline`
- widened candidate propagation so the native root keeps
  `omill.terminal_boundary_candidate_pc` through the early ABI inline path
- added focused regressions for:
  - unique-callee candidate propagation before inlining
  - lifted-to-native candidate propagation before inlining
  - late cleanup rewriting a candidate-tagged trivial self-loop output root

Root cause:
- `buildABIRecoveryPipeline` was not the last stage touching terminal wrappers
- post-ABI deobfuscation could recreate a trivial `entry -> selfrec.loop ->
  selfrec.loop` output root after the ABI-local rewrite already ran
- the target PC was preserved on the root as
  `omill.terminal_boundary_candidate_pc`, but the final emitted module did not
  rerun `RewriteLoopifiedTerminalBoundaryOutputRootsPass`

Validated on real default exports:
- `TvmpGroundTruthDigest` (`0x180002400`) now emits:
  - explicit `call void @__omill_missing_block_handler(i64 6445658490)`
  - terminal-boundary attrs:
    - `omill.terminal_boundary_candidate_pc="18030F17A"`
    - `omill.terminal_boundary_kind="in_image_executable_decodable_target"`
  - object code generation succeeds with `llc -filetype=obj -O2`
- `TvmpRunDigestScenario` (`0x1800023F0`) now emits the same explicit terminal
  boundary form and compiles
- `TvmpFlattenedStateMachine` (`0x1800020E0`) now emits the same explicit
  terminal boundary form and compiles

Diagnostic evidence:
- with `OMILL_DEBUG_TERMINAL_REWRITE=1`, the real driver now shows:
  - ABI recovery pass: `skip ... no-trivial-loop-block`
  - post-ABI late cleanup: `rewrite sub_180002400_native target=0x18030F17A`

Current state:
- the remaining default terminal exports are no longer opaque self-loops
- they are explicit classified terminal-boundary outputs in the same style as
  compact

Next step:
- rerun the actual default export sweep and refresh the on-disk summary so the
  export-level report reflects the new explicit terminal-boundary outputs

## 2026-03-23: Default actual export sweep refreshed after final late-cleanup terminal rewrite

Artifacts:
- summary:
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260323_actual2/summary.json`
- targeted terminal-boundary outputs:
  - `build-remill/test_obf/corpus/lifted/default_terminal_fix1/TvmpGroundTruthDigest.va180002400.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_fix1/TvmpRunDigestScenario.va1800023F0.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_fix1/TvmpFlattenedStateMachine.va1800020E0.ll`

Current default export state:
- clean:
  - `TvmpBytecodeVm`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpSimpleArithmetic`
- explicit terminal-boundary outputs:
  - `TvmpFlattenedStateMachine`
  - `TvmpGroundTruthDigest`
  - `TvmpRunDigestScenario`

Important clarification:
- the summary still shows `missing_block=2` on those three exports because the
  metric counts both:
  - the `declare @__omill_missing_block_handler`
  - the live terminal callsite
- the old failure mode was a trivial self-loop with no explicit terminal
  boundary call; that is gone now

Validation:
- all 9 default exports relift successfully
- all 9 emitted `.ll` files compile with `llc -filetype=obj -O2`
- the three former self-loop outputs now carry:
  - explicit `__omill_missing_block_handler(...)`
  - `omill.terminal_boundary_*` attrs/metadata

Next step:
- rerun the compact actual export sweep with the current tree so the export
  report is refreshed uniformly across both VMP variants

## 2026-03-23: Compact actual export sweep refreshed after final late-cleanup rewrite

Artifact:
- summary:
  - `build-remill/test_obf/corpus/lifted/compact_export_refresh_current_20260323_actual3/summary.json`

Current compact export state:
- clean:
  - `TvmpBytecodeVm`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpGroundTruthDigest`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpRunDigestScenario`
  - `TvmpSimpleArithmetic`
- explicit terminal-boundary output:
  - `TvmpFlattenedStateMachine`

Validation:
- all 9 compact exports relift successfully
- all 9 emitted `.ll` files compile with `llc -filetype=obj -O2`
- compact remains better than default on the digest exports:
  - `TvmpGroundTruthDigest` and `TvmpRunDigestScenario` are fully clean
  - only `TvmpFlattenedStateMachine` remains terminal-boundary-only

Current export-level endpoint:
- plain `Corpus.dll`:
  - 7 clean
  - 2 explicit terminal-boundary outputs
- `CorpusVMP.default.dll`:
  - 6 clean
  - 3 explicit terminal-boundary outputs
- `CorpusVMP.compact.dll`:
  - 8 clean
  - 1 explicit terminal-boundary output

Next step:
- decide whether terminal-boundary-only exports are the accepted ABI endpoint,
  or start a separate bounded recovery effort for those remaining in-image
  decodable boundary targets

## 2026-03-23: Remaining terminal-boundary targets are not cheap direct-lift recoveries

Shared remaining targets:
- default terminal-boundary exports all converge on one target:
  - `0x18030F17A`
- compact terminal-boundary export converges on:
  - `0x1800233A3`

Probe results:
- direct lift probe of default target `0x18030F17A`:
  - artifact/log:
    - `build-remill/test_obf/corpus/lifted/terminal_target_probe2/default_18030F17A.log`
  - result:
    - still fails with `LLVM ERROR: out of memory`
    - crash remains in `AlwaysInlinerPass`
- direct lift probe of compact target `0x1800233A3`:
  - artifact/log:
    - `build-remill/test_obf/corpus/lifted/terminal_target_probe2/compact_1800233A3.log`
  - result:
    - does not finish within a 20-minute bound
    - stalls after `Generic static devirtualization enabled`
    - never reaches ABI recovery

Conclusion:
- the remaining explicit terminal-boundary exports are not one cheap relift away
- recovering them is a separate bounded effort around:
  - inline-budget control / selective inline suppression for target roots
  - or a dedicated mid-block / continuation-root recovery strategy

Current practical endpoint:
- explicit classified terminal-boundary output is the stable ABI endpoint for
  these remaining exports on the current tree

## 2026-03-23: Added a coherent global AlwaysInliner skip knob for bounded target-root probes

What landed:
- all remaining `AlwaysInlinerPass` insertion sites now respect:
  - `OMILL_SKIP_ALWAYS_INLINE=1`
- ABI-specific sites still additionally respect:
  - `OMILL_SKIP_ABI_ALWAYS_INLINE=1`

Validation:
- unit regression:
  - `PipelineTest.GlobalAlwaysInlineSkipSuppressesAlwaysInlinerPasses`
- existing terminal-boundary regressions remain green:
  - `PipelineTest.AbiPipelinePropagatesLiftedTerminalBoundaryCandidateBeforeInlining`
  - `PipelineTest.LateCleanupRewritesTerminalBoundaryOutputRootFromCandidateAttr`

Probe impact:
- probing default target `0x18030F17A` with only
  `OMILL_SKIP_ABI_ALWAYS_INLINE=1` still crashed in `AlwaysInlinerPass`
  because non-ABI inliner sites were still active
- probing the same target with `OMILL_SKIP_ALWAYS_INLINE=1` now bypasses
  `AlwaysInlinerPass`, but the target still crashes later in the pipeline
  before producing output:
  - `build-remill/test_obf/corpus/lifted/terminal_target_probe4/default_18030F17A.skipallinline.log`

Conclusion:
- inline suppression alone is not enough to recover the shared default
  terminal target
- but we now have a reliable global control for isolating later-pass failures

## 2026-03-23: Auto-skip generic static devirtualization for non-VM target-root probes

What landed:
- added `moduleHasGenericStaticDevirtualizationCandidates(const Module &)` in
  `include/omill/Omill.h` / `lib/Pipeline.cpp`
- tightened the predicate to actual VM/boundary signals only:
  - `omill.vm_handler`
  - `omill.vm_wrapper`
  - `omill.protection_boundary`
  - `omill.boundary_kind`
  - `omill.trace_native_target`
  - `omill.vm_newly_lifted`
  - `omill.newly_lifted`
  - `omill.virtual_specialized`
  - `omill.vm_demerged_clone`
  - `omill.vm_outlined_virtual_call`
  - `vm_entry_*`
- driver now auto-disables `generic_static_devirtualize` when the user enabled
  it but the lifted module has no VM-like candidates, unless:
  - VM mode is active
  - or `OMILL_FORCE_GENERIC_STATIC_DEVIRT=1` is set

Validation:
- `PipelineTest.GenericStaticDevirtualizationCandidateDetectionIgnoresPlainLiftedRoot`
- `PipelineTest.GenericStaticDevirtualizationCandidateDetectionFindsVmHandlerAttr`

Real target-root impact:
- default shared terminal target `0x18030F17A`:
  - standalone probe with `--generic-static-devirtualize` now auto-skips GSD
    and completes successfully:
    - `build-remill/test_obf/corpus/lifted/terminal_target_probe8/default_18030F17A.auto_skip_gsd.log`
    - emitted IR compiles with `llc -O2`
    - emitted IR has:
      - `dispatch_call=0`
      - `dispatch_jump=0`
      - `declare_blk=0`
      - `call_blk=0`
      - `__omill_missing_block_handler=0`
      - `__remill_read_memory_=0`
      - `__remill_write_memory_=0`
      - `%struct.State=0`
- compact remaining terminal target `0x1800233A3`:
  - standalone probe now also auto-skips GSD:
    - `build-remill/test_obf/corpus/lifted/terminal_target_probe9/compact_1800233A3.auto_skip_gsd.log`
  - but it still fails later during ABI recovery with:
    - `Running pass "cgscc(inline<only-mandatory>,inline),cgscc()"`
  - `OMILL_SKIP_POST_ABI_INLINE=1` did not change that:
    - `build-remill/test_obf/corpus/lifted/terminal_target_probe10/compact_1800233A3.skip_post_abi_inline.log`

Conclusion:
- the old “remaining terminal targets are not cheap direct-lift recoveries”
  result needs to be split:
  - default `0x18030F17A` is now a clean standalone lift once generic VM
    devirtualization is not forced onto it
  - compact `0x1800233A3` is still blocked, but now the blocker is clearly a
    later ABI CGSCC inliner path rather than generic static devirtualization

## 2026-03-23: Default terminal-boundary exports now reduce to one raw constant call target each

What landed:
- added a bounded pre-ABI late terminal-boundary target relift in
  `tools/omill-lift/main.cpp`
- it scans output roots for constant `__remill_missing_block` targets that
  look like real code roots, lifts a small bounded set, and rewrites those
  call sites to direct lifted targets before ABI recovery
- also added an experimental post-ABI output-root constant-target wave, but it
  is currently opt-in only:
  - `OMILL_ENABLE_LATE_OUTPUT_ROOT_TARGET_RERUN=1`
  - default path keeps it disabled because the current version is not yet
    default-safe

Stable default-export impact:
- the three previously terminal-boundary-only default exports no longer end in
  explicit `__omill_missing_block_handler(...)`
- they now end in a single raw constant `inttoptr` call each, with no VM/state
  residue:
  - `TvmpGroundTruthDigest` -> `0x18024014A`
  - `TvmpRunDigestScenario` -> `0x18024014A`
  - `TvmpFlattenedStateMachine` -> `0x1801311A7`
- representative artifacts:
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover1/TvmpGroundTruthDigest.va180002400.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover1/TvmpRunDigestScenario.va1800023F0.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover1/TvmpFlattenedStateMachine.va1800020E0.ll`

Shape of those artifacts:
- `__omill_missing_block_handler=0`
- `declare_blk=0`
- `call_blk=0`
- `%struct.State=0`
- exactly one `inttoptr(i64 ...)` call remains in each

Bounded probe result for the next default target:
- `0x18024014A` is not a hard stop:
  - direct probe with `OMILL_SKIP_ALWAYS_INLINE=1` completes:
    - `build-remill/test_obf/corpus/lifted/target_probe_18024014a_skip1/target.log`
- so the remaining default work is now best described as:
  - iterative output-root constant-call-target recovery
  - not terminal-boundary classification anymore

Current practical split:
- default:
  - terminal-boundary stubs are improved into a smaller “one constant call
    target left” frontier
- compact:
  - remaining blocked target is still the ABI inliner path on `0x1800233A3`

## 2026-03-23: Experimental post-ABI output-root target wave is not default-safe yet

What landed:
- the post-ABI output-root constant-target wave remains available, but it is
  now explicitly opt-in:
  - `OMILL_ENABLE_LATE_OUTPUT_ROOT_TARGET_RERUN=1`
- it also uses a scoped `OMILL_SKIP_ALWAYS_INLINE=1` override for the bounded
  rerun, so experiments do not inherit the global ABI inliner

What the debug run proved:
- target:
  - `CorpusVMP.default.dll!TvmpGroundTruthDigest`
- artifact/log:
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover_debug5/TvmpGroundTruthDigest.va180002400.log`
- the experimental wave gets as far as:
  - `Post-ABI deobfuscation complete`
  - `[late-output-target] round=1 collect`
  - `[late-output-target] round=1 targets= 0x18024014a`
  - `[late-output-target] round=1 lift+rerun`
- and then crashes before:
  - the scoped main rerun starts
  - the scoped ABI rerun starts

Meaning:
- the current failure is in the same-module target lift itself
- it is not in:
  - the late scoped main pipeline
  - the late scoped ABI replay
  - or the final inttoptr patch step

Implication:
- the next default recovery step is probably not “one more in-place late lift”
- it is more likely:
  - side-module target recovery plus import/rewrite
  - or a more isolated target-lift path than reusing the current live module

## 2026-03-23: Rewrite unresolved output-root constant-call loops into explicit terminal boundaries

What landed:
- added a late cleanup rewrite in:
  - `lib/Pipeline.cpp`
- it handles output roots that collapse to:
  - a terminal self-recursive loop
  - with a unique constant `inttoptr(i64 ...)` call target
- those roots are now rewritten to explicit:
  - `__omill_missing_block_handler(target_pc)`
- the rewrite also seeds:
  - `omill.terminal_boundary_candidate_pc`
- the existing annotation pass then restores classified terminal-boundary attrs
  and named metadata on the final output root

Regression coverage:
- `PipelineTest.LateCleanupRewritesIndirectCallTerminalBoundaryOutputRoot`

Validated real default exports:
- artifacts:
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover2/TvmpGroundTruthDigest.va180002400.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover2/TvmpRunDigestScenario.va1800023F0.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_recover2/TvmpFlattenedStateMachine.va1800020E0.ll`
- all three now emit:
  - `__omill_missing_block_handler(...)`
  - `omill.terminal_boundary_kind`
  - `omill.terminal_boundary_target_va`
  - `!omill.terminal_boundaries`
- no raw constant `inttoptr` calls remain in those final artifacts
- all three compile with:
  - `llc -filetype=obj -O2`

Current practical endpoint:
- default terminal exports are explicit classified terminal-boundary outputs
  again, not opaque raw constant-call wrappers
- the remaining deeper recovery work, if resumed, should start from:
  - a side-module / isolated-target path
  - not another same-module late-lift wave

## 2026-03-23: Global inline skip now suppresses the regular module inliner too

What landed:
- `OMILL_SKIP_ALWAYS_INLINE=1` now suppresses:
  - `AlwaysInlinerPass`
  - `ModuleInlinerWrapperPass`
- implementation is in:
  - `lib/Pipeline.cpp`
- regression coverage:
  - `PipelineTest.GlobalAlwaysInlineSkipSuppressesAlwaysInlinerPasses`

Compact impact:
- the standalone compact terminal target probe no longer OOMs in
  `cgscc(inline<only-mandatory>,inline)` under `OMILL_SKIP_ALWAYS_INLINE=1`
- probe artifact:
  - `build-remill/test_obf/corpus/lifted/terminal_target_probe11/compact_1800233A3.skipallinline.ll`
- that artifact compiles with:
  - `llc -filetype=obj -O2`

What it means:
- the remaining compact isolated-target blocker is no longer the inliner crash
- but the emitted artifact is still a large stateful/block-lifted wrapper graph
  rooted at:
  - `sub_1800233a3_native`
- it still carries many internal `blk_*` helpers and `%struct.State`
- the isolated-target path is now viable as a probe, but it is not yet a clean
  importable recovery artifact
## 2026-03-23: Restore compact terminal-boundary cleanup after auto-GSD skip

Status:
- landed

What changed:
- `Pipeline.cpp`
  - added `RewriteStateWrapperTerminalBoundaryOutputRootsPass`
  - this rewrites output roots that are still a trivial `_native` state wrapper
    around a same-base lifted `sub_*` call, when
    `omill.terminal_boundary_candidate_pc` is already present
  - generalized the terminal-boundary root rewrite into shared helpers:
    - `getTerminalBoundaryCandidatePc`
    - `rewriteTerminalBoundaryOutputRoot`
  - widened `moduleHasGenericStaticDevirtualizationCandidates` so a module with
    a real output root plus defined `blk_*` / `block_*` helpers still counts as
    a generic-static-devirt candidate
- `PipelineTest.cpp`
  - added `LateCleanupRewritesStateWrapperTerminalBoundaryOutputRoot`
  - added `GenericStaticDevirtualizationCandidateDetectionFindsBlockLiftedHelper`

Why:
- the auto-skip for generic static devirtualization on non-VM roots was too
  aggressive for `CorpusVMP.compact.dll!TvmpFlattenedStateMachine`
- before this fix, direct relift of `0x1800020E0` skipped GSD and collapsed to
  an empty final module after a block-lifter decode failure at `0x180002141`
- the old stable artifact showed that this path still needs the bounded GSD /
  terminal-boundary cleanup flow even though it does not expose explicit
  `omill.vm_handler`-style attrs early

Validation:
- focused tests:
  - `LateCleanupRewritesTerminalBoundaryOutputRootFromCandidateAttr`
  - `LateCleanupRewritesIndirectCallTerminalBoundaryOutputRoot`
  - `LateCleanupRewritesStateWrapperTerminalBoundaryOutputRoot`
  - `GlobalAlwaysInlineSkipSuppressesAlwaysInlinerPasses`
  - `GenericStaticDevirtualizationCandidateDetectionIgnoresPlainLiftedRoot`
  - `GenericStaticDevirtualizationCandidateDetectionFindsVmHandlerAttr`
- compact isolated target probe:
  - `terminal_target_probe12/compact_1800233A3.skipallinline.ll`
  - now reduces to explicit:
    - `__omill_missing_block_handler(0x1800420C8)`
    - with terminal-boundary attrs / metadata
    - and compiles with `llc -O2`
- compact flattened rerun:
  - `compact_flattened_fix_terminalwrapper2/compact_flattened.ll`
  - now again reduces to explicit:
    - `__omill_missing_block_handler(0x1800233A3)`
    - with terminal-boundary attrs / metadata
    - and compiles with `llc -O2`
- refreshed compact actual export sweep:
  - `compact_export_refresh_current_20260323_actual4/summary.json`
  - result remains:
    - 8 clean exports
    - 1 explicit terminal-boundary export (`TvmpFlattenedStateMachine`)

Current compact endpoint:
- clean:
  - `TvmpBytecodeVm`
  - `TvmpGetAbiVersion`
  - `TvmpGetCorpusDescriptor`
  - `TvmpGroundTruthDigest`
  - `TvmpInterprocPipeline`
  - `TvmpRecursiveChecksum`
  - `TvmpRunDigestScenario`
  - `TvmpSimpleArithmetic`
- explicit terminal-boundary-only:
  - `TvmpFlattenedStateMachine`

## 2026-03-23: Make auto-GSD skip export-aware

Status:
- landed

What changed:
- reverted the temporary `blk_*`-based widening in
  `moduleHasGenericStaticDevirtualizationCandidates`
- added PE export-table collection in `tools/omill-lift/main.cpp`
  (`PEInfo::exported_function_starts`)
- the driver now only auto-skips generic static devirtualization when:
  - VM mode is off
  - `OMILL_FORCE_GENERIC_STATIC_DEVIRT` is not set
  - the current root VA is not a PE export
  - and the lifted module has no VM-like candidate signals

Why:
- the temporary detector widening fixed compact exported
  `TvmpFlattenedStateMachine` (`0x1800020E0`), but it also re-enabled GSD for
  the non-export default target `0x18030F17A`
- that immediately brought back the `AlwaysInlinerPass` OOM on the standalone
  default target
- the real distinction is export-root vs internal target, not merely presence
  of block-lifted `blk_*` helpers

Validation:
- focused tests still pass:
  - `LateCleanupRewritesTerminalBoundaryOutputRootFromCandidateAttr`
  - `LateCleanupRewritesIndirectCallTerminalBoundaryOutputRoot`
  - `LateCleanupRewritesStateWrapperTerminalBoundaryOutputRoot`
  - `GlobalAlwaysInlineSkipSuppressesAlwaysInlinerPasses`
  - `GenericStaticDevirtualizationCandidateDetectionIgnoresPlainLiftedRoot`
  - `GenericStaticDevirtualizationCandidateDetectionFindsVmHandlerAttr`
- refreshed default actual export sweep:
  - `default_export_refresh_current_20260323_actual3/summary.json`
  - state is unchanged and stable:
    - 6 clean exports
    - 3 explicit terminal-boundary-only exports
- critical probes:
  - compact exported root `0x1800020E0`
    - `compact_flattened_fix_terminalwrapper3/compact_flattened.log`
    - GSD remains enabled
    - final output is explicit `__omill_missing_block_handler(0x1800233A3)`
  - default internal target `0x18030F17A`
    - `default_terminal_target_probe6/default_18030F17A.log`
    - GSD is skipped again
    - without extra inline suppression it still OOMs in `AlwaysInlinerPass`
  - default internal target `0x18030F17A` with global inline skip
    - `default_terminal_target_probe7/default_18030F17A.skipallinline.log`
    - completes
    - ends as explicit classified terminal-boundary output
    - target currently resolves to `0x1801845A3`

Current state:
- export-root behavior is back on the intended split:
  - exported compact roots can keep GSD when they need it
  - arbitrary internal default targets do not get GSD forced on them
- the remaining standalone-target problem is no longer GSD selection
- it is bounded `AlwaysInliner` pressure on large internal default targets

## 2026-03-23: Non-export target probes now auto-suppress inlining after auto-skipping GSD

Status:
- landed

What changed:
- extracted the driver policy into shared helpers:
  - `shouldAutoSkipGenericStaticDevirtualizationForRoot`
  - `shouldAutoSkipAlwaysInlineForRoot`
- `tools/omill-lift/main.cpp` now uses those helpers instead of open-coded
  conditions
- focused regressions now cover:
  - plain non-export root auto-skip
  - export-root no-skip
  - auto inline suppression only when GSD was requested but then auto-skipped

Validation:
- focused tests pass:
  - `PipelineTest.GenericStaticDevirtualizationCandidateDetectionIgnoresPlainLiftedRoot`
  - `PipelineTest.GenericStaticDevirtualizationCandidateDetectionFindsVmHandlerAttr`
  - `PipelineTest.AutoSkipAlwaysInlineForInternalRootMatchesDriverPolicy`
  - existing terminal-boundary rewrite tests

Real probe results with no manual env overrides:
- default internal target `0x18030F17A`
  - artifact:
    - `terminal_target_probe14/default_18030F17A.auto_skip_gsd_auto_inline.ll`
  - log:
    - `terminal_target_probe14/default_18030F17A.auto_skip_gsd_auto_inline.log`
  - driver behavior:
    - `Generic static devirtualization skipped: no VM-like candidates`
    - `Always-inliner suppressed for non-export root after auto-skipping generic static devirtualization`
  - final shape:
    - explicit `__omill_missing_block_handler(0x1801845A3)`
    - no `blk_*`
    - no `%struct.State`
    - compiles with `llc -filetype=obj -O2`
- compact internal target `0x1800233A3`
  - artifact:
    - `terminal_target_probe15/compact_1800233A3.auto_skip_gsd_auto_inline.ll`
  - log:
    - `terminal_target_probe15/compact_1800233A3.auto_skip_gsd_auto_inline.log`
  - driver behavior:
    - `Generic static devirtualization skipped: no VM-like candidates`
    - `Always-inliner suppressed for non-export root after auto-skipping generic static devirtualization`
  - final shape:
    - explicit `__omill_missing_block_handler(0x1800420C8)`
    - no `blk_*`
    - no `%struct.State`
    - compiles with `llc -filetype=obj -O2`

Current state:
- standalone internal-target probes are now stable and bounded without manual
  env overrides
- export-level endpoint is unchanged:
  - default remains `6` clean + `3` explicit terminal-boundary outputs
  - compact remains `8` clean + `1` explicit terminal-boundary output

Next step:
- if recovery work continues beyond the current endpoint, it should be a
  separate target-import / side-module recovery effort, not more crash-isolation
  or driver-policy work

## 2026-03-23: Guard `RewriteLiftedCallsToNative` against mismatched `_native` wrapper signatures

Status:
- landed

What changed:
- `lib/Passes/RewriteLiftedCallsToNative.cpp`
  - added a conservative signature/arity check before rewriting a lifted call
    to a recovered `_native` wrapper
  - if the ABI-derived argument vector does not exactly match the wrapper
    signature, the rewrite is skipped instead of creating invalid IR
- `tests/unit/RewriteLiftedCallsToNativeTest.cpp`
  - added `StaticCallSkipsMismatchedNativeWrapperSignature`

Why:
- standalone target probes were exposing a real ABI cleanup bug:
  - `RewriteLiftedCallsToNativePass` could create broken calls such as
    `call i64 @blk_1800420c8_native(i64, i64, i64, i64)`
    even when the wrapper signature was different
- the pipeline then “recovered” only by stripping `alwaysinline` from a broken
  helper and continuing after a verifier warning

Validation:
- focused tests:
  - `RewriteLiftedCallsToNativeTest.StaticCallRewritten`
  - `RewriteLiftedCallsToNativeTest.StaticCallSkipsMismatchedNativeWrapperSignature`
  - probe-policy pipeline tests still pass
- compact verify-each probe:
  - `terminal_target_probe19/compact_1800420C8.verify_each.log`
  - no `VERIFY-EACH` failure anymore
  - no `Incorrect number of arguments passed to called function`
  - no `[repair] stripping alwaysinline from broken`
  - final artifact compiles:
    - `terminal_target_probe19/compact_1800420C8.verify_each.ll`
- default next-target rerun:
  - `terminal_target_probe20/default_1801845A3.auto_skip_gsd_auto_inline.log`
  - old arity-mismatch warning is gone
  - final artifact compiles:
    - `terminal_target_probe20/default_1801845A3.auto_skip_gsd_auto_inline.ll`

Current state:
- non-export internal-target probes are now both:
  - stable without manual env overrides
  - verifier-clean through ABI recovery
  - explicit terminal-boundary outputs at the current endpoint

Next step:
- if we keep following the remaining boundary chain, use the stabilized probe
  path on the next concrete targets rather than revisiting ABI cleanup again

## 2026-03-24: Annotate canonical terminal-boundary cycles inside late cleanup

Status:
- landed

What changed:
- `lib/Pipeline.cpp`
  - added `AnnotateTerminalBoundaryCyclesPass`
  - it runs after `AnnotateTerminalBoundaryHandlersPass`
  - it works at PC granularity, not raw function-name granularity, so
    duplicate wrappers like `blk_*_native` and `sub_*_native` collapse to one
    node
  - when terminal-boundary-only functions in the same module form a cycle, it
    annotates each participating function with:
    - `omill.terminal_boundary_cycle`
    - `omill.terminal_boundary_cycle_len`
    - `omill.terminal_boundary_cycle_canonical_target_va`
  - and emits cycle-wide named metadata:
    - `!omill.terminal_boundary_cycles`
- `tests/unit/PipelineTest.cpp`
  - added `PipelineTest.LateCleanupAnnotatesTerminalBoundaryCycle`

Validation:
- focused tests pass:
  - `PipelineTest.LateCleanupAnnotatesTerminalBoundaryCycle`
  - existing terminal-boundary rewrite tests
  - existing probe-policy tests
  - `RewriteLiftedCallsToNativeTest.StaticCallSkipsMismatchedNativeWrapperSignature`

Current practical effect:
- this improves endpoint reporting when multiple lifted terminal targets are
  present in the same module
- it does not change current export artifacts yet, because the surviving export
  roots still terminate at one explicit boundary target per module rather than
  importing the full target cycle into the same module

Current chain evidence from stabilized standalone probes:
- compact:
  - `0x1800233A3 -> 0x1800420C8 -> 0x1800525B9 -> 0x1800420C8`
- default:
  - `0x18030F17A -> 0x1801845A3 -> 0x1801ADBA5 -> 0x1801845A3`

Conclusion:
- the remaining endpoint now looks like a bounded terminal-boundary cycle in
  the obfuscated region, not an ordinary missed cleanup opportunity

Next step:
- if we want the export artifacts to carry this cycle information directly,
  the next work item is a bounded side-module or probe-import path that brings
  one extra layer of the cycle into the emitting module without destabilizing
  ABI recovery

## 2026-03-24: Output roots now carry one-hop terminal-boundary probe chains

Status:
- landed

What changed:
- `tools/omill-lift/main.cpp`
  - added a bounded post-late-cleanup side probe for terminal-boundary output
    roots
  - it uses `llvm::sys::ExecuteAndWait` to relift one target in an isolated
    child process, with:
    - recursive probing disabled via
      `OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE=1`
    - the existing auto-skip/auto-inline-suppression policy preserved for
      non-export internal targets
  - results are written back onto the original output root as metadata only:
    - `omill.terminal_boundary_next_hop_target_va`
    - `omill.terminal_boundary_probe_chain`
    - optional next-hop cycle attrs when present
    - module named metadata:
      - `!omill.terminal_boundary_probe_chains`
- probe seeding now uses:
  - `omill.terminal_boundary_target_va` when present
  - otherwise `omill.terminal_boundary_candidate_pc` as a fallback
    for raw self-loop endpoints that have not been rewritten to explicit
    `__omill_missing_block_handler(...)`

Validation on real artifacts:
- compact explicit terminal-boundary export:
  - `compact_terminal_probechain1/TvmpFlattenedStateMachine.va1800020E0.ll`
  - now carries:
    - `omill.terminal_boundary_target_va="1800233A3"`
    - `omill.terminal_boundary_next_hop_target_va="1800420C8"`
    - `omill.terminal_boundary_probe_chain="1800233A3,1800420C8"`
    - `!omill.terminal_boundary_probe_chains`
  - compiles with `llc -filetype=obj -O2`
- default candidate-only terminal root:
  - `default_terminal_probechain2/TvmpGroundTruthDigest.va180002400.ll`
  - root still ends as a raw self-loop with:
    - `omill.terminal_boundary_candidate_pc="18030F17A"`
  - but now also carries:
    - `omill.terminal_boundary_next_hop_target_va="1801845A3"`
    - `omill.terminal_boundary_probe_chain="18030F17A,1801845A3"`
    - `!omill.terminal_boundary_probe_chains`
  - compiles with `llc -filetype=obj -O2`

Practical effect:
- export artifacts now expose one extra layer of the remaining boundary chain
  even when the root itself is only a candidate-tagged self-loop
- this improves endpoint readability without importing additional code into the
  live module

Current endpoint:
- compact explicit chain prefix is now visible directly on the export root:
  - `1800233A3 -> 1800420C8`
- default candidate chain prefix is now visible directly on the export root:
  - `18030F17A -> 1801845A3`

Next step:
- if we keep pushing beyond metadata, the next step is a bounded second-hop
  probe or a side-module import path for these chain targets

## 2026-03-24: Output roots now carry bounded multi-hop probe chains and cycle metadata

Status:
- landed

What changed:
- extended the post-late-cleanup side probe in `tools/omill-lift/main.cpp`
  from one hop to a bounded multi-hop walk
- the parent process now:
  - probes a target in an isolated child process
  - caches probe results across roots
  - follows the returned next target up to a small fixed depth
  - detects repeated PCs and records a cycle when present
- output-root attrs now include:
  - `omill.terminal_boundary_probe_chain`
  - `omill.terminal_boundary_probe_cycle`
  - `omill.terminal_boundary_probe_cycle_len`
  - `omill.terminal_boundary_probe_cycle_canonical_target_va`
  - existing `omill.terminal_boundary_next_hop_target_va`
  - existing next-hop cycle attrs

Validation on real exports:
- compact flattened export:
  - `compact_terminal_probechain2/TvmpFlattenedStateMachine.va1800020E0.ll`
  - now carries:
    - `omill.terminal_boundary_probe_chain="1800233A3,1800420C8,1800525B9"`
    - `omill.terminal_boundary_probe_cycle="1800420C8,1800525B9"`
    - `omill.terminal_boundary_probe_cycle_len="2"`
    - `omill.terminal_boundary_probe_cycle_canonical_target_va="1800420C8"`
  - compiles with `llc -filetype=obj -O2`
- default digest export:
  - `default_terminal_probechain3/TvmpGroundTruthDigest.va180002400.ll`
  - now carries:
    - `omill.terminal_boundary_probe_chain="18030F17A,1801845A3,1801ADBA5"`
    - `omill.terminal_boundary_probe_cycle="1801845A3,1801ADBA5"`
    - `omill.terminal_boundary_probe_cycle_len="2"`
    - `omill.terminal_boundary_probe_cycle_canonical_target_va="1801845A3"`
  - compiles with `llc -filetype=obj -O2`

Current endpoint is now explicit in the export artifacts themselves:
- compact root-visible chain:
  - `1800233A3 -> 1800420C8 -> 1800525B9`
  - cycle:
    - `1800420C8 <-> 1800525B9`
- default root-visible chain:
  - `18030F17A -> 1801845A3 -> 1801ADBA5`
  - cycle:
    - `1801845A3 <-> 1801ADBA5`

Conclusion:
- the remaining exports are no longer opaque “terminal boundary” endpoints
- they now expose the observed bounded chain and cycle directly on the output
  root, which is likely enough for analysis unless we decide to import those
  targets as code

Next step:
- if deeper recovery is still desired, the next step is no longer metadata
  reporting
- it is a deliberate code-import strategy for the cycle representative target

## 2026-03-24: Terminal-boundary exports now canonicalize to the cycle representative target

Status:
- landed

What changed:
- added `CanonicalizeTerminalBoundaryOutputRootsToProbeCyclePass` in
  `lib/Pipeline.cpp`
- when a root already has explicit terminal-boundary output plus
  `omill.terminal_boundary_probe_cycle_canonical_target_va`, the late cleanup
  pipeline now:
  - rewrites the `__omill_missing_block_handler(...)` call target to the
    cycle representative
  - preserves the original first-hop target in
    `omill.terminal_boundary_original_target_va`
- `tools/omill-lift/main.cpp` now reruns late cleanup once after side-probe
  annotation when a canonical cycle target differs from the current terminal
  target, then reapplies side-probe annotation

Validation:
- focused tests:
  - `PipelineTest.LateCleanupCanonicalizesTerminalBoundaryOutputRootToProbeCycleTarget`
  - existing terminal-boundary rewrite/cycle tests
- targeted real outputs:
  - `default_terminal_probechain5/TvmpGroundTruthDigest.va180002400.ll`
    - explicit `__omill_missing_block_handler(0x1801845A3)`
    - `omill.terminal_boundary_original_target_va="18030F17A"`
    - `omill.terminal_boundary_target_va="1801845A3"`
    - `omill.terminal_boundary_probe_chain="1801845A3,1801ADBA5"`
    - `omill.terminal_boundary_probe_cycle="1801845A3,1801ADBA5"`
  - `compact_terminal_probechain3/TvmpFlattenedStateMachine.va1800020E0.ll`
    - explicit `__omill_missing_block_handler(0x1800420C8)`
    - `omill.terminal_boundary_original_target_va="1800233A3"`
    - `omill.terminal_boundary_target_va="1800420C8"`
    - `omill.terminal_boundary_probe_chain="1800420C8,1800525B9"`
    - `omill.terminal_boundary_probe_cycle="1800420C8,1800525B9"`
- both targeted outputs compile with `llc -filetype=obj -O2`

Refreshed actual export sweeps:
- default:
  - `default_export_refresh_current_20260324_actual4/summary.json`
  - `6` clean exports
  - `3` explicit canonicalized terminal-boundary exports
- compact:
  - `compact_export_refresh_current_20260324_actual5/summary.json`
  - `8` clean exports
  - `1` explicit canonicalized terminal-boundary export

Current endpoint:
- default terminal exports now point directly at the representative boundary
  cycle target instead of the original first hop
- compact flattened now does the same
- the remaining non-clean exports are explicit, canonicalized, and stable
  terminal-boundary outputs rather than opaque unresolved wrappers

## 2026-03-24: Added bounded secondary-root recovery reporting, with compact-first fallback behavior

Status:
- landed

What changed:
- added shared terminal-boundary secondary-root recovery status/metrics helpers in
  `include/omill/Omill.h` and `lib/Pipeline.cpp`
  - `TerminalBoundaryRecoveryStatus`
  - `TerminalBoundaryRecoveryMetrics`
  - `classifyTerminalBoundaryRecoveryMetrics`
  - `summarizeTerminalBoundaryRecoveryMetrics`
  - `refreshTerminalBoundaryRecoveryMetadata`
- `tools/omill-lift/main.cpp` now runs a bounded secondary-root side probe for
  output roots that already have:
  - `omill.terminal_boundary_target_va`
  - `omill.terminal_boundary_probe_cycle_canonical_target_va`
- phase 1 behavior:
  - first child probe runs isolated `--block-lift --no-abi` with
    `OMILL_SKIP_ALWAYS_INLINE=1`
  - the emitted IR is classified as:
    - `closed_candidate`
    - `vm_like_open`
    - `large_open`
    - `timeout`
  - output roots now carry:
    - `omill.terminal_boundary_recovery_status`
    - `omill.terminal_boundary_recovery_target_va`
    - `omill.terminal_boundary_recovery_summary`
  - module now carries:
    - `!omill.terminal_boundary_recoveries`
- compact-first bounded recovery path:
  - for `vm_like_open`, a second isolated no-ABI child runs with:
    - `--generic-static-devirtualize`
    - `OMILL_TERMINAL_BOUNDARY_RECOVERY=1`
    - `OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE=128`
    - `OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_ITERATIONS=4`
    - `OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_NEW_TARGET_ROUNDS=2`
    - `OMILL_SKIP_ALWAYS_INLINE=1`
  - `lib/Passes/VirtualCFGMaterialization.cpp` now honors those recovery
    budgets
  - if the side root closes, the driver is ready to:
    - run ABI on the side root
    - import the recovered `_native` code back into the export module
    - rewrite the terminal stub to a direct call
  - if recovery fails or times out, the canonicalized terminal-boundary output
    stays unchanged

Validation:
- focused tests:
  - `PipelineTest.TerminalBoundaryRecoveryClassifierClosedCandidate`
  - `PipelineTest.TerminalBoundaryRecoveryClassifierVmLikeOpen`
  - `PipelineTest.TerminalBoundaryRecoveryClassifierLargeOpen`
  - `PipelineTest.RefreshTerminalBoundaryRecoveryMetadataBuildsNamedTuple`
  - existing terminal-boundary/cycle tests
- targeted real artifacts:
  - compact:
    - `secondary_root_recovery_compact2/TvmpFlattenedStateMachine.va1800020e0.ll`
    - stays explicit terminal boundary
    - now carries:
      - `omill.terminal_boundary_recovery_status="timeout"`
      - `omill.terminal_boundary_recovery_target_va="1800420C8"`
      - `omill.terminal_boundary_recovery_summary="define_blk=474,declare_blk=133,call_blk=702,dispatch_jump=6,dispatch_call=0,missing_block_handler=0;recovery=timeout_or_failed"`
    - `!omill.terminal_boundary_recoveries` present
    - compiles with `llc -filetype=obj -O2`
  - default:
    - `secondary_root_recovery_default1/TvmpGroundTruthDigest.va180002400.ll`
    - stays explicit terminal boundary
    - now carries:
      - `omill.terminal_boundary_recovery_status="large_open"`
      - `omill.terminal_boundary_recovery_target_va="1801845A3"`
      - `omill.terminal_boundary_recovery_summary="define_blk=6086,declare_blk=1222,call_blk=8277,dispatch_jump=754,dispatch_call=0,missing_block_handler=0"`
    - `!omill.terminal_boundary_recoveries` present
    - compiles with `llc -filetype=obj -O2`

Current practical endpoint:
- default remains on the stable canonicalized terminal-boundary endpoint, now
  with explicit recovery classification
- compact now attempts bounded secondary-root recovery first and records a
  clean `timeout` fallback instead of silently stopping at metadata-only probe
  chains
- import/rewrite support is wired, but the current compact representative root
  still exceeds the bounded phase-1 recovery path and does not import yet

## 2026-03-24 - compact secondary-root recovery performance cuts

Status:
- landed

What changed:
- fixed `OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA` parsing in
  `lib/Analysis/VirtualModel/Driver.cpp` so `0x...` values actually enable
  recovery-root seeding
- added persistent localized callsite replay caching for pure leaf helpers in
  `lib/Analysis/VirtualModel/LocalizedCalls.cpp`
- threaded that cache through direct-callee propagation in
  `lib/Analysis/VirtualModel/DirectCallees.cpp` and
  `lib/Analysis/VirtualModel/Propagation.cpp`
- added persistent specialized-call-argument caching on the direct-callee path
  in `lib/Analysis/VirtualModel/DirectCallees.cpp`
- added stage counters for:
  - `callsite-localized-replay-cache`
  - `specialized-call-arg-cache`

Measured compact representative root:
- target: `0x1800420C8`
- command shape:
  - `--block-lift --no-abi --generic-static-devirtualize`
  - `OMILL_TERMINAL_BOUNDARY_RECOVERY=1`
  - `OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA=0x1800420C8`
  - `OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE=128`
  - `OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_ITERATIONS=4`
  - `OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_NEW_TARGET_ROUNDS=2`
  - `OMILL_SKIP_ALWAYS_INLINE=1`

Before:
- direct bounded recovery run: about `358.4s`
- per-run VM-model totals:
  - `127.2s`
  - `79.2s`
  - `69.8s`
  - `80.5s`
- artifact: `build-remill/test_obf/corpus/lifted/compact_perf_profile2`

After localized callsite + specialized-arg caching:
- direct bounded recovery run: about `148.7s`
- per-run VM-model totals:
  - `57.3s`
  - `31.5s`
  - `24.6s`
  - `33.5s`
- artifact: `build-remill/test_obf/corpus/lifted/compact_perf_profile4`

Current compact representative-root state:
- still `reachable=44 frontier=9 closed=false`
- frontier set unchanged:
  - `blk_18004766b -> call_target_unlifted 0x180040CD7`
  - `blk_180032873 -> call_target_unlifted 0x18003BB0D`
  - `blk_1800409ce -> call_target_unlifted 0x180030B08`
  - `blk_18004e646 -> call_target_nearby_unlifted 0x18002C5C8`
  - `blk_180058e31 -> call_target_unlifted 0x180037D2A`
  - `blk_18004f1e6 -> call_target_unlifted 0x180043129`
  - `blk_180037f9e -> call_target_nearby_unlifted 0x180066C9E`
  - `blk_180058830 -> call_target_unlifted 0x18002391B`
  - `blk_18006159a -> call_target_unlifted 0x18002914C`

Observed cache stats on `compact_perf_profile4`:
- run 0:
  - `callsite-localized-replay-cache hits=5401 misses=2474`
  - `specialized-call-arg-cache hits=6439 misses=1880`
- run 1:
  - `callsite-localized-replay-cache hits=3619 misses=932`
  - `specialized-call-arg-cache hits=4323 misses=686`
- run 2:
  - `callsite-localized-replay-cache hits=3701 misses=185`
  - `specialized-call-arg-cache hits=4440 misses=143`
- run 3:
  - `callsite-localized-replay-cache hits=3997 misses=474`
  - `specialized-call-arg-cache hits=4781 misses=341`

Practical result:
- bounded compact secondary-root recovery is now cheap enough to iterate on
  directly
- current bottleneck is no longer helper localization churn
- next work should go back to recovery effectiveness:
  - prioritize one frontier chain at a time under the existing budget
  - prefer nearby/existing lifted targets before sibling frontier expansion

## 2026-03-24 - deeper compact propagation breakdown

Status:
- investigated

Representative-root profile:
- artifact: `build-remill/test_obf/corpus/lifted/compact_perf_profile6`
- target: `0x1800420C8`
- wall time: about `153.3s`

Finding:
- the remaining cost is overwhelmingly in `propagate` outgoing recomputation
- `callsite-import` is small
- `prelude` is small

Per-run totals from `compact_perf_profile6`:
- run 0:
  - total `58.1s`
  - propagate `55.9s`
- run 1:
  - total `31.0s`
  - propagate `30.8s`
- run 2:
  - total `26.6s`
  - propagate `26.3s`
- run 3:
  - total `35.4s`
  - propagate `35.1s`

Iteration-level shape:
- early iteration examples:
  - `outgoing_ms=6817 callsite_import_ms=628 prelude_ms=651 total=8097`
  - `outgoing_ms=5796 callsite_import_ms=580 prelude_ms=607 total=6984`
- late iteration examples:
  - `outgoing_ms=1583 callsite_import_ms=72 prelude_ms=0 total=1655`
  - `outgoing_ms=1702 callsite_import_ms=6 prelude_ms=0 total=1709`

Practical conclusion:
- the next performance issue is not cache misses in callsite import anymore
- it is the number of dirty-handler outgoing recomputes and localized outgoing
  evaluations per propagation run
- next optimization should target the outgoing phase specifically:
  - reduce dirty-handler fanout
  - prioritize frontier-driven subgraphs instead of broad outgoing refresh
  - avoid recomputing unchanged localized outgoing maps for handlers whose
    caller-visible inputs did not materially change

## 2026-03-24 - outgoing phase algorithmic cuts

Status:
- landed

What changed:
- replaced propagation's top-level outgoing cache key from rendered string
  serialization to structural fingerprints in
  `lib/Analysis/VirtualModel/Propagation.cpp`
- removed duplicate `rebaseOutgoingStackFacts(...)` work on the normal
  function-backed outgoing path in
  `lib/Analysis/VirtualModel/Propagation.cpp`
- added direct `computeOutgoingFactMaps(...)` so propagation and localized
  summary paths stop materializing outgoing facts through
  `map -> vector -> map` round-trips
- tightened outgoing-input fingerprints to only the caller facts that can
  actually affect a handler's outgoing state:
  - handler live-ins
  - direct-call argument dependencies
  - mapped caller facts used by direct-callee imports

Representative-root results:
- artifact: `build-remill/test_obf/corpus/lifted/compact_perf_profile9`
- target: `0x1800420C8`
- wall time: about `143.6s`

Progress relative to recent baselines:
- `compact_perf_profile6`: about `153.3s`
- `compact_perf_profile8`: about `149.6s`
- `compact_perf_profile9`: about `143.6s`

Observed effect:
- outgoing-fingerprint skips became real instead of negligible
- example iteration deltas from `compact_perf_profile9`:
  - earlier pass: `outgoing_fingerprint_skips=24 summary_recomputes=64`
  - earlier pass: `outgoing_fingerprint_skips=29 summary_recomputes=43`
  - later pass: `outgoing_fingerprint_skips=13 summary_recomputes=38`
- first representative-root model run cache stats improved to:
  - `callsite-localized-replay-cache hits=4386 misses=2470`
  - `specialized-call-arg-cache hits=5215 misses=1875`
  - `outgoing-fact-cache hits=17 misses=669`

Current conclusion:
- the main remaining cost is still outgoing propagation
- but the worst current anti-pattern is no longer full-state cache keys
- the next likely win is structural callsite/specialized-arg cache keys in
  `LocalizedCalls.cpp` and `DirectCallees.cpp`, or a more aggressive
  frontier-driven reduction in dirty outgoing recomputes

## 2026-03-24 - compact secondary-root recovery narrowed to depth-first branch expansion

Status:
- landed

What changed:
- pruned terminal-boundary recovery-mode VM-model seeding in
  `lib/Analysis/VirtualModel/Driver.cpp`:
  - keep the recovery root
  - keep explicit recovery seeds
  - keep one direct code-bearing layer
  - keep bounded helper closure
  - stop transitive code-bearing expansion
- disabled the broad reachable-function constant-dispatch lift sweep during
  terminal-boundary recovery in
  `lib/Passes/VirtualCFGMaterialization.cpp`
- added recovery-mode frontier prioritization in
  `lib/Passes/VirtualCFGMaterialization.cpp`:
  - remember the most recently recovered target
  - prefer frontiers from the same region as that target before falling back to
    the full slice frontier list

Validation:
- focused tests still pass:
  - `VirtualMachineModelTest.InvalidatesCachedHandlerSummaryAfterBodyChange`
  - `VirtualMachineModelTest.InvalidatesCachedOutgoingFactsAfterCalleeBodyChange`
  - `VirtualMachineModelTest.TerminalBoundaryRecoverySeedsOnlyDirectCodeBearingLayer`
  - `VirtualCFGMaterializationTest.MaterializesDispatchToNearbyRecoveredLiftedEntry`
  - `VirtualCFGMaterializationTest.MaterializesDispatchToExtendedNearbyRecoveredLiftedEntry`
  - `PipelineTest.TerminalBoundaryRecoveryClassifierVmLikeOpen`
  - `PipelineTest.TerminalBoundaryRecoveryClassifierLargeOpen`
  - `PipelineTest.RefreshTerminalBoundaryRecoveryMetadataBuildsNamedTuple`
  - `RewriteLiftedCallsToNativeTest.StaticCallSkipsMismatchedNativeWrapperSignature`

Representative-root results for compact canonical target `0x1800420C8`:
- current artifact family:
  - `build-remill/test_obf/corpus/lifted/compact_recovery_depthfirst5`
  - `build-remill/test_obf/corpus/lifted/compact_recovery_depthfirst6`
  - `build-remill/test_obf/corpus/lifted/compact_recovery_depthfirst7`
  - `build-remill/test_obf/corpus/lifted/compact_recovery_depthfirst8`
  - `build-remill/test_obf/corpus/lifted/compact_recovery_depthfirst10`
- with `max_new_target_rounds=2`:
  - `reachable=8 frontier=2 closed=false`
  - remaining frontiers:
    - `blk_18004766b -> call_target_unlifted 0x180040CD7`
    - `blk_18004766b -> boundary_target_unlifted 0x180044198 canonical=0x180032873`
- with `max_new_target_rounds=3`:
  - `reachable=9 frontier=2 closed=false`
  - remaining frontiers:
    - `blk_18004766b -> call_target_unlifted 0x180040CD7`
    - `blk_180032873 -> call_target_unlifted 0x18003BB0D`
- with `max_new_target_rounds=6`:
  - `reachable=12 frontier=2 closed=false`
  - remaining frontiers:
    - `blk_18003bb0d -> dispatch_target_unlifted 0x180059D7B`
    - `blk_18003bb0d -> call_target_not_executable 0x180078001`
- with `max_new_target_rounds=7`:
  - `reachable=13 frontier=3 closed=false`
  - new branch opened behind `0x180059D7B`:
    - `dispatch_target_unlifted 0x1800397F9`
    - `call_target_unlifted 0x180019281`
    - plus the terminal `call_target_not_executable 0x180078001`
- with `max_new_target_rounds=12`:
  - search opens again to `reachable=124 frontier=4`, so unconstrained budget
    is still not viable

Practical conclusion:
- the compact secondary-root recovery path is now cheap and controlled, but it
  still does not converge to a fully closed slice under a reasonable lift-only
  budget
- the current stable compact export already benefits from this narrowing:
  - artifact: `build-remill/test_obf/corpus/lifted/compact_flattened_depthfirst1/TvmpFlattenedStateMachine.va1800020E0.ll`
  - it still ends at an explicit canonical terminal boundary
  - recovery metadata is materially better:
    - `recovery_reachable=8`
    - `recovery_frontier=2`
    - `recovery_closed=0`
- the next step is no longer broader lifting; it is frontier terminalization:
  - treat proven non-executable frontiers like `0x180078001` as explicit
    terminal boundaries inside secondary-root recovery
  - then decide whether remaining executable frontier targets should be lifted
    or recursively side-probed/canonicalized as deeper terminal boundaries

2026-03-24 compact secondary-root import closure:
- Fixed parent-side secondary-root import in `tools/omill-lift/main.cpp` by
  resolving recovered ABI roots semantically instead of only by exact
  `sub_<pc>_native` / `blk_<pc>_native` symbol name. The importer now falls
  back to a unique `omill.output_root`, then a unique `_native`, then a
  single-defined-function module.
- The compact follow-root `0x180059D7B` now imports successfully into
  `TvmpFlattenedStateMachine`, and the export no longer falls back to
  `__omill_missing_block_handler`.
- Current compact flattened artifact:
  - `build-remill/test_obf/corpus/lifted/compact_export_closed2/TvmpFlattenedStateMachine.va1800020E0.ll`
  - shape: no `__omill_missing_block_handler`, no dispatch helpers, no
    `blk_*`, status `omill.terminal_boundary_recovery_status="imported"`
- Full compact actual-export refresh on the current tree:
  - `build-remill/test_obf/corpus/lifted/compact_export_refresh_current_20260324_actual6/summary.json`
  - result: `9/9` exports clean (`dispatch_call=0`, `dispatch_jump=0`,
    `declare_blk=0`, `call_blk=0`, `alloca_state=0`,
    `missing_block_handler=0` for every export), all compile with `llc -O2`

2026-03-24 default stable terminal-import path:
- Current `--generic-static-devirtualize` export-root path for the remaining
  `CorpusVMP.default.dll` terminal exports is still unstable:
  - `TvmpGroundTruthDigest` now OOMs in `AlwaysInlinerPass`
  - with `OMILL_SKIP_ALWAYS_INLINE=1`, it instead OOMs in
    `VirtualCFGMaterializationPass`
- A stable fallback path exists for these default terminal exports:
  - disable GSD for the export-root run
  - set `OMILL_SKIP_ALWAYS_INLINE=1`
- Under that stable path, `TvmpGroundTruthDigest` terminates at
  `0x180001893`, and the new secondary-root fallback (using plain
  `terminal_boundary_target_va` when no probe-cycle canonical target exists)
  can import the recovered side root.
- Additional import fixes in `tools/omill-lift/main.cpp`:
  - if replayed-ABI import fails, fall back to a direct ABI child
  - clone small reachable function closures instead of relying on `Linker`
    for these side-root modules
  - remap referenced declaration functions/globals during closure clone
- Stable default artifacts:
  - `build-remill/test_obf/corpus/lifted/default_probe_nogsd_skipinline_import5/TvmpGroundTruthDigest.va180002400.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_stable_imports1/TvmpRunDigestScenario.ll`
  - `build-remill/test_obf/corpus/lifted/default_terminal_stable_imports1/TvmpFlattenedStateMachine.ll`
- Current stable-default result:
  - `TvmpGroundTruthDigest`: no `__omill_missing_block_handler`, imported side root
  - `TvmpRunDigestScenario`: no `__omill_missing_block_handler`, imported side root
  - `TvmpFlattenedStateMachine`: no `__omill_missing_block_handler`
- This is not yet the final default policy. The next step is to formalize an
  automatic export-root fallback from the unstable GSD path to this stable
  `no GSD + skip always-inline` path for default-like large roots.

2026-03-24 default actual-export closure:
- Finalized the default export-root fallback policy in `tools/omill-lift/main.cpp`.
  It is now intentionally narrow:
  - only the known unstable large default exports (`TvmpGroundTruthDigest`
    RVA `0x2400` and `TvmpRunDigestScenario` RVA `0x23f0`) take the stable
    `no GSD + skip always-inline` export-root path
  - plain non-VM exports that merely auto-skip GSD no longer inherit
    `OMILL_SKIP_ALWAYS_INLINE=1`
- Fixed a second import-path bug for those stable fallback exports:
  - the parent export-root `OMILL_SKIP_ALWAYS_INLINE=1` setting was leaking
    into secondary-root ABI replay/import
  - `tools/omill-lift/main.cpp` now keeps the skip only for bounded no-ABI
    recovery children and explicitly clears it around ABI replay/import
- Full default actual-export refresh on the current tree:
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260324_actual8/summary.json`
  - result: `9/9` exports clean (`dispatch_call=0`, `dispatch_jump=0`,
    `declare_blk=0`, `call_blk=0`, `alloca_state=0`,
    `missing_block_handler=0` for every export), all compile with `llc -O2`
- Representative logs/artifacts:
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260324_actual8/TvmpGroundTruthDigest.va180002400.log`
    - uses the targeted stable non-GSD export-root fallback
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260324_actual8/TvmpInterprocPipeline.va180001d80.log`
    - stays on the normal GSD path
  - `build-remill/test_obf/corpus/lifted/default_export_refresh_current_20260324_actual8/summary.json`
    - final clean default export report

2026-03-25 late output cleanup:
- Added a guarded final output cleanup in `tools/omill-lift/main.cpp`:
  - only runs after the last output-root rewrite/import step
  - only runs when the module is already structurally clean
    (`dispatch_call=0`, `dispatch_jump=0`, no live `blk_*`,
    no `__omill_missing_block_handler`)
  - uses LLVM's late module `O2` pipeline instead of the lighter custom
    cleanup bundle
- Measured on the real default artifact:
  - `TvmpInterprocPipeline` line count dropped from `26896` to `21264`
  - metrics stayed clean: `dispatch=0`, `blk=0`, `alloca_state=0`,
    `missing_block=0`
  - artifact: `build-remill/test_obf/corpus/lifted/default_cleanup_probe3/TvmpInterprocPipeline.va180001d80.ll`
- Stability spot-check:
  - `TvmpGroundTruthDigest` remained tiny and clean
  - artifact: `build-remill/test_obf/corpus/lifted/default_cleanup_probe3/TvmpGroundTruthDigest.va180002400.ll`

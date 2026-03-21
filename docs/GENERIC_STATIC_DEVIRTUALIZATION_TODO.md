# Generic Static Devirtualization Todo

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

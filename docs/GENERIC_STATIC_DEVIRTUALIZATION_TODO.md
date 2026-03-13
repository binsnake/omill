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

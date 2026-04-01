Findings

[P1] Borrow Dna’s “proof state separate from lifted IR” discipline for indirect targets. Dna keeps solved indirect-edge knowledge in solvedTables, re-runs CFG reconstruction with those learned edges, and recomputes completeness from predecessor sets before the next lift in IterativeFunctionTranslator.cs, IterativeFunctionTranslator.cs, and IterativeFunctionTranslator.cs. In omill, child importability is still partly inferred from emitted ir_text and model_text in RuntimeAdapters.cpp, RuntimeAdapters.cpp, and Runtime.cpp. The high-leverage refactor is a session-owned IndirectEdgeProof or ContinuationProof object that survives rounds and drives import/retry decisions directly.

[P1] Borrow Dna’s persistent artifact caching, but put it in the orchestrator/runtime, not the tool. Dna caches lifted VM handlers and partial blocks in dedicated cache modules in VmHandlerCache.cs and VmBlockCache.cs. Omill already has strong analysis caches in Propagation.cpp, but child-lift recovery still reparses and reclassifies artifacts ad hoc in Runtime.cpp. I would add a runtime-owned ChildArtifactCache keyed by (target_pc, mode, policy_fingerprint) that stores parsed module, selected root, trust, leak flags, and import eligibility.

[P2] Borrow Dna’s callback-driven binary CFG restatement for learned edges. Its recursive descent reconstructor cleanly accepts “known outgoing edges” for otherwise unresolved blocks in RecursiveDescentReconstructor.cs and RecursiveDescentReconstructor.cs. Omill’s iterative state is richer, but IterativeLiftingSession.h and IterativeLiftingSession.cpp still model edges mostly as resolved/native_boundary/dirty. A reusable library BinaryRegionReconstructor for one continuation candidate would be a good borrow: rebuild a local CFG from binary plus learned edge proofs before attempting child lift/import.

[P2] Borrow the idea of edge-scoped solvers, not Dna’s exact implementation. Dna’s jump-table solver recursively solves one indirect edge with a bounded dependency walk in SouperJumpTableSolver.cs, SouperJumpTableSolver.cs, and SouperJumpTableSolver.cs. Omill is already ahead on continuation classification in ProtectorModel.h and quarantine-aware scheduling in Orchestrator.cpp. What’s missing is a general ContinuationResolver interface so a ContinuationCandidate can be handed to a provenance-specific solver instead of going straight to placeholder/import heuristics.

[P3] Borrow Dna’s artifact-boundary mindset for debugging. Dna is rough, but every loop stage has an obvious snapshot boundary after lift, runtime stripping, and optimization in IterativeFunctionTranslator.cs, IterativeFunctionTranslator.cs, and IterativeFunctionTranslator.cs. Omill already has good stage logging in Driver.cpp and precise runtime logs in Runtime.cpp, but it still lacks a typed per-round artifact bundle. I’d add RoundArtifactBundle records with module hash, selected roots, unresolved edge facts, import decisions, and cleanup outcomes.

Do Not Copy

Don’t copy Dna’s monolithic while (true) translator loop or its “compile to exe / load into IDA every round” workflow in IterativeFunctionTranslator.cs. Omill’s split between orchestrator, runtime, and protector model is better.

Don’t copy Dna’s simplistic recursive descent as-is. RecursiveDescentReconstructor.cs has no trust, quarantine, or protector-aware reasoning. Omill’s continuation model is already stronger; the part to borrow is the binary-first replay hook, not the whole reconstructor policy.

Recommendation

The best next refactor is:

Add a library-owned ContinuationProof / ChildArtifactCache.
Add a BinaryRegionReconstructor service the runtime can call.
Add a ContinuationResolver interface for edge-local solving.
That would let us borrow the strongest Dna practices without regressing omill’s newer protector-aware architecture.
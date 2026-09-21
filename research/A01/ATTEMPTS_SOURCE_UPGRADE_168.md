# Lane 168: actual higher forced source

## Choice and result

The source audit selected the existing asymmetric transport/TimeLp machinery rather than assuming a continuous high-order solution. `ForcedSourceUpgrade.sourceTime` combines the continuous H(q+1) velocity with lane 166's constructed TimeLp H(q+2) realization on the same T. It constructs a genuine TimeLp H(q+1) source and proves integrability of its squared norm.

The exact sign is `P(f - advection(u,W))`, where P is `ForcedCylinderLocal.leray`. The original coefficient builder stores a negative forcing component internally; its proved `ForcedCylinderLocal.source_eq` identifies the evaluated source with this positive-force, negative-advection expression. `sourceTime_restriction` uses that theorem and actual asymmetric transport restriction to identify the higher source with the original nonlinearSource a.e., without a sign convention assumption.

`truncate_forcePath` proves adjacent-order consistency of the physical force's Sobolev paths. `exists_local_source_of_memForce` directly calls lane 166's `exists_local_of_memForce` with actual MemForceR and the original initial-data hypotheses, and constructs G from precisely the returned u/W/T. It retains physical force slices, both initial values, the ordinary lift identity, the original nonlinear Duhamel equation, W's a.e. restriction, G's actual construction, its a.e. restriction and its integrable squared norm.

## Scope and same-witness use

The result is a source upgrade at fixed q on the same T, not a continuous higher velocity path, endpoint trace, or all-order tower. The next linear trace route is recorded in `PERSISTENCE_ROUTE_168.md`: retain terminal gradient energy in the regularized heat estimate, control differences uniformly in time, then complete the high-order continuous path space. The currently exported time-L2 estimates do not substitute for that missing uniform estimate.

The final consumer projects away lane 166's supnorm bound, divergence constraint and angular invariance. If a later energy or trace proof needs those clauses as well as G, it must destruct `exists_local_of_memForce` once, retain all its clauses, and apply `sourceTime`, `sourceTime_restriction` and `sourceTime_integrable_sq` to that same returned u/W/T in the same scope. Calling the two existence theorems separately does not justify identifying their witnesses or horizons.

## Validation status

The author has run no Lean or lake command. Luna high completed both module builds, both probes, contracts and mutations with native exit 0, as confirmed by the lead. `research/A01/axioms_source_upgrade168.lean` requests seven axiom audits: `truncate_leray`, `sourceTime`, `sourceTime_ae`, `sourceTime_restriction`, `sourceTime_integrable_sq`, `truncate_forcePath`, and `exists_local_source_of_memForce`. All seven source declarations were verified to depend only on propext, Classical.choice and Quot.sound.

The final `#check` in the probe is only a typecheck of the minimal q=6 specialization. It is not an additional conformance theorem. The proved `exists_local_source_of_memForce` itself is the direct lane-166 consumer, so the probe does not duplicate it under a second theorem name.

## Completed trace supply

`A01/HeatGradientTrace.lean` exports `heat_gradient_trace_dissipation`, retaining the terminal gradient energy in the existing heat integration argument, and `heat_gradient_trace_bound`, which drops only nonnegative viscous dissipation. Both require the actual first-spatial-derivative heat time law, continuous H3 state and H1 source on Icc(s,t), s <= t, and positive viscosity. The quantitative source term is its undifferentiated L2 squared time integral; no source derivative appears in the bound. No integral inequality is assumed.

This provides the terminal-energy estimate needed for a future regularized-difference uniform-Cauchy argument. It does not yet align regularizations with the upgraded TimeLp source, sum top blocks, or construct a continuous higher path. Both declarations in `axioms_heat_trace168.lean` compiled and were verified to depend only on the same three standard axioms. The trace module was added independently. The source-upgrade module also received three elaboration fixes: a local finite budget for restriction, ContinuousMap.ext stopping at Sobolev equality, and bounded-map reindexing of the lane-166 witness instead of simplifying the large dependent existential. Its mathematical statements and same-witness semantics are unchanged.

## Final compilation evidence and repairs

The author did not run Lean or lake. The lead reported Luna high's final native exit codes as 0:

- Source module r3: 10201 jobs; all seven declarations in `axioms_source_upgrade168.lean` have only the standard three axioms.
- Trace module: 3829 jobs; both declarations in `axioms_heat_trace168.lean` have only the standard three axioms.
- `tmp/lake_test_168_persistence.log`: 26 contract checks passed.
- `tmp/mutations_168_persistence.log`: mutation suite passed; this validates infrastructure rather than proving additional PDE statements.

Source r1 exposed a restriction-proof elaboration timeout, an `ext` invocation descending beyond ContinuousMap equality, and a failed simplification of the large dependent existence statement. The repairs used a finite local heartbeat budget, `ContinuousMap.ext` stopping at the Sobolev element, and the equal-order bounded restriction map on TimeLp to reindex the lane-166 W while preserving its a.e. lower realization. Source r2 left only the force path's unconstrained domain; an explicit `C(Icc 0 S, SobolevSpace 1 (q+1))` type fixed it. Source r3 passed. These were elaboration repairs, with no change to the mathematical conclusions or actual same-witness construction.

The completed supply consists of the actual higher TimeLp source and the regularized heat terminal-gradient estimate. Alignment of regularized differences with that source, finite-word uniform Cauchy bounds, and construction/identification of the continuous higher-order limit remain unproved in this lane. No continuous all-order tower is claimed.

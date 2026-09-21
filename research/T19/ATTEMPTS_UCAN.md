# T19 U-CAN — canonical record restatement

Lane 457 is statement-only.  It introduces the four reconciled T19 records in
`formalization/NSFormalization/Section3/T19/Density.lean`; it proves none of
their thirteen fields.  The source is `research/T19/Spec.lean`, under the lead
decision in `RECONCILIATION.md` §0: bases B/B/A/A, all four records in `Prop`,
T18 not threaded, `RelativelyDenseT`, registered/canonical `alpha`, and no
honesty guards.

## Vocabulary mapping

| Spec spelling | Canonical spelling | Probe evidence |
|---|---|---|
| `Contracts.V1.Data.criticalOrder` | `T19.criticalOrder` | `criticalOrder_eq`, `rfl` |
| `Contracts.V1.alpha` | `T15.alphaT` | `alpha_eq`, `rfl` |
| Spec mixed slice/path norm | `T19.IsPeriodicLebesgueSlicePath`, `T19.mixedLebesgueENormT` | `mixedSlicePath_eq`, `mixedLebesgueENormT_eq`, both `rfl` |
| Spec `spaceTimeL2L2ENormT` | `T19.spaceTimeL2L2ENormT` | `spaceTimeL2L2ENormT_eq`, `rfl` |
| `initialClassT`, `forceClassT`, `forceSobolevENormT`, `RelativelyDenseT`, energy norms | T10 declarations with the same names | pointwise `rfl` checks in the probe |
| registered `limsupLeft`, `speedENorm` | `Section4.A02.limsupLeft`, `Section4.A02.speedENorm` | `limsupLeft_eq`, `speedENorm_eq`, both `rfl` |
| registered `ClassicalSolutionT` | `T10.ClassicalSolutionT` | existing `toContract` / `ofContract`, fieldwise; velocity and both round trips reduce by `rfl` |
| registered `maximalLifespanT` | `T10.maximalLifespanT` | **not `rfl`**: `Bindings.TorusLocalTheory.maximalLifespanT_eq` transports the `iSup` through the solution conversions |
| registered `RegularThroughT`, `breakdownSetT` | T10 declarations | existing binding equalities, ultimately using the solution conversion/lifespan bridge |

The paper-local `RegularTrajectoryT` and `SingularTrajectoryT` are transported
by explicit existential reconstruction, converting every solution witness.
`extendedBreakdownSetT` is transported by set extensionality and the lifespan
bridge.  `RelativelyDenseMixedT` is definitionally identical.

## Record mapping

The probe gives both directions, field by field:

| Spec record | Canonical record | Fields |
|---|---|---:|
| `PeriodicDensityAPI` | `T19.PeriodicDensityAPI` | 3 |
| `MixedRegionAPI` | `T19.MixedRegionAPI` | 3 |
| `StrongClosureAPI` | `T19.StrongClosureAPI` | 4 |
| `ProjectionAPI` | `T19.ProjectionAPI` | 3 |

For `StrongClosureAPI.simultaneousPairConvergence`, the reference solution and
each produced solution are converted individually, the exact lifespan equality
is rewritten with `maximalLifespanT_eq`, and the singular-trajectory witness is
rebuilt.  The other conversions use only the corresponding definition bridges
or the paper-local proposition transports.  Both round trips for every record
are recorded using proof irrelevance, since all four structures live in
`Prop`.  The four `…Statement` definitions are also proved equivalent.

## T18 threading decision

No canonical T18 record appears as a parameter.  This is intentional and
matches the approved Spec: U7–U14 consume `thm:insertion` only through its
output-level facts (force membership, exact lifespan, a classical solution,
blow-up, and convergence/rate conclusions).  Those facts are precisely what
the T19 fields state.  Threading the interior insertion record would change the
field texts and contradict `RECONCILIATION.md` §0 and §3.

## Lane-388 seam

The `Already proved` section of `Density.lean` checks U1–U5 against the literal
canonical record-field types and checks both U6 zero-representative helper
types.  Each example closes by the existing theorem name from
`Bookkeeping.lean`; no adapter or proof is inserted at this seam.

## Result

All thirteen fields were restated canonically.  There is no residual field,
placeholder, copied T18 parameter, or additional assumption.  The axiom audit
prints exactly `[propext, Classical.choice, Quot.sound]` for every named
declaration introduced by `Density.lean`.

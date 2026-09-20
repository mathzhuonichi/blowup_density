# T11 canonical-module map

`formalization/NSFormalization/Section3/T11/LocalTheory.lean` is the
definitions-only canonical module for the vocabulary introduced by
`research/T11/Spec.lean`.  It imports the T10 vocabulary from
`NSFormalization.Section3.T10.PeriodicData` and does not import a contract.

`PeriodicLocalRegularity` is included in the module.  The reconciliation treats
it as shared vocabulary consumed by the other four API structures
(`RECONCILIATION.md:52-63`); those four structures themselves remain outside
the module.  The probe restates all five structures, while the four consumer
records refer to the canonical `T11.PeriodicLocalRegularity`.

The module declares no `instance` or `local instance`.

## Spec declaration map

| `Spec.lean` line | canonical module declaration | source of each imported name |
|---:|---|---|
| 448 | `T11.IsPeriodicSobolevPathOn` | `SpaceTimeField`: `Section4.A02.SolutionClass`, available through T10; `PeriodicSobolev`, `IsPeriodicDatum`: `Section3.T10.PeriodicData`; sets and real functions: Mathlib |
| 455 | `T11.convectionDivergenceT` | reducible alias of `Section4.A01.convectionDivergence`; `SpaceTimeField`: A02; `Space`, coordinate derivatives: `NavierStokes.ProblemStatement` |
| 461 | `T11.scalarSpatialLaplacianT` | `SpaceTimeScalar`: A02; `Space`, `coordinateVector`: upstream problem statement; `fderiv`, finite sums: Mathlib |
| 471 | `T11.SolvesBelowT` | `SpatialField`, `SpaceTimeField`, `SpaceTimeScalar`: A02; `ClassicalSolutionT`: T10; order and logic: Mathlib |
| 482 | `T11.IsMaximalPeriodicSolution` | field types: A02; `ClassicalSolutionT`, `maximalLifespanT`: T10; `ENNReal.ofReal`: Mathlib |
| 490 | `T11.squaredHTwoIntegralT` | `SpaceTimeField`: A02; `periodicSobolevENorm`: T10; `lintegral`, `Ioo`, natural power: Mathlib |
| 496 | `T11.timeShiftT` | reducible alias of `Section4.A04.timeShift`; `SpaceTimeField`: A02 |
| 504 | `T11.ExtendsBeyondT` | field types: A02; `ClassicalSolutionT`: T10; interval sets and logic: Mathlib |
| 531 | `T11.PeriodicLocalRegularity` | `ClassicalSolutionT`, `PeriodicSobolev`: T10; preceding T11 declarations; `Space`, `SpaceTime`, `spatialDivergence`, `temporalDerivative`, `spatialLaplacian`, `pressureGradient`: upstream problem statement; `ContDiffOn`: Mathlib |
| 571 | intentionally absent; `PeriodicLocalTheoryAPI` is restated in the probe | all fields elaborate over T10, the canonical T11 predicates, and canonical `PeriodicLocalRegularity` |
| 677 | intentionally absent; `PeriodicContinuationAPI` is restated in the probe | T10 solution/norm/lifespan vocabulary and the canonical T11 restart/continuation predicates |
| 772 | `T11.velocityMeanT` | `SpaceTimeField`: A02; `meanT`: T10 |
| 777 | `T11.forceMeanT` | `SpaceTimeField`: A02; `meanT`: T10 |
| 783 | `T11.galileanMeanT` | `SpatialField`, `SpaceTimeField`: A02; `meanT`: T10; Bochner interval integral: Mathlib |
| 788 | `T11.galileanShiftT` | field types: A02; `galileanMeanT`: preceding T11 declaration; Bochner interval integral: Mathlib |
| 793 | `T11.galileanVelocityT` | field types: A02; preceding T11 Galilean declarations; vector operations: Mathlib |
| 800 | `T11.galileanForceT` | field types: A02; `galileanShiftT`, `forceMeanT`: preceding T11 declarations |
| 805 | `T11.galileanPressureT` | `SpatialField`, `SpaceTimeField`, `SpaceTimeScalar`: A02; `galileanShiftT`: preceding T11 declaration |
| 811 | intentionally absent; `PeriodicMeanReductionAPI` is restated in the probe | T10 mean/input/solution vocabulary, canonical T11 Galilean maps and canonical `PeriodicLocalRegularity`; `HasDerivAt`: Mathlib |
| 900 | `T11.unitViscosityInitialT` | `SpatialField`: A02; inverse and scalar action: Mathlib |
| 905 | `T11.unitViscosityVelocityT` | `SpaceTimeField`: A02; inverse, division and scalar action: Mathlib |
| 910 | `T11.unitViscosityPressureT` | `SpaceTimeScalar`: A02; inverse, multiplication and powers: Mathlib |
| 915 | `T11.unitViscosityForceT` | `SpaceTimeField`: A02; inverse, scalar action and powers: Mathlib |
| 920 | `T11.restoreViscosityVelocityT` | `SpaceTimeField`: A02; scalar action and multiplication: Mathlib |
| 924 | `T11.restoreViscosityPressureT` | `SpaceTimeScalar`: A02; multiplication and powers: Mathlib |
| 928 | `T11.restoreViscosityForceT` | `SpaceTimeField`: A02; scalar action, multiplication and powers: Mathlib |
| 933 | intentionally absent; `PeriodicViscosityRescalingAPI` is restated in the probe | T10 input/solution vocabulary, canonical T11 scaling maps and canonical `PeriodicLocalRegularity` |

## Reuse decisions and bridge evidence

| T11 declaration | decision | evidence |
|---|---|---|
| `convectionDivergenceT` | Reused as a reducible alias. `Section4.A01.convectionDivergence` is a `def` on the same `VelocityField`/`SpaceTimeField` vocabulary and has the same body. | `Bindings/LocalTheoryV2.lean:32-34` gives the contract-to-A01 `rfl` bridge. The probe checks T11-to-A01 and T11-to-contract by `rfl`. |
| `timeShiftT` | Reused as a reducible alias. `Section4.A04.timeShift` is a `def` on the same field vocabulary and has the same body. | `Bindings/ContinuationV2.lean:69-71` gives the contract-to-A04 `rfl` bridge. The probe checks both equalities by `rfl`. |
| `SolvesBelowT` | Defined in T11. | A04's local source quantifies over `A02.ClassicalSolutionR`; T11 must quantify over the distinct `T10.ClassicalSolutionT`. The structure exception rules out a structure-level `rfl` reuse. |
| `IsMaximalPeriodicSolution` | Defined in T11. | A02's source uses `ClassicalSolutionR` and `maximalLifespanR`; T11 uses the distinct periodic solution structure and `maximalLifespanT`. |
| `squaredHTwoIntegralT` | Defined in T11. | A04's source integrates the whole-space `D01.sobolevENorm`; T11 integrates `T10.periodicSobolevENorm`. The predicate shape is the same but the norm vocabulary is not. |

`scalarSpatialLaplacianT`, `ExtendsBeyondT`, the Galilean maps, and the
viscosity maps have no token-identical registered Section 4 `def` on the same
vocabulary, so their specification bodies are retained locally.

## Probe scope

`research/T11/probes/api_on_canonical.lean` imports the T11 and T10 modules and
the V1/V2 contracts.  It restates the five reconciled structures and contains
all explicit `rfl` checks required for the two reused T11 declarations.  The
contracts are probe-only dependencies; no file below `formalization/` imports
`Contracts.*` or `Bindings.*`.

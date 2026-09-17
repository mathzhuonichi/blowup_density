# T12 canonical-module map

`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean` is the
definitions-only canonical module for the declarations introduced by
`research/T12/Spec.lean` before `MeanZeroSobolevCalculusAPI`.  It imports the
canonical T10 data layer instead of copying the temporary
`BlowupDensity.T10.Draft` block.  Every T12-native definition has the spec's
name, binder order, and body.  The three already-canonical derivative
declarations are the brief's mandated exception: they are exposed as reducible
aliases of the existing Section 4 sources rather than duplicated.

The module declares no `instance` or `local instance`.  In particular it does
not repeat the Haar measure/probability instances already provided in the
imported torus source.

## Spec declaration map

| `Spec.lean` line | canonical module declaration | source of each imported name |
|---:|---|---|
| 195 | `T12.IsPeriodicScalarDatum` | `Space`: `NavierStokes.ProblemStatement`; `IsPeriodicSpatial`, `torusLift`, `periodicTorusMeasure`, `PeriodicFrequency`, `periodicFrequencyWeight`, `periodicFourierCoeff`, `PeriodicScalarData`: `Section3.T10.PeriodicData`; `Integrable`, scalar/complex coercions and scalar action: Mathlib |
| 204 | `T12.periodicScalarSobolevENorm` | `PeriodicScalarData`: T10; `IsPeriodicScalarDatum`: preceding T12 declaration; extended norm, subtype and infimum: Mathlib |
| 210 | `T12.MemPeriodicHmScalar` | periodic objects and lift: T10; `periodicScalarSobolevENorm`: preceding T12 declaration; `MemLp`, `⊤`: Mathlib |
| 217 | `T12.MemPeriodicHmVector` | `SpatialField`: `Section4.A02.SolutionClass`; periodic objects and `periodicSobolevENorm`: T10; `MemLp`, `⊤`: Mathlib |
| 224 | `T12.MemPeriodicHomogeneous` | `SpatialField`: A02; `IsPeriodicSpatial`, lift/measure, `IsMeanZeroT`, `periodicHomogeneousENorm`: T10; `MemLp`, `⊤`: Mathlib |
| 230 | `T12.SmoothPeriodicT` | `SpatialField`: A02; `IsPeriodicSpatial`: T10; `ContDiff` and `∞`: Mathlib |
| 235 | `T12.periodicLpENorm` | `Space`: upstream problem statement; `torusLift`, `periodicTorusMeasure`: T10; `NormedAddCommGroup`, `eLpNorm`, `ℝ≥0∞`: Mathlib |
| 244 | `T12.lift` | reducible alias of `Section4.C01.lift`; `SpatialField`, `SpaceTimeField`: A02 |
| 249 | `T12.gradientTensor` | reducible alias of `Section4.A05.gradTensor`; `Space`: upstream problem statement; `SpatialField`: A02; `WithLp`: Mathlib |
| 255 | `T12.laplacian` | reducible alias of `Section4.A05.lap`; `SpatialField`: A02 |
| 274 | `T12.IsPeriodicLambda` | `SpatialField`: A02; `SmoothPeriodicT`: preceding T12 declaration; frequency/coefficient/angular-weight vocabulary: T10; `Real.sqrt` and complex/real coercions: Mathlib |
| 287 | intentionally absent from the canonical module; `MeanZeroSobolevCalculusAPI` is restated in `probes/api_on_canonical.lean` | its seven constants, seven positivity fields, and nine theorem clauses elaborate over the canonical T10 and T12 declarations |

The anonymous completed-density checks at `Spec.lean:175-187` are not named
T12 declarations and are not copied into the module.  They concern registered
Section 4 contract abbreviations, while this canonical `formalization/` module
must not import a contract.

## Imported T10 vocabulary

The T12 bodies use these declarations directly from
`NSFormalization.Section3.T10.PeriodicData`:

- `PeriodicFrequency`, `PeriodicScalarData`, `periodicTorusMeasure`,
  `torusLift`, `periodicFourierCoeff`, and `periodicFrequencyWeight`;
- `IsPeriodicSpatial`, `periodicSobolevENorm`, `IsMeanZeroT`,
  `periodicAngularFrequencySq`, and `periodicHomogeneousENorm`.

No T10 declaration is restated in the T12 namespace, so there is no second
source of periodic vocabulary and no duplicated measure instance.

## Reused derivative declarations and bridge evidence

| T12 declaration | local canonical source | registered identification |
|---|---|---|
| `lift` | `NSFormalization.Section4.C01.lift` in `Section4/C01/Trilinear.lean`; its declaration is token-identical to the registered time-independent lift | the probe checks both `T12.lift v = C01.lift v` and `T12.lift v = Contracts.V1.lift v` by `rfl` |
| `gradientTensor` | `NSFormalization.Section4.A05.gradTensor` in `Section4/A05/GradientL6.lean` | `verification/Bindings/GradientL6.lean:27-28` proves `Contracts.V1.gradientTensor v = A05.gradTensor v` by `rfl`; the probe checks both orientations relevant to T12 by `rfl` |
| `laplacian` | `NSFormalization.Section4.A05.lap` in `Section4/A05/HessianLaplacian.lean`, imported through `A05.GradientL6` | `verification/Bindings/GradientL6.lean:32-33` proves `Contracts.V1.laplacian v = A05.lap v` by `rfl`; the probe checks both orientations relevant to T12 by `rfl` |

The contract binding has no separately named `lift_eq` theorem, because its
registered gradient and Laplacian bridge computations already unfold that
lift.  `Section4.C01.lift` is the sole exact local declaration with the T12
type and body, and the probe supplies the explicit missing `rfl` check.

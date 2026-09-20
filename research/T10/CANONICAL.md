# T10 canonical-module map

`formalization/NSFormalization/Section3/T10/PeriodicData.lean` is the
definitions-only canonical module for `research/T10/Spec.lean`.  Except for the
five declarations already present in `Paper1/TorusCube.lean`, declaration
names, binder order, field order, and bodies are copied from the amended spec.
Docstrings are implementation-facing and need not be duplicated by a future
contract.

## Spec declaration map

| `Spec.lean` line | canonical module declaration | imported names and their source |
|---:|---|---|
| 48 | `T10.PeriodicFrequency` | reducible alias of `Paper1.PeriodicFrequency` |
| 51 | `T10.PeriodicTorus` | reducible alias of `Paper1.PeriodicTorus` |
| 58 | `T10.periodicTorusMeasure` | reducible alias of `Paper1.periodicTorusMeasure` |
| 63 | `T10.IsPeriodicSpatial` | `Space`, `coordinateVector`: `NavierStokes.ProblemStatement` |
| 68 | `T10.IsPeriodicOn` | `SpaceTime`, `Space`, `coordinateVector`: `NavierStokes.ProblemStatement` |
| 76 | `T10.torusLift` | reducible wrapper around `Paper1.torusLift`; explicit polymorphic binders are needed for Lean to infer `E` |
| 84 | `T10.periodicFourierCoeff` | reducible alias of `Paper1.periodicFourierCoeff` |
| 89 | `T10.periodicFrequencyWeight` | `Real.pi`: Mathlib; `PeriodicFrequency`: preceding alias |
| 93 | `T10.PeriodicScalarData` | `lp`: Mathlib; `PeriodicFrequency`: preceding alias |
| 97 | `T10.PeriodicVectorData` | `WithLp`: Mathlib; `PeriodicScalarData`: preceding declaration |
| 101 | `T10.realPeriodicSubmodule` | `Submodule`, `star`: Mathlib; `PeriodicVectorData`: preceding declaration |
| 119 | `T10.PeriodicSobolev` | `realPeriodicSubmodule`: preceding declaration |
| 123 | `T10.periodicSobolevDataNorm` | norm instances supplied by Mathlib for the preceding carrier |
| 134 | `T10.IsPeriodicDatum` | `SpatialField`: `Section4.A02.SolutionClass` via the required `Section4.A02.Restrict` import; `Integrable`: Mathlib; the torus objects are the aliases above |
| 143 | `T10.periodicSobolevENorm` | `ENNReal` and extended norm: Mathlib; `IsPeriodicDatum`: preceding declaration |
| 150 | `T10.meanT` | `SpatialField`: A02; `Space`: upstream problem statement; reused torus lift/measure |
| 154 | `T10.constantPartT` | `SpatialField`: A02; `meanT`: preceding declaration |
| 158 | `T10.meanZeroPartT` | `SpatialField`: A02; `meanT`: preceding declaration |
| 162 | `T10.meanDecompositionT` | `SpatialField`: A02; preceding mean declarations |
| 168 | `T10.meanZeroPeriodicSobolev` | `Submodule`: Mathlib; `PeriodicSobolev`: preceding declaration |
| 181 | `T10.IsMeanZeroT` | `SpatialField`: A02; `meanT`: preceding declaration |
| 185 | `T10.periodicAngularFrequencySq` | `Real.pi`: Mathlib; aliased frequency lattice |
| 191 | `T10.homogeneousDatumWeight` | `Real.rpow`: Mathlib; preceding angular weight |
| 201 | `T10.IsPeriodicHomogeneousDatum` | `SpatialField`: A02; `Integrable`: Mathlib; preceding periodic/mean/Fourier declarations |
| 211 | `T10.periodicHomogeneousENorm` | `ENNReal`: Mathlib; preceding homogeneous datum predicate |
| 216 | `T10.periodicDerivativeSymbol` | `Complex.I`: Mathlib; aliased frequency lattice |
| 222 | `T10.IsSolenoidalPeriodicDatum` | preceding coefficient carrier and derivative symbol |
| 231 | `T10.periodicLeray` | preceding coefficient carrier; finite sums and complex coercions from Mathlib |
| 242 | `T10.IsPeriodicLerayDatum` | `periodicLeray`: preceding declaration |
| 248 | `T10.IsPeriodicReweight` | preceding carrier and Bessel weight |
| 257 | `T10.IsPeriodicSobolevPath` | `SpaceTimeField`: A02; preceding datum predicate |
| 264 | `T10.forceSobolevENormT` | `forceTimeMeasure`: A02; `AEStronglyMeasurable`, `eLpNorm`: Mathlib |
| 272 | `T10.initialClassT` | `SpatialField`, `IsSolenoidal`: A02; `ContDiff`: Mathlib |
| 278 | `T10.MemForceT` | `SpaceTimeField`: A02; `tsupport`, compactness/product sets: Mathlib |
| 284 | `T10.forceClassT` | `SpaceTimeField`: A02; preceding force predicate |
| 290 | `T10.pressureMeanT` | `SpaceTimeScalar`: A02; reused torus lift/measure |
| 295 | `T10.PressureGaugeT` | `SpaceTimeScalar`: A02; preceding pressure mean |
| 300 | `T10.normalizePressureT` | `SpaceTimeScalar`: A02; preceding pressure mean |
| 311 | `T10.ClassicalSolutionT` | field abbreviations: A02; `spatialDivergence`, `pressureGradient`: `NavierStokes.ProblemStatement`; residual: `NavierStokes.R3.ProblemStatement`; remaining types/predicates are preceding T10 declarations or Mathlib |
| 364 | `T10.maximalLifespanT` | `ENNReal.ofReal`: Mathlib; preceding solution structure |
| 369 | `T10.RegularThroughT` | preceding solution structure |
| 376 | `T10.breakdownSetInT` | `SpaceTimeField`, `SpatialField`: A02; preceding lifespan |
| 382 | `T10.breakdownSetT` | preceding force class and parametric breakdown set |
| 388 | `T10.RelativelyDenseT` | `SpaceTimeField`: A02; preceding force norm |
| 395 | `T10.energyEssSupT` | `SpaceTimeField`: A02; `essSup`, `eLpNorm`, restricted volume: Mathlib; reused torus lift/measure |
| 402 | `T10.energyGradientT` | `spatialGradient`: `Section4.I02.Energy`; other vocabulary as in `energyEssSupT` |
| 410 | `T10.energyENormT` | preceding two physical energy terms |
| 415 | `T10.coefficientEnergyEssSupT` | `SpaceTimeField`: A02; preceding periodic Sobolev norm |
| 422 | `T10.coefficientEnergyGradientT` | preceding homogeneous norm and mean-zero part |
| 429 | `T10.coefficientEnergyENormT` | preceding two coefficient energy terms |
| 438 | intentionally absent from the module; `TorusDataAPI` is restated in `probes/api_on_canonical.lean` | all fields elaborate over the canonical declarations above; amended `parseval_forward` includes its `MemLp` premise |

`Spec.lean:33-42` contains two anonymous `example` checks, not named data-layer
declarations.  They concern the Section 4 completed-density abbreviations and
are therefore not copied into this T10 module.  The API probe imports
`Contracts.V1.Data` only for contract-side vocabulary, with no dependency in
the canonical `formalization/` module.

## Imported vocabulary and bridge evidence

| name used by T10 | canonical local/upstream source | binding evidence |
|---|---|---|
| `Space`, `SpaceTime`, `coordinateVector`, `spatialDivergence`, `pressureGradient` | `NavierStokes.ProblemStatement` | `verification/Bindings/Packet.lean`: `space_eq`, `coordinateVector_eq`, `spatialDivergence_eq`, `pressureGradient_eq` |
| `NavierStokesR3.ProblemStatement.navierStokesResidual` | `NavierStokes.R3.ProblemStatement` | `Bindings/Packet.lean`: `navierStokesResidual_eq` |
| `SpatialField`, `SpaceTimeField`, `SpaceTimeScalar`, `forceTimeMeasure`, `IsSolenoidal` | `NSFormalization.Section4.A02.SolutionClass`, imported through `Section4.A02.Restrict` | `Bindings/DatumLemmas.lean`: `datumLemmas_forceTimeMeasure_eq`; `Bindings/Uniqueness.lean` and other solution bindings document the token-identical A02 vocabulary and fieldwise solution conversion |
| `ClassicalSolutionR` (allowed source, not used by a T10 body) | the sole A02-local structure in `Section4.A02.SolutionClass`, imported by `Section4.A02.Restrict` | `Bindings/Uniqueness.lean`: `uniqueness_toA02` and its fieldwise `rfl` checks; no structure-level `rfl` bridge is possible |
| `IsSobolevPath` (mentioned by the spec's anonymous check, not used by a T10 body) | `Section4.A02.SolutionClass` | `Bindings/DatumLemmas.lean`: `datumLemmas_isSobolevPath_eq` for the definitionally equal D01 copy |
| `spatialGradient` | `NSFormalization.Section4.I02.Energy` | `Bindings/Correction.lean`: `spatialGradient_eq := rfl` |
| Mathlib torus/Fourier primitives | `Mathlib.Analysis.Fourier.AddCircleMulti`, transitively imported by `Paper1.TorusCube` | `Paper1.TorusCube` fixes their use in the local unit-period convention |

The brief referred to `verification/Bindings/Data.lean`, but that file is not
present in this checkout.  The bridge evidence above is the actual distributed
replacement in the repository.  The contract allowlist in
`experiments/check_contracts.py` independently confirms
`NavierStokes.R3.ProblemStatement` and the six local `Source`/`Paper3`
definition-level modules as canonical contract inputs.

## Reused rather than copied

The following canonical `Paper1.TorusCube` declarations were imported and
reused:

- `PeriodicFrequency`
- `PeriodicTorus`
- `periodicTorusMeasure`
- `torusLift`
- `periodicFourierCoeff`

All five identifications are checked by `rfl` in
`research/T10/probes/api_on_canonical.lean`.  The polymorphic `torusLift` alias
spells out its binders because a bare alias leaves `E` unconstrained; its body is
still exactly the imported function and the function equality check is `rfl`.

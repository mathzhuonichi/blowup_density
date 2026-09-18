# T13 canonical-module map

`formalization/NSFormalization/Section3/T13/Localization.lean` is the
definitions-only canonical module for the declarations introduced by
`research/T13/Spec.lean` before `LocalizationAPI`.  Every T13-native
definition has the spec's name, binder order, and body.  The temporary T10
copy in the research spec is not repeated: its vocabulary is imported from
`NSFormalization.Section3.T10.PeriodicData`.  The module declares no
`instance` or `local instance`.

## Spec declaration map

| `Spec.lean` line | canonical module declaration | source of each imported name |
|---:|---|---|
| 171 | `T13.fundamentalCube` | `Space`: `NavierStokes.ProblemStatement`; `Set`, finite coordinates, order, and set-builder notation: Mathlib |
| 176 | `T13.SupportedInBall` | `Space`: upstream problem statement; `SpatialField`: `Section4.A02.SolutionClass`, imported transitively through T10; `tsupport`, `Metric.ball`, and `⊆`: Mathlib |
| 180 | `T13.latticeVector` | `PeriodicFrequency`: `Section3.T10.PeriodicData`; `Space`: upstream problem statement; `EuclideanSpace.equiv` and integer-to-real coercion: Mathlib |
| 185 | `T13.periodize` | `SpatialField`: Section4 A02; `PeriodicFrequency`: T10; `latticeVector`: preceding T13 declaration; subtraction and `∑'`: Mathlib |
| 192 | `T13.fractionalRadialKernel` | `Space`: upstream problem statement; `ENNReal.ofReal`, norm, real exponentiation, and arithmetic: Mathlib |
| 197 | `T13.cFrac` | `Space`: upstream problem statement; `fractionalRadialKernel`: preceding T13 declaration; `Complex.exp`, `Complex.I`, norm, `ENNReal.ofReal`, and `lintegral`: Mathlib |
| 204 | `T13.periodicKernel` | `PeriodicFrequency`: T10; `latticeVector`, `fractionalRadialKernel`: preceding T13 declarations; addition and `∑'`: Mathlib |
| 209 | `T13.latticeTail` | `PeriodicFrequency`: T10; `latticeVector`, `fractionalRadialKernel`: preceding T13 declarations; subtype, zero, addition, and `∑'`: Mathlib |
| 215 | `T13.IReal` | `Space`: upstream problem statement; `SpatialField`: Section4 A02; `fractionalRadialKernel`: preceding T13 declaration; vector operations, norm, `ENNReal.ofReal`, and iterated `lintegral`: Mathlib |
| 221 | `T13.ITorus` | `SpatialField`: Section4 A02; `fundamentalCube`, `periodicKernel`: preceding T13 declarations; restricted `lintegral`, vector operations, norm, and `ENNReal.ofReal`: Mathlib |
| 229 | `T13.gradientENorm` | `Space`, `coordinateVector`: upstream problem statement; `SpatialField`: Section4 A02; `Measure`, `fderiv`, finite sums, `lintegral`, `ENNReal.ofReal`, norm, and real exponentiation: Mathlib |
| 238 | intentionally absent from the canonical module; `LocalizationAPI` is restated in `probes/api_on_canonical.lean` | its six fields elaborate over the canonical T10/T13 declarations, Section4 D01's `dotHomogeneousENorm`, Section4 A02's `SpatialField`, and Mathlib |

## Imported T10 vocabulary

The bodies and API probe use these declarations directly from
`NSFormalization.Section3.T10.PeriodicData`:

- `PeriodicFrequency` in `latticeVector`, `periodize`, `periodicKernel`, and
  `latticeTail`;
- `IsPeriodicSpatial`, `periodicSobolevENorm`,
  `periodicHomogeneousENorm`, and `meanZeroPartT` in the API probe.

No T10 declaration is restated in the T13 namespace.  In particular, this
module introduces no second torus measure or probability instance.

## Reused Section 4 declarations and bridge evidence

| name used by T13 | local canonical source | registered identification and probe check |
|---|---|---|
| `SpatialField` | `NSFormalization.Section4.A02.SolutionClass`, available through the required T10 import | `verification/Bindings/DatumLemmas.lean` documents the token-identical A02/Data vocabulary; the T13 probe checks the type equality against `Contracts.V1.Data.SpatialField` by `rfl` |
| `dotHomogeneousENorm` | `NSFormalization.Section4.D01.HomogeneousNorm` | `verification/Bindings/HomogeneousNorm.lean:12` proves the contract-to-D01 function equality by `rfl`; the T13 probe checks the pointwise equality in the orientation used by its API by `rfl` |

The canonical T13 module imports `Section4.D01.HomogeneousNorm` rather than
copying the contract-side whole-space norm.  The underlying D01
`IsHomogeneousDatum`, `homogeneousENorm`, `IsHomogeneousSliceDatum`, and
`homogeneousFourierENorm` restatements remain in
`Section4.D01.HomogeneousWitness`; their contract identifications are the
`rfl` bridges in `verification/Bindings/DatumLemmas.lean:130-158`.  T13 does
not introduce new copies of any of them.
